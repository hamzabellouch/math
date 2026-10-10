import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Evolve

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

omit [DecidableEq J] in
theorem ladder_minimum_mass
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (D K : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ Fintype.card V)
    (w : BagEdge bags → ℝ)
    (hw : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K) (T q : ℕ)
    (z : Slot T q → PM (BagEdge.Incident (bags := bags))) :
    Real.log ((ladderLaw w T q z)⁻¹) ≤
      (10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1):ℕ) := by
  have hl := ladderLaw_power_lower hbags hG D K hD hN w hw T q z
  have hp : 0 < ladderLaw w T q z := by
    apply Finset.prod_pos; intro x _; exact slotLaw_pos w x (z x)
  have hu := inv_anti₀ (by positivity : (0:ℝ) < ((2:ℝ)^(10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1)))⁻¹) hl
  rw [inv_inv] at hu
  have hh := Real.log_le_log (inv_pos.mpr hp) hu
  rw [Real.log_pow] at hh
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hΛ : (0:ℝ) ≤ (10*Fintype.card V*q*(T+1)*(K+Nat.clog 2 (Fintype.card V*D+2)+1):ℕ) := Nat.cast_nonneg _
  exact hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hlog hΛ)

end

def ladderL (N D : ℕ) : ℕ := (10^4*N*D)^100

def ladderQ (N D : ℕ) : ℕ := 32*ladderL N D

def ladderM (N D T : ℕ) : ℕ := T*(ladderQ N D)^2+ladderQ N D

def ladderLambda (N D K T : ℕ) : ℕ :=
  10*N*ladderQ N D*(T+1)*(K+Nat.clog 2 (N*D+2)+1)

noncomputable def ladderSteps (N D K T : ℕ) (ξ : ℝ) : ℕ :=
  20*ladderL N D*ladderM N D T*(ladderLambda N D K T+⌈Real.logb 2 ξ⁻¹⌉₊+1)

end MatchingFPRAS.Transport

namespace MatchingFPRAS.FiniteChain

lemma log_inv_le_ceil_logb {ξ : ℝ} (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    -Real.log ξ ≤ (⌈Real.logb 2 ξ⁻¹⌉₊:ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog21 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith
  have hxi : 1 ≤ ξ⁻¹ := (one_le_inv₀ hξ).mpr hξ1.le
  have hlogxi : 0 ≤ Real.log ξ⁻¹ := Real.log_nonneg hxi
  have hb : 0 ≤ Real.logb 2 ξ⁻¹ := div_nonneg hlogxi hlog2.le
  have he : Real.logb 2 ξ⁻¹*Real.log 2 = -Real.log ξ := by
    rw [Real.logb,div_mul_cancel₀ _ hlog2.ne',Real.log_inv]
  exact (by nlinarith : -Real.log ξ ≤ Real.logb 2 ξ⁻¹).trans (Nat.le_ceil _)

lemma mixing_at_steps {a u γ Λ ξ : ℝ} {n b : ℕ}
    (ha : 0 ≤ a) (hu : 0 < u) (hγ : γ ≤ 1) (hΛ : 0 ≤ Λ)
    (hξ : 0 < ξ) (hb : -Real.log ξ ≤ (b:ℝ))
    (hmass : Real.log u⁻¹ ≤ Λ)
    (hsteps : 2*(Λ+(b:ℝ)+1) ≤ γ*n)
    (hmix : a^2 ≤ (1-γ)^n*(u⁻¹-1)) : a/2 ≤ ξ := by
  have hmass' : u⁻¹ ≤ Real.exp Λ := (Real.log_le_iff_le_exp (inv_pos.mpr hu)).mp hmass
  have hp : 0 ≤ 1-γ := by linarith
  have he : (1-γ)^n ≤ Real.exp (-γ*(n:ℝ)) := by
    calc
      _ ≤ (Real.exp (-γ))^n := pow_le_pow_left₀ hp (Real.one_sub_le_exp_neg γ) n
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hsq : a^2 ≤ ξ^2 := by
    calc
      _ ≤ (1-γ)^n*(u⁻¹-1) := hmix
      _ ≤ (1-γ)^n*Real.exp Λ := mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hp _)
      _ ≤ Real.exp (-γ*(n:ℝ))*Real.exp Λ := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = Real.exp (-γ*(n:ℝ)+Λ) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (2*Real.log ξ) := Real.exp_le_exp.mpr (by linarith)
      _ = ξ^2 := by rw [show (2:ℝ)=(2:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log hξ]
  nlinarith

end MatchingFPRAS.FiniteChain

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J} {G : SimpleGraph J}

noncomputable local instance : Fintype (BagEdge bags) := Fintype.ofFinite _

noncomputable local instance : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _

theorem ideal_ladder_sampling
    (hbags : ∀ v, ∀ a ∈ bags v, ∀ b ∈ bags v, a = b ∨ G.Adj a b)
    (hG : G.IsAcyclic) (height : J → ℝ) (hheight : ∀ l, 0 < height l)
    (hstep : ∀ a b, G.Adj a b → height a ≤ 2*height b)
    (D K : ℕ) (hD : 1 ≤ D) (hN : 2 ≤ Fintype.card V) (w : BagEdge bags → ℝ)
    (hw : ∀ e, height e.color / D ≤ w e ∧ w e ≤ 3*height e.color)
    (hglobal : ∀ e, (D:ℝ)⁻¹ ≤ w e ∧ w e ≤ 3*4^K)
    (M₀ : PM (BagEdge.Incident (bags := bags))) (T : ℕ)
    (z : Slot T (ladderQ (Fintype.card V) D) → PM (BagEdge.Incident (bags := bags)))
    (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ < 1) :
    let ν := ladderLaw w T (ladderQ (Fintype.card V) D)
    let C := ladderFlow hbags hG w T (ladderQ (Fintype.card V) D)
    (∑ s, |MatchingFPRAS.FiniteChain.walk ν C z (ladderSteps (Fintype.card V) D K T ξ) s-ν s|)/2 ≤ ξ := by
  classical
  dsimp only
  let N := Fintype.card V
  let L := ladderL N D
  let q := ladderQ N D
  let M := ladderM N D T
  let Λ := ladderLambda N D K T
  let b := ⌈Real.logb 2 ξ⁻¹⌉₊
  let ν := ladderLaw w T q
  let C := ladderFlow hbags hG w T q
  let n := ladderSteps N D K T ξ
  let γ : ℝ := 3/(8*(M:ℝ))
  have hL0 : 0 < L := by
    have hn : 0 < N := by dsimp [N]; omega
    have hd : 0 < D := by omega
    dsimp [L,ladderL]; positivity
  have hq0 : 0 < q := by dsimp [q,ladderQ]; exact Nat.mul_pos (by decide) hL0
  have hM0 : 0 < M := by dsimp [M,ladderM]; omega
  have hMr : (0:ℝ) < M := by exact_mod_cast hM0
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast hL0
  have hΛr : (0:ℝ) ≤ Λ := Nat.cast_nonneg _
  have hγ : γ ≤ 1 := by
    dsimp [γ]
    apply (div_le_one (by positivity : (0:ℝ)<8*M)).mpr
    have hm : (1:ℝ) ≤ M := by exact_mod_cast hM0
    linarith
  have hsteps : 2*((Λ:ℝ)+(b:ℝ)+1) ≤ γ*(n:ℝ) := by
    have hb0 : (0:ℝ) ≤ b := Nat.cast_nonneg _
    have hfac : (0:ℝ) ≤ (Λ:ℝ)+(b:ℝ)+1 := by positivity
    calc
      _ ≤ ((15:ℝ)/2)*(L:ℝ)*((Λ:ℝ)+(b:ℝ)+1) :=
        mul_le_mul_of_nonneg_right (by linarith) hfac
      _ = _ := by
        dsimp [γ,n,ladderSteps,L,M,Λ,b]
        push_cast
        have hm0 : (ladderM N D T:ℝ) ≠ 0 := hMr.ne'
        field_simp [hm0]
        ring
  have hp : 0 < ν z := by
    apply Finset.prod_pos; intro i _; exact slotLaw_pos w i (z i)
  have hmass : Real.log ((ν z)⁻¹) ≤ (Λ:ℝ) :=
    ladder_minimum_mass hbags hG D K hD hN w hglobal T q z
  have hmix := concrete_ladder_mixing (hbags := hbags) (hG := hG)
    height hheight hstep D hD w hw hN M₀ T z n
  dsimp only at hmix
  have hmix' : (∑ s, |MatchingFPRAS.FiniteChain.walk ν C z n s-ν s|)^2 ≤
      (1-γ)^n*((ν z)⁻¹-1) := by
    simp only [γ,ν,C,q,M,ladderM,ladderQ,ladderL,N,Nat.cast_mul,Nat.cast_ofNat] at hmix ⊢
    convert hmix using 1
    congr 4
  exact MatchingFPRAS.FiniteChain.mixing_at_steps
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) hp hγ hΛr hξ
    (MatchingFPRAS.FiniteChain.log_inv_le_ceil_logb hξ hξ1) hmass hsteps hmix'

end MatchingFPRAS.Transport

end OAI
