import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.MarkingTwoCaps
import OAI.Combinatorics.SharpRamsey.Reciprocal.ReciprocalBands

namespace OAI

section
namespace SharpLogRamsey.Marking
open Finset
open scoped BigOperators Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K]

theorem twoDomain_low_or_high {n : ℕ} (hdim : Module.finrank K V=n+3)
    (W : State (K:=K) (V:=V)) (W' : State (K:=K) (V:=Module.Dual K V))
    (m : RankMask (K:=K) (V:=V)) (m' : RankMask (K:=K) (V:=Module.Dual K V))
    (h : (twoDomain W W' m m').Nonempty) :
    (((twoDomain W W' m m').image Prod.fst).card:ℝ)*
      ((twoDomain W W' m m').image Prod.snd).card ≤ 1024*(Nat.card K:ℝ)^(n+3) ∨
    (m.2=.popular ∧ m'.2=.popular ∧ 1 ≤ m.1.val ∧ m.1.val≤n+2 ∧
      1 ≤ m'.1.val ∧ m'.1.val≤n+2 ∧ n+3 < m.1.val+m'.1.val) := by
  have hdim' : Module.finrank K V=(n+2)+1 := by omega
  obtain hp|hp|⟨hp,hp',hr,hr',hs,hs'⟩ := twoDomain_cases hdim' W W' m m' h
  · left
    exact (twoPoor_product hdim W W' m m' (Or.inl hp)).trans (mul_le_mul_of_nonneg_right (by norm_num : (16:ℝ)≤1024) (by positivity))
  · left
    exact (twoPoor_product hdim W W' m m' (Or.inr hp)).trans (mul_le_mul_of_nonneg_right (by norm_num : (16:ℝ)≤1024) (by positivity))
  by_cases hsum : m.1.val+m'.1.val≤n+3
  · left
    obtain ⟨ha,hb,-,-⟩ := twoPopular_caps hdim' W W' m m' hp hp'
    have hq : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le
    calc
      _ ≤ (32*(Nat.card K:ℝ)^m.1.val)*(32*(Nat.card K:ℝ)^m'.1.val) :=
        mul_le_mul ha hb (by positivity) (by positivity)
      _ = 1024*(Nat.card K:ℝ)^(m.1.val+m'.1.val) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq hsum) (by norm_num)
  · exact Or.inr ⟨hp,hp',hr,hr',hs,hs',by omega⟩

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma ambient_point_bound {d : ℕ} (hdim : Module.finrank K V=d+1)
    (S : Finset (Projectivization K V)) : (S.card:ℝ)≤2*(Nat.card K:ℝ)^d := by
  have ht : Module.finrank K (⊤ : Submodule K V)=d+1 := by
    simpa using hdim
  have hb := card_subspace_points_le (⊤ : Submodule K V) ht
  have hcard : (S.card:ℝ)≤(Fintype.card (Projectivization K V):ℝ) := by
    exact_mod_cast card_le_univ S
  exact hcard.trans (by simpa using hb)

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] [Finite K] in
lemma exp_nat_log {q : ℝ} (hq : 0<q) (d : ℕ) : Real.exp ((d:ℝ)*Real.log q)=q^d := by
  rw [Real.exp_nat_mul,Real.exp_log hq]

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in

theorem twoDomain_reciprocal_caps {d : ℕ} (hd : 1≤d)
    (hdim : Module.finrank K V=d+1)
    (D : Finset (ProjectivePair (K:=K) (V:=V))) (hD : D.Nonempty)
    (hp : ((D.image Prod.fst).card:ℝ)*(D.image Prod.snd).card≤
      1024*(Nat.card K:ℝ)^(d+1)) :
    let σ := Real.log (Nat.card K:ℝ)
    let u := ReciprocalBands.clamp d σ (Real.log (D.image Prod.snd).card)
    σ≤u ∧ u≤(d:ℝ)*σ ∧
      ((D.image Prod.fst).card:ℝ)≤1024*Real.exp (((d:ℝ)+1)*σ-u) ∧
      ((D.image Prod.snd).card:ℝ)≤1024*Real.exp u := by
  have hq : (0:ℝ)<Nat.card K := by exact_mod_cast Nat.card_pos (α:=K)
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (Finite.one_lt_card : 1<Nat.card K).le
  have hdim' : Module.finrank K (Module.Dual K V)=d+1 := by
    rwa [Subspace.dual_finrank_eq]
  have ha := ambient_point_bound hdim (D.image Prod.fst)
  have hb := ambient_point_bound hdim' (D.image Prod.snd)
  have hbp : (0:ℝ)<(D.image Prod.snd).card := by
    exact_mod_cast card_pos.mpr (hD.image Prod.snd)
  apply ReciprocalBands.clamped_caps hd (Real.log_nonneg hq1) hbp (by norm_num)
  · rw [exp_nat_log hq]
    exact ha.trans (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤1024) (by positivity))
  · rw [exp_nat_log hq]
    exact hb.trans (mul_le_mul_of_nonneg_right (by norm_num : (2:ℝ)≤1024) (by positivity))
  · convert hp using 1
    rw [←Nat.cast_add_one,exp_nat_log hq]

end
end SharpLogRamsey.Marking

end

end OAI
