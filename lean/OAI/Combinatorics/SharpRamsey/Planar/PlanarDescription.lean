import Mathlib
import OAI.Combinatorics.SharpRamsey.Planar.PlanarSourceCover
import OAI.Combinatorics.SharpRamsey.Learning.EnumeratedCover

namespace OAI

section
namespace SharpLogRamsey.PlanarLearning
open Finset Real Filter SourceScales
open scoped Classical BigOperators Topology NNReal
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPlanarDescription_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPlanarDescription_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPlanarDescription_3 : Fintype (Projectivization K V) := by
  letI : Finite V := Module.finite_of_finite K
  exact Fintype.ofFinite _

lemma plane_card (hdim : Module.finrank K V=3) :
    (Fintype.card (Projectivization K V):ℝ)=1+Nat.card K+(Nat.card K:ℝ)^2 := by
  rw [←Nat.card_eq_fintype_card,Projectivization.card_of_finrank K V hdim]
  norm_num [sum_range_succ]

lemma plane_log_card (hdim : Module.finrank K V=3) :
    log ((Fintype.card (Projectivization K V):ℝ)+1)≤2*Nat.card K ∧
    log ((Fintype.card (Projectivization K V):ℝ)*log 2+1)≤2*Nat.card K := by
  let q : ℝ := Nat.card K
  have hq : 1≤q := by
    dsimp only [q]
    exact_mod_cast (show 1≤Nat.card K from Nat.card_pos (α:=K))
  have hQ : (Fintype.card (Projectivization K V):ℝ)+1≤(q+1)^2 := by
    rw [plane_card hdim]; dsimp [q] at *; nlinarith
  have hlog : log ((q+1)^2)≤2*q := by
    rw [log_pow]
    have hh := log_le_sub_one_of_pos (show 0<q+1 by linarith)
    norm_num only [Nat.cast_ofNat]
    linarith
  have hfirst := (log_le_log (by positivity) hQ).trans hlog
  refine ⟨hfirst,?_⟩
  apply le_trans _ hfirst
  apply log_le_log (by have := log_nonneg (by norm_num : (1:ℝ)≤2); positivity)
  have hh : log 2≤(1:ℝ) := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
  nlinarith [show (0:ℝ)≤Fintype.card (Projectivization K V) by positivity]

lemma description_cost {q P d τ H Q : ℝ} {M : ℕ}
    (hq : 1≤q) (hP : 1≤P) (hd : 0≤d) (hτ : τ≤1)
    (hM : (M:ℝ)≤2*q*P+1) (hH : log (H+1)≤2*q) (hQ : log (Q+1)≤2*q) :
    2*((M:ℝ)*d+2*P*τ+log 4+log (H+1))+log 3+log (Q+1)≤
      200*q*P*(d+P) := by
  have hqP : 1≤q*P := one_le_mul_of_one_le_of_one_le hq hP
  have hM' : (M:ℝ)≤3*q*P := by nlinarith
  have hMd := mul_le_mul_of_nonneg_right hM' hd
  have hPt := mul_le_mul_of_nonneg_left hτ (show 0≤2*P by linarith)
  have hPq : P≤q*P := le_mul_of_one_le_left (by linarith) hq
  have hqP' : q≤q*P := le_mul_of_one_le_right (by linarith) hP
  have hlog4 : log 4≤(3:ℝ) := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4); linarith
  have hlog3 : log 3≤(2:ℝ) := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<3); linarith
  have hbig : q*P≤q*P*P := le_mul_of_one_le_right (by positivity) hP
  have hpos : 0≤q*P*d := by positivity
  nlinarith

theorem full_source_cover {η : ℝ} (hη : 0<η) (C : ℝ) (hC : 1≤C) :
    ∀ᶠ σ : ℝ in atTop,∀ D R,Admissible σ η D R →
    exp σ=(Nat.card K:ℝ) → Module.finrank K V=3 →
    ∀ (U : Finset (Projectivization K V)) (n : ℕ) (b τ : ℝ),
    0<n → n≤U.card → 0≤b → b≤C*scaleKstar σ η D →
    0<τ → τ≤C*σ^(-100*beta η) →
    let P := scaleP σ η D R
    ∃ caps : Finset (Finset (Projectivization K V)),
      (∀ W∈caps,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
      (∀ S,Input U n b τ S → ∃ W∈caps,(n:ℝ)/2≤(S∩W).card) ∧
      log ((caps.card:ℝ)+1)≤200*(Nat.card K:ℝ)*P*(log ((U.card:ℝ)/n)+P) := by
  have ht : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [source_cover (K:=K) (V:=V) hη C hC,
    eventually_uniform_L hη (eventually_ge_atTop (1:ℝ)),
    eventually_uniform_R hη 1,ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))]
    with σ hcover hL hR ht
  intro D R had hex hdim U n b τ hn hnu hb hbu hτ hτu
  let P := scaleP σ η D R
  let q : ℝ := Nat.card K
  let d := log ((U.card:ℝ)/n)
  have hP : 1≤P := one_le_mul_of_one_le_of_one_le (hL D R had) (hR D R had)
  have hq : 1≤q := by
    dsimp only [q]
    exact_mod_cast (show 1≤Nat.card K from Nat.card_pos (α:=K))
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hnu' : (n:ℝ)≤U.card := by exact_mod_cast hnu
  have hd : 0≤d := log_nonneg ((le_div_iff₀ hn').mpr (by linarith))
  have hqP : 1≤q*P := one_le_mul_of_one_le_of_one_le hq hP
  by_cases hsmall : (n:ℝ)≤100*q*P
  · obtain ⟨hsize,hcapture,hlen⟩ := DescriptionEnumeration.public_cover U n hn hnu
    refine ⟨U.powersetCard n,?_,?_,?_⟩
    · intro W hW
      obtain ⟨hWU,hnW⟩ := hsize W hW
      refine ⟨hWU,?_⟩
      rw [hnW]
      exact le_mul_of_one_le_right (by positivity) (one_le_exp_iff.mpr (by linarith))
    · intro S hS
      obtain ⟨W,hW,he⟩ := hcapture S hS.1 hS.2.1
      refine ⟨W,hW,?_⟩
      rw [he,hS.2.1]
      linarith
    · apply hlen.trans
      have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤d+1 by linarith)
      have hb' := mul_le_mul_of_nonneg_left (show d+1≤d+P by linarith)
        (show 0≤100*q*P by positivity)
      have hlow : 1≤q*P*(d+P) := le_trans hqP (le_mul_of_one_le_right (by positivity) (by linarith))
      have hl : log 2≤(1:ℝ) := by have := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2); linarith
      change _≤200*q*P*(d+P)
      dsimp only [d] at hh hb' hlow
      nlinarith
  · obtain ⟨caps,hsize,hcapture,hlen⟩ := hcover D R had hex hdim U n b τ hn hnu
      (le_of_not_ge hsmall) hb hbu hτ hτu
    refine ⟨caps,hsize,hcapture,hlen.trans ?_⟩
    apply description_cost hq hP hd (hτu.trans ht.le) (Nat.ceil_lt_add_one (by positivity)).le
      (plane_log_card hdim).2
      (plane_log_card (V:=Module.Dual K V) (Subspace.dual_finrank_eq.trans hdim)).1

end
end SharpLogRamsey.PlanarLearning

end

end OAI
