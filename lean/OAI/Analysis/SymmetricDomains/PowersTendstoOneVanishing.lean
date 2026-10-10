import Mathlib
import OAI.Analysis.SymmetricDomains.VariableEulerAutomorphismFamily

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
namespace Release061
open Set Filter Topology Metric
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

theorem powers_tendsto_one_of_vanishing_normalized_displacement
    (hU : IsOpen U) [LocallyCompactSpace U] (hc : IsPreconnected U)
    (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    {ι : Type*} (l : Filter ι) [NeBot l] (q : ι → Biholomorph U U)
    (h : ι → ℝ) (hp : ∀ i, 0≤h i) (N : ι → ℕ) {T : ℝ} (hT : 0<T)
    (hNT : ∀ i, (N i:ℝ)*h i≤T) (p : U) {R : ℝ} (hR : 0<R)
    (hRU : closedBall p.val R⊆U)
    (hstep : ∀ ε : ℝ, 0<ε → ∀ᶠ i in l, ∀ y∈closedBall p.val R,
      ‖(q i).ambientAut y-y‖≤ε*h i) :
    Tendsto (fun i => (q i)^(N i)) l (𝓝 1) := by
  have hbound (ε : ℝ) (hε : 0<ε) : ∀ᶠ i in l, ∀ x∈closedBall p.val (R/2),
      dist (((q i).ambientAut^[N i]) x) x≤ε := by
    let d : ℝ := min (R/(4*T)) (ε/(2*T))
    have hd : 0<d := lt_min (div_pos hR (by positivity)) (div_pos hε (by positivity))
    have hdR : d*T≤R/4 := by
      have hv := (le_div_iff₀ (show 0<4*T by positivity)).mp (min_le_left (R/(4*T)) (ε/(2*T)))
      dsimp [d]
      nlinarith
    have hdε : d*T≤ε/2 := by
      have hv := (le_div_iff₀ (show 0<2*T by positivity)).mp (min_le_right (R/(4*T)) (ε/(2*T)))
      dsimp [d]
      nlinarith
    filter_upwards [hstep d hd] with i hi
    intro x hx
    have hsub : closedBall x (R/2)⊆closedBall p.val R := by
      intro y hy
      exact (dist_triangle y x p.val).trans (by linarith [mem_closedBall.mp hy,mem_closedBall.mp hx])
    have hn : (N i:ℝ)*(d*h i)≤d*T := by
      calc
        _ = d*((N i:ℝ)*h i) := by ring
        _ ≤ d*T := mul_le_mul_of_nonneg_left (hNT i) hd.le
    have hh := iterate_displacement_of_bound (q i).ambientAut x x (mul_nonneg hd.le (hp i))
      (R := R/2) (N := N i) (by simpa only [dist_self,zero_add] using hn.trans (hdR.trans (by linarith)))
      (fun y hy => hi y (hsub hy)) (N i) le_rfl
    simp only [dist_self,zero_add] at hh
    exact hh.trans (hn.trans (hdε.trans (half_le_self hε.le)))
  have hball : closedBall p.val (R/2)⊆U := (closedBall_subset_closedBall (half_le_self hR.le)).trans hRU
  have htend (x : Affine n) (hx : x∈closedBall p.val (R/2)) :
      Tendsto (fun i => ((q i)^(N i)).ambientAut x) l (𝓝 x) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hbound (ε/2) (half_pos hε)] with i hi
    have hv := hi x hx
    simpa only [ambientAut_iterate (p := ⟨x,hball hx⟩),ambientAut_apply (p := ⟨x,hball hx⟩)] using
      hv.trans_lt (half_lt_self hε)
  let V : Set U := Subtype.val ⁻¹' closedBall p.val R
  have hV : IsCompact V := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    simpa only [V,image_preimage_eq_inter_range,Subtype.range_coe_subtype,ofPred_mem_eq,
      inter_eq_left.mpr hRU] using isCompact_closedBall p.val R
  let K : Set (Biholomorph U U) := (fun e : Biholomorph U U => e.toHomeomorph p) ⁻¹' V
  have hK : IsCompact K :=
    (bounded_divisible_automorphism_evaluation_proper hU hc hbd Γ hhol p).isCompact_preimage hV
  have hpow : ∀ᶠ i in l, (q i)^(N i)∈K := by
    filter_upwards [hbound R hR] with i hi
    have hv := hi p.val (mem_closedBall_self (by linarith))
    change (((q i)^(N i)).toHomeomorph p).val∈closedBall p.val R
    simpa only [mem_closedBall,ambientAut_iterate] using hv
  obtain ⟨e,he,heq⟩ := exists_tendsto_of_compact_local_pointwise hU hc l
    (fun i => (q i)^(N i)) K hK hpow p (half_pos hR) hball id htend
  have he1 : e=1 := eq_of_ambientAut_eventuallyEq hU hc p (by
    filter_upwards [closedBall_mem_nhds p.val (half_pos hR)] with x hx
    rw [heq hx,ambientAut_apply 1 ⟨x,hball hx⟩,one_apply]
    rfl)
  rwa [he1] at he
end Biholomorph
end Release061

end

end OAI
