import OAI.Geometry.SurfaceImmersion.Atlas.QuadraticCutoffBounds
import OAI.Geometry.Immersion.ClosedSurface.WeightedBounds

namespace OAI

/-! Disjoint supports prevent a factor counting the prescribed points in
the finite-point preparation estimates. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.SphericalJets
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem disjoint_sum_jet_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → E → V) (hq : ∀ i ∈ s, ContDiff ℝ ∞ (q i))
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (tsupport (q i)) (tsupport (q j)))
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    (hb : ∀ i ∈ s, ∀ x, ‖iteratedFDeriv ℝ j (q i) x‖ ≤ C) (x : E) :
    ‖iteratedFDeriv ℝ j (fun x => ∑ i ∈ s, q i x) x‖ ≤ C := by
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => ((hq i hi).of_le (by simp)).contDiffAt)]
  have hz (i : ι) (hx : x ∉ tsupport (q i)) : iteratedFDeriv ℝ j (q i) x = 0 := by
    by_contra hn
    exact hx (tsupport_iteratedFDeriv_subset j (subset_closure hn))
  by_cases hex : ∃ i ∈ s, x ∈ tsupport (q i)
  · obtain ⟨i,hi,hxi⟩ := hex
    have hzero : ∀ k ∈ s, k ≠ i → iteratedFDeriv ℝ j (q k) x = 0 := by
      intro k hk hki
      apply hz k
      exact fun hxk => Set.disjoint_left.mp (hdisj hk hi hki) hxk hxi
    rw [Finset.sum_eq_single i hzero (by simp [hi])]
    exact hb i hi x
  · have hzero : ∀ i ∈ s, iteratedFDeriv ℝ j (q i) x = 0 := by
      intro i hi
      exact hz i (fun hxi => hex ⟨i,hi,hxi⟩)
    rw [Finset.sum_eq_zero hzero,norm_zero]
    exact hC

theorem disjoint_sum_weighted_bound {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q : ι → E → V) (hq : ∀ i ∈ s, ContDiff ℝ ∞ (q i))
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (tsupport (q i)) (tsupport (q j)))
    {C : ℝ} (hC : 0 ≤ C) {m : ℕ}
    (hb : ∀ i ∈ s, WeightedEstimates.WeightedBound univ 1 m C (q i)) :
    WeightedEstimates.WeightedBound univ 1 m C (fun x => ∑ i ∈ s, q i x) := by
  intro j hj x hx
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ]
  apply disjoint_sum_jet_bound s q hq hdisj hC j
  intro i hi y
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hb i hi j hj y (mem_univ y)

end ClosedSurfaceR4.SphericalJets

end

end OAI
