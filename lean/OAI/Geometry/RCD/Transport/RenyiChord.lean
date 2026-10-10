import OAI.Geometry.RCD.Transport.RenyiTreeChord

namespace OAI

/-! # A compressed finite-dimensional Rényi chord from the actual RCD inputs

The selected plan has all maximal dyadic midpoints, a uniform density
bound, the scalar reduced-CD chord, and continuous endpoint entropy.
The full position-dependent CD* estimate remains a separate step.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.exists_compressed_renyi_chord
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X) (hK : K≤0)
    {N : ℝ} (hN : (n:ℝ)≤N) (a : RenyiTransportNode n X) :
    ∃ π : Measure C(Time,X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧ IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))) ∧
      (∀ t : Time, π.map (fun γ => γ t) ≤ compressionBudget K n a.distance a.capacity • hausdorff n X) ∧
      (∀ m, RenyiDyadicMaximal (hausdorff n X) (1-1/N) (fun t => π.map (fun γ => γ t)) m) ∧
      (∀ t, reducedChord K (N+1) a.distance (renyiIntegral (hausdorff n X) a.left N)
        (renyiIntegral (hausdorff n X) a.right N) t ≤
          renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N) ∧
      ContinuousAt (fun t : Time => renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N) 0 ∧
      ContinuousAt (fun t : Time => renyiIntegral (hausdorff n X) (π.map (fun γ => γ t)) N) 1 := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hN1 : 1<N := by linarith
  have hq0 : 0<1-1/N := sub_pos.mpr ((div_lt_one (by linarith : 0<N)).mpr hN1)
  have hq1 : 1-1/N<1 := by have := one_div_pos.mpr (by linarith : 0<N); linarith
  let S := hX.selectedRenyiSplit K n hn (1-1/N) hq0 hq1
  obtain ⟨π,hπ,hg,hp,hf⟩ := exists_plan_following_all_renyi_levels S a
  let := hπ
  exact ⟨π,hπ,hg,hp,hX.plan_following_renyi_tree_compression K n hn S a π hg hp hf,
    fun m => (hf m).maximal,hX.plan_following_renyi_tree_chord K n hn hK hN S a π hg hp hf⟩

end RegularPointCoordinates

end

end OAI
