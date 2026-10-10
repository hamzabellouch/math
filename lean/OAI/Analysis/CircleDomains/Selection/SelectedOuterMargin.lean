import OAI.Analysis.CircleDomains.Modulus.OuterBarrierMargin
import OAI.Analysis.CircleDomains.Rigidity.SelectedTraceBound

namespace OAI

/-! The selected compact coordinates are separated from every bounded
trace center on the unchanged outer source collar. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem planePair_eq_complex_symm (z : ℂ) :
    planePair z.re z.im = complexPlaneCoordinates.symm z := by
  apply complexPlaneCoordinates.injective
  apply Complex.ext <;> simp [complexPlaneCoordinates_apply]

 theorem planePair_sub_norm (z : ℂ) (x : EuclideanPlane) :
    ‖planePair z.re z.im-x‖ = ‖z-complexPlaneCoordinates x‖ := by
  rw [planePair_eq_complex_symm]
  rw [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z-x),
    map_sub, complexPlaneCoordinates.apply_symm_apply]

namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem selected_pair_outer_margin (M : CompactScalarModel G u)
    (harea : ExteriorCoefficientAreaTheorem)
    {R d R₀ A L δ ε v C r σ : ℝ} (H : ControlledHeight R d)
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    (S : FlattenedSourceSelection M H Wold A L δ ε)
    (hR₀ : 0 < R₀) (hsource : (((↑) : ℂ → Sphere) '' ball 0 R₀)ᶜ ⊆ G)
    (η : ℂ → ℝ) (θ : EuclideanPlane → ℝ)
    {x : EuclideanPlane} (hx : x ∈ physicalPlaneDomain G)
    (hη : η (complexPlaneCoordinates x) = 1)
    (hθ : θ (complexPlaneCoordinates.symm (M.function (complexPlaneCoordinates x))) = 1)
    (hH : |H.height (M.function (complexPlaneCoordinates x))-
      (M.function (complexPlaneCoordinates x)).im| ≤ v)
    (hs : complexPlaneCoordinates x ∉ ⋃ n, support (S.cutoff n))
    (hxR : 2*R₀ ≤ ‖x‖) {c : EuclideanPlane} (hc : ‖c‖ ≤ C)
    (hmargin : r+σ+(δ+v)+R₀+C ≤ ‖x‖) :
    r+σ ≤ ‖planePair (M.compactPrioritySource S.cutoff S.value η x)
      (M.compactHeightSource H (flattenValues S.heightValues) θ x)-c‖ := by
  have hp := M.compact_pair_error_outside_support H (flattenValues S.heightValues)
    (fun t => (S.height_close t).le) η θ S.cutoff S.value hx hη hθ hH hs
  have hex := M.exterior_deviation_le harea hR₀ hsource (complexPlaneCoordinates x)
    (by simpa only [complexPlaneCoordinates_norm] using hxR)
  have hmodel : ‖planePair (M.function (complexPlaneCoordinates x)).re
      (M.function (complexPlaneCoordinates x)).im-x‖ ≤ R₀ := by
    rwa [planePair_sub_norm]
  exact outer_pair_margin hp hmodel hc hmargin

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
