import OAI.Analysis.CircleDomains.Transfer.ModelScalarPullback
import OAI.Analysis.CircleDomains.Transfer.ModelHeightDescent
import OAI.Analysis.CircleDomains.Topology.CompactValueFlattening

namespace OAI

/-! The flattened height, cut off beyond the actual omitted set, is a
compact continuous Sobolev test on the source. The constancy on holes is
proved from the constructed height. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem height_cutoff_constant_on_components (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (T : ℝ → ℝ) (η : EuclideanPlane → ℝ)
    (hη : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), η x = 1)
    {p q : Sphere} (hp : p ∉ extendAtInfinity M.function '' G)
    (hq : q ∈ connectedComponentIn (extendAtInfinity M.function '' G)ᶜ p) :
    sphereFromPlaneFunction (fun x => η x*T (H.height (complexPlaneCoordinates x))) p =
      sphereFromPlaneFunction (fun x => η x*T (H.height (complexPlaneCoordinates x))) q := by
  have hheight := M.height_constant_on_sphere_components hinf H hHz hp hq
  have hqout := connectedComponentIn_subset _ _ hq
  cases p using OnePoint.rec with
  | infty => exact (hp ⟨_, hinf, rfl⟩).elim
  | coe z =>
    cases q using OnePoint.rec with
    | infty => exact (hqout ⟨_, hinf, rfl⟩).elim
    | coe w =>
      have hz : complexPlaneCoordinates.symm z ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) := by
        simpa only [physicalPlaneDomain, mem_preimage, planeSphere, complexPlaneCoordinates.apply_symm_apply] using hp
      have hw : complexPlaneCoordinates.symm w ∉ physicalPlaneDomain (extendAtInfinity M.function '' G) := by
        simpa only [physicalPlaneDomain, mem_preimage, planeSphere, complexPlaneCoordinates.apply_symm_apply, mem_compl_iff] using hqout
      simp only [sphereFromPlaneFunction_coe, hη _ hz, hη _ hw,
        complexPlaneCoordinates.apply_symm_apply, one_mul]
      exact congrArg T (by simpa only [finiteCoord_coe] using hheight)

 theorem compact_flattened_height_pullback (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} (H : ControlledHeight R d)
    (hHz : ∀ᵐ x ∂volume.restrict (physicalPlaneDomain (extendAtInfinity M.function '' G))ᶜ,
      heightLimitGradient H.error₀ H.error₁ x = 0)
    (O : Set ℝ) (hO : MeasurableSet O) (A : ℝ)
    (W : DeGiorgi.MemW1pWitness 2 (flattenValues O ∘ H.height ∘ complexPlaneCoordinates) (Metric.ball 0 A))
    (η : EuclideanPlane → ℝ) (hη : ContDiff ℝ ∞ η) (hηs : HasCompactSupport η)
    (hηA : tsupport η ⊆ Metric.ball 0 A)
    (hηF : ∀ x ∉ physicalPlaneDomain (extendAtInfinity M.function '' G), η x = 1) :
    let v := fun x => η x*flattenValues O (H.height (complexPlaneCoordinates x))
    let w := fun x => sphereFromPlaneFunction v (invFun M.projection (planeSphere x))
    Continuous w ∧ HasCompactSupport w ∧
      Nonempty (DeGiorgi.MemW1pWitness 2 w (physicalPlaneDomain G)) := by
  let v := fun x => η x*flattenValues O (H.height (complexPlaneCoordinates x))
  have hv : Continuous v := hη.continuous.mul
    ((flattenValues_lipschitz hO).continuous.comp (H.height.continuous.comp complexPlaneCoordinates.continuous))
  have hvs : HasCompactSupport v := hηs.mul_right
  obtain ⟨V⟩ := exists_global_compact_cutoff_witness Metric.isOpen_ball W.memW1p hη hηs hηA
  obtain ⟨hw, hws, Ww, _⟩ := M.compact_scalar_pullback hsard hsch hG hconn hinf hTD hv hvs V
    (fun p hp q hq => M.height_cutoff_constant_on_components hinf H hHz (flattenValues O) η hηF hp hq)
  exact ⟨hw, hws, ⟨Ww⟩⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
