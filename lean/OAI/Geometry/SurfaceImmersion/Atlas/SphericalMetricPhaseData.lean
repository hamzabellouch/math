import OAI.Geometry.SurfaceImmersion.Geometry.SphericalLift
import OAI.Geometry.SurfaceImmersion.Geometry.SphericalJets
import OAI.Geometry.SurfaceImmersion.Atlas.MetricGoodPhaseData

namespace OAI

/-! A smooth three-space immersion supplies the actual starting phase geometry. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Matrix

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes

private lemma inner_spaceCoordinates_symm (X Y : RVec 4) :
    inner ℝ (spaceCoordinates.symm X) (spaceCoordinates.symm Y) = X ⬝ᵥ Y := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (spaceCoordinates_dot (spaceCoordinates.symm X) (spaceCoordinates.symm Y)).symm

private lemma fderiv_realDot_apply {F G : RField 4} {x : Base}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (v : Base) :
    fderiv ℝ (fun y => F y ⬝ᵥ G y) x v =
      F x ⬝ᵥ (fderiv ℝ G x v)+(fderiv ℝ F x v) ⬝ᵥ G x := by
  have hF' := spaceCoordinates.symm.hasFDerivAt.comp x hF.hasFDerivAt
  have hG' := spaceCoordinates.symm.hasFDerivAt.comp x hG.hasFDerivAt
  have hd := fderiv_inner_apply ℝ hF'.differentiableAt hG'.differentiableAt v
  have he : (fun y => inner ℝ (spaceCoordinates.symm (F y)) (spaceCoordinates.symm (G y))) =
      (fun y => F y ⬝ᵥ G y) := funext fun y => inner_spaceCoordinates_symm (F y) (G y)
  simp only [Function.comp_apply] at hd
  rw [he,hF'.fderiv,hG'.fderiv] at hd
  change fderiv ℝ (fun y => F y ⬝ᵥ G y) x v =
    inner ℝ (spaceCoordinates.symm (F x)) (spaceCoordinates.symm (fderiv ℝ G x v))+
      inner ℝ (spaceCoordinates.symm (fderiv ℝ F x v)) (spaceCoordinates.symm (G x)) at hd
  simpa only [inner_spaceCoordinates_symm] using hd

private lemma sphere_real_radial_first {F : RField 4} {x : Base}
    (hF : DifferentiableAt ℝ F x) (hunit : ∀ y, F y ⬝ᵥ F y = 1) (v : Base) :
    F x ⬝ᵥ coordDeriv v F x = 0 := by
  have he : (fun y => F y ⬝ᵥ F y) = (fun _ => (1 : ℝ)) := funext hunit
  have hd := congrArg (fun L : Base →L[ℝ] ℝ => L v)
    (congrArg (fun f : Base → ℝ => fderiv ℝ f x) he)
  rw [fderiv_realDot_apply hF hF] at hd
  simp only [fderiv_const_apply,zero_apply] at hd
  rw [dotProduct_comm (fderiv ℝ F x v) (F x)] at hd
  change F x ⬝ᵥ fderiv ℝ F x v = 0
  linarith

private lemma sphere_real_radial_second {F : RField 4} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hunit : ∀ y, F y ⬝ᵥ F y = 1) {x : Base} (hx : x ∈ U) (v w : Base) :
    F x ⬝ᵥ coordDeriv v (coordDeriv w F) x =
      -(coordDeriv v F x ⬝ᵥ coordDeriv w F x) := by
  have hFx := (hF x hx).contDiffAt (hU.mem_nhds hx)
  have he : (fun y => F y ⬝ᵥ coordDeriv w F y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact sphere_real_radial_first
      (((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)) hunit w
  have hd := congrArg (fun L : Base →L[ℝ] ℝ => L v) he.fderiv_eq
  rw [fderiv_realDot_apply (hFx.differentiableAt (by simp))
    ((contDiffAt_coordDeriv hFx w).differentiableAt (by simp))] at hd
  simp only [fderiv_const_apply,zero_apply] at hd
  change F x ⬝ᵥ fderiv ℝ (coordDeriv w F) x v =
    -(fderiv ℝ F x v ⬝ᵥ coordDeriv w F x)
  change F x ⬝ᵥ fderiv ℝ (coordDeriv w F) x v+
    fderiv ℝ F x v ⬝ᵥ coordDeriv w F x = 0 at hd
  linarith

/-- The inward radial pairing of the coordinate second form is the induced
metric, even though the coordinate representative is only smooth on its chart. -/
lemma sphere_realSecondForm_inward {F : RField 4} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hunit : ∀ y, F y ⬝ᵥ F y = 1) {x : Base} (hx : x ∈ U) (v w : Base) :
    realSecondForm F v w x ⬝ᵥ (-F x) =
      coordDeriv v F x ⬝ᵥ coordDeriv w F x := by
  have hFx := ((hF x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hX : coordDeriv dx F x ⬝ᵥ (-F x) = 0 := by
    rw [dotProduct_neg,dotProduct_comm,sphere_real_radial_first hFx hunit,neg_zero]
  have hY : coordDeriv dy F x ⬝ᵥ (-F x) = 0 := by
    rw [dotProduct_neg,dotProduct_comm,sphere_real_radial_first hFx hunit,neg_zero]
  unfold realSecondForm realNormalPart
  simp only [sub_dotProduct,smul_dotProduct,smul_eq_mul,hX,hY,mul_zero,sub_zero]
  rw [dotProduct_neg,dotProduct_comm,sphere_real_radial_second hU hF hunit hx,neg_neg]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- A spherical immersion has nonzero second fundamental form in every
coordinate chart, with the first coordinate direction as an explicit witness. -/
theorem spherical_coordinate_second_nonzero {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hunit : ∀ p, ‖G p‖ = 1)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) (p : M) :
    ∃ v w : Base, realSecondForm (coordinateMap G p) v w (coordinateCenter p) ≠ 0 := by
  have hcoords : ∀ x, coordinateMap G p x ⬝ᵥ coordinateMap G p x = 1 := by
    intro x
    dsimp only [coordinateMap,Function.comp_apply]
    rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,hunit]
    norm_num
  have hdir : coordDeriv dx (coordinateMap G p) (coordinateCenter p) ≠ 0 := by
    intro hz
    change fderiv ℝ (coordinateMap G p) (coordinateCenter p) dx = 0 at hz
    have hi := coordinateMap_immersion_center hG p (hI p)
    have he : dx = (0 : Base) := hi (by simpa only [map_zero] using hz)
    simp [dx] at he
  have hnorm : 0 < coordDeriv dx (coordinateMap G p) (coordinateCenter p) ⬝ᵥ
      coordDeriv dx (coordinateMap G p) (coordinateCenter p) := by
    have hn : 0 ≤ coordDeriv dx (coordinateMap G p) (coordinateCenter p) ⬝ᵥ
        coordDeriv dx (coordinateMap G p) (coordinateCenter p) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact hn.lt_of_ne' ((dotProduct_self_eq_zero).not.mpr hdir)
  refine ⟨dx,dx,?_⟩
  intro hz
  have hh := sphere_realSecondForm_inward (coordinateDomain_open p)
    (coordinateMap_smoothOn hG p) hcoords (coordinateCenter_mem p) dx dx
  rw [hz,zero_dotProduct] at hh
  linarith

variable [T2Space M] [CompactSpace M]

/-- A given smooth immersion into three-space yields a spherical immersion
and all the concrete phase geometry for any smooth target metric. -/
theorem metricPhaseData_of_three_space_immersion
    (g : SmoothMetric M) {F : M → SphericalStart.ThreeSpace}
    (hF : ContMDiff planeModel 𝓘(ℝ,SphericalStart.ThreeSpace) ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,SphericalStart.ThreeSpace) F p)) :
    ∃ G : M → Space, ContMDiff planeModel spaceModel ∞ G ∧
      (∀ p, ‖G p‖ = 1) ∧
      (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
      Nonempty (MetricGoodPhaseData g G) := by
  let v : Space := EuclideanSpace.single 0 1
  have hv : ‖v‖ = 1 := by simp [v]
  obtain ⟨G,hG,hu,hi⟩ := SphericalStart.spherical_immersion_of_three_space_immersion hv hF hI
  exact ⟨G,hG,hu,hi,MetricGoodPhaseData.nonempty g hG hi
    (spherical_coordinate_second_nonzero hG hu hi)⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
