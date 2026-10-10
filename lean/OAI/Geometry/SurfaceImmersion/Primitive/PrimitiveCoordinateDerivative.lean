import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCoordinateGerms
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveDataC1
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveAmplitudeChain

namespace OAI

/-! First-derivative control of the actual amplitude from its finite active
chart data. The data bounds involve only first jets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance coordDerivFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordDerivFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance coordDerivDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorNormed : NormedAddCommGroup (Plane →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorSpace : NormedSpace ℝ (Plane →L[ℝ] ℝ) := inferInstance
local instance coordDerivFiberT2 : T2Space TensorFiber := inferInstance
local instance coordDerivDualT2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordDerivCovectorT2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance coordDerivDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordDerivDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordDerivSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordDerivSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)
local instance coordDerivDataNormed : NormedAddCommGroup (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
local instance coordDerivDataSpace : NormedSpace ℝ (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
local instance coordDerivDataT2 : T2Space (PrimitiveAmplitudeData (B.centers × Fin 3)) := inferInstance
local instance coordDerivDataDualNormed : NormedAddCommGroup (PrimitiveAmplitudeData (B.centers × Fin 3) →L[ℝ] ℝ) := inferInstance
local instance coordDerivDataDualSpace : NormedSpace ℝ (PrimitiveAmplitudeData (B.centers × Fin 3) →L[ℝ] ℝ) := inferInstance

theorem primitiveCoordinateData_fderiv_bound
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hQ : ∀ (a : B.centers × Fin 3) (p : M), p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (i : B.centers) {p : M} (hp : p ∈ tsupport (B.weight i))
    {D : ℝ} (hD : 0 ≤ D)
    (hbq : ∀ a, p ∈ tsupport (B.weight a.1) →
      ‖fderiv ℝ (B.coefficientFrameRead P i a) (chart (i : M) p)‖ ≤ D)
    (hbw : ∀ a, ‖fderiv ℝ (psi a ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ D)
    (hbv : ∀ a, p ∈ tsupport (B.weight a.1) →
      ‖fderiv ℝ (B.phaseCovectorRead i (phi a)) (chart (i : M) p)‖ ≤ D)
    (hbH : ‖fderiv ℝ (B.tensorFrameRead i u) (chart (i : M) p)‖ ≤ D) :
    ‖fderiv ℝ (B.primitiveCoordinateData P psi phi u i
      {a | p ∈ tsupport (B.weight a.1)}) (chart (i : M) p)‖ ≤ D := by
  classical
  let x := chart (i : M) p
  let q := fun (a : B.centers × Fin 3) (y : JetPolynomial.Base) => if p ∈ tsupport (B.weight a.1) then B.coefficientFrameRead P i a y else 0
  let w := fun a => psi a ∘ (chart (i : M)).symm
  let v := fun (a : B.centers × Fin 3) (y : JetPolynomial.Base) => if p ∈ tsupport (B.weight a.1) then B.phaseCovectorRead i (phi a) y else 0
  have hs := B.weight_support i hp
  have ht := (chart (i : M)).map_source hs
  have hq (a : B.centers × Fin 3) : DifferentiableAt ℝ (q a) x := by
    dsimp only [q]
    split_ifs with ha
    · exact (B.coefficientFrameRead_smoothAt P i a hs (B.weight_support a.1 ha)
        (hQ a p ha)).differentiableAt (by simp)
    · exact differentiableAt_const _
  have hw (a : B.centers × Fin 3) : DifferentiableAt ℝ (w a) x :=
    (((hpsi a).comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn.contDiffAt
      ((chart (i : M)).open_target.mem_nhds ht)).differentiableAt (by simp)
  have hv (a : B.centers × Fin 3) : DifferentiableAt ℝ (v a) x := by
    dsimp only [v]
    split_ifs with ha
    · exact ((B.phaseCovectorRead_smoothOn i (phi a) (hphi a)).contDiffAt
        ((chart (i : M)).open_target.mem_nhds ht)).differentiableAt (by simp)
    · exact differentiableAt_const _
  have hH := ((B.tensorFrameRead_smoothOn i u hu).contDiffAt
    ((chart (i : M)).open_target.mem_nhds ht)).differentiableAt (by simp)
  apply primitive_data_fderiv_bound q w v (B.tensorFrameRead i u) x hq hw hv hH hD
  · intro a
    dsimp only [q]
    split_ifs with ha
    · exact hbq a ha
    · simpa only [fderiv_const_apply,norm_zero] using hD
  · exact hbw
  · intro a
    dsimp only [v]
    split_ifs with ha
    · exact hbv a ha
    · simpa only [fderiv_const_apply,norm_zero] using hD
  · exact hbH

theorem correctedAmplitude_coordinate_bound
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hQ : ∀ (a : B.centers × Fin 3) (p : M), p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (hs : ∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1))
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (i : B.centers) {p : M} (hp : p ∈ tsupport (B.weight i))
    (a : B.centers × Fin 3) (ha : p ∈ tsupport (B.weight a.1))
    (R D : ℝ)
    (hdata : ‖fderiv ℝ (B.primitiveCoordinateData P psi phi u i
      {b | p ∈ tsupport (B.weight b.1)}) (chart (i : M) p)‖ ≤ D)
    (hparam : let z : PrimitiveAmplitudeData (B.centers × Fin 3) :=
        B.primitiveCoordinateData P psi phi u i {b | p ∈ tsupport (B.weight b.1)} (chart (i : M) p);
      (primitiveDataOperator z.1).IsInvertible ∧ 0 < primitiveParameterCoefficient a z ∧
        |primitiveParameterAmplitude a z| ≤ R ∧
        ‖fderiv ℝ (primitiveParameterAmplitude a) z‖ ≤ R) :
    |B.correctedPrimitiveAmplitude P psi phi u a p| ≤ R ∧
      ‖fderiv ℝ (B.correctedPrimitiveAmplitude P psi phi u a ∘ (chart (i : M)).symm)
        (chart (i : M) p)‖ ≤ R*D := by
  let F := B.primitiveCoordinateData P psi phi u i {b | p ∈ tsupport (B.weight b.1)}
  have hg := B.primitiveCoordinateData_germ P psi phi hphi hs u i (B.weight_support i hp) a ha
  have hv := hg.self_of_nhds
  simp only [Function.comp_apply,(chart (i : M)).left_inv (B.weight_support i hp)] at hv
  refine ⟨hv ▸ hparam.2.2.1,?_⟩
  have he := hg.fderiv_eq (𝕜 := ℝ)
  change fderiv ℝ (primitiveParameterAmplitude a ∘ F) (chart (i : M) p) = _ at he
  rw [← he]
  exact primitive_amplitude_chain_bound a F (chart (i : M) p)
    (B.primitiveCoordinateData_smoothAt P psi phi hpsi hphi hQ u hu i hp)
    hparam.1 hparam.2.1 hparam.2.2.2 hdata

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
