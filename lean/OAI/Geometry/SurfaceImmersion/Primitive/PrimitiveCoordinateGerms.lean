import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCoordinateData
import OAI.Geometry.SurfaceImmersion.Geometry.TensorFrameReadBounds

namespace OAI

/-! The finite coordinate model agrees with the actual corrected amplitude
on a neighborhood, including at zero cutoff values. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
local instance coordinateGermFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance coordinateGermFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
local instance coordinateGermDualNormed : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coordinateGermDualSpace : NormedSpace ℝ (TensorFiber →L[ℝ] ℝ) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
local instance coordinateGermDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordinateGermDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance coordinateGermSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coordinateGermSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

lemma primitiveCoordinateData_germ
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hs : ∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1))
    (u : ∀ p : M, CovariantTwoTensor p) (i : B.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) (a : B.centers × Fin 3)
    (ha : p ∈ tsupport (B.weight a.1)) :
    let S : Set (B.centers × Fin 3) := {b | p ∈ tsupport (B.weight b.1)}
    (fun y => primitiveParameterAmplitude a (B.primitiveCoordinateData P psi phi u i S y)) =ᶠ[𝓝 (chart (i : M) p)]
      (B.correctedPrimitiveAmplitude P psi phi u a ∘ (chart (i : M)).symm) := by
  classical
  dsimp only
  have hz : ∀ᶠ q in 𝓝 p, ∀ b : B.centers × Fin 3,
      p ∉ tsupport (B.weight b.1) → psi b q = 0 := by
    apply Filter.eventually_all.mpr
    intro b
    by_cases hb : p ∈ tsupport (B.weight b.1)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hb))
    · exact (notMem_tsupport_iff_eventuallyEq.mp (fun h => hb (hs b h))).mono (fun _ h _ => h)
  have hc : ContinuousAt (chart (i : M)).symm (chart (i : M) p) :=
    ((chart (i : M)).continuousOn_symm _ ((chart (i : M)).map_source hp)).continuousAt
      ((chart (i : M)).open_target.mem_nhds ((chart (i : M)).map_source hp))
  have hc' : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
    simpa only [(chart (i : M)).left_inv hp] using hc.tendsto
  filter_upwards [hc'.eventually hz,
    (chart (i : M)).open_target.mem_nhds ((chart (i : M)).map_source hp)] with y hy hyT
  have hq := (chart (i : M)).map_target hyT
  have he := B.primitiveCoordinateData_amplitude P psi phi hphi u i
    {b | p ∈ tsupport (B.weight b.1)} a ha hq hy
  simpa only [(chart (i : M)).right_inv hyT,Function.comp_apply] using he

lemma primitiveCoordinateData_smoothAt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (hpsi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a))
    (hphi : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (phi a))
    (hQ : ∀ (a : B.centers × Fin 3) (p : M), p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p))
    (u : ∀ p : M, CovariantTwoTensor p)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (i : B.centers) {p : M} (hp : p ∈ tsupport (B.weight i)) :
    let S : Set (B.centers × Fin 3) := {b | p ∈ tsupport (B.weight b.1)}
    ContDiffAt ℝ ∞ (B.primitiveCoordinateData P psi phi u i S) (chart (i : M) p) := by
  classical
  dsimp only
  have hsource := B.weight_support i hp
  have htarget := (chart (i : M)).map_source hsource
  have hq (a : B.centers × Fin 3) : ContDiffAt ℝ ∞
      (fun y => if p ∈ tsupport (B.weight a.1) then B.coefficientFrameRead P i a y else 0)
      (chart (i : M) p) := by
    by_cases ha : p ∈ tsupport (B.weight a.1)
    · simp only [ite_eq_left ha]
      exact B.coefficientFrameRead_smoothAt P i a hsource (B.weight_support a.1 ha) (hQ a p ha)
    · simpa only [ite_eq_right ha] using (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : JetPolynomial.Base => (0 : TensorFiber →L[ℝ] ℝ)) (chart (i : M) p))
  have hw (a : B.centers × Fin 3) : ContDiffAt ℝ ∞
      (psi a ∘ (chart (i : M)).symm) (chart (i : M) p) :=
    ((hpsi a).comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn.contDiffAt
      ((chart (i : M)).open_target.mem_nhds htarget)
  have hv (a : B.centers × Fin 3) : ContDiffAt ℝ ∞
      (fun y => if p ∈ tsupport (B.weight a.1) then B.phaseCovectorRead i (phi a) y else 0)
      (chart (i : M) p) := by
    by_cases ha : p ∈ tsupport (B.weight a.1)
    · simp only [ite_eq_left ha]
      exact (B.phaseCovectorRead_smoothOn i (phi a) (hphi a)).contDiffAt
        ((chart (i : M)).open_target.mem_nhds htarget)
    · simpa only [ite_eq_right ha] using (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : JetPolynomial.Base => (0 : Plane →L[ℝ] ℝ)) (chart (i : M) p))
  have hH := (B.tensorFrameRead_smoothOn i u hu).contDiffAt
    ((chart (i : M)).open_target.mem_nhds htarget)
  exact (((contDiffAt_pi.mpr hq).prodMk (contDiffAt_pi.mpr hw)).prodMk
    (contDiffAt_pi.mpr hv)).prodMk hH

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
