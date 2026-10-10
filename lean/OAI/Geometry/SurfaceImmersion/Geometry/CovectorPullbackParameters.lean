import OAI.Geometry.SurfaceImmersion.Atlas.IndependentPhaseProjections
import OAI.Geometry.Immersion.ClosedSurface.AtlasPhases

namespace OAI

/-! Actual pullback of phase covectors by a chart derivative. Its parameter
map is open when the chart determinant is nonzero. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

def pullCovectorMap (A : CurvePlane →L[ℝ] CurvePlane) : CurvePlane →L[ℝ] CurvePlane :=
  (((A dx).1 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    ((A dx).2 • ContinuousLinearMap.snd ℝ ℝ ℝ)).prod
  (((A dy).1 • ContinuousLinearMap.fst ℝ ℝ ℝ) +
    ((A dy).2 • ContinuousLinearMap.snd ℝ ℝ ℝ))

lemma pullCovectorMap_apply (A : CurvePlane →L[ℝ] CurvePlane) (v : CurvePlane) :
    pullCovectorMap A v = pullCovector A v := by
  ext <;> simp [pullCovectorMap,pullCovector] <;> ring

lemma pullCovectorMap_surjective (A : CurvePlane →L[ℝ] CurvePlane)
    (hA : coordDet A ≠ 0) : Function.Surjective (pullCovectorMap A) := by
  intro y
  refine ⟨(((A dy).2*y.1-(A dx).2*y.2)/coordDet A,
    ((A dx).1*y.2-(A dy).1*y.1)/coordDet A),?_⟩
  rw [pullCovectorMap_apply]
  ext <;> dsimp [pullCovector] <;> field_simp [hA] <;> dsimp [coordDet] <;> ring

lemma covectorDet_pullback (A : CurvePlane →L[ℝ] CurvePlane) (v w : CurvePlane) :
    covectorDet (pullCovector A v) (pullCovector A w) = coordDet A * covectorDet v w := by
  dsimp [covectorDet,pullCovector,coordDet]
  ring

lemma phaseLinear_ne_zero_on_kernel {v w t : CurvePlane}
    (hdet : covectorDet v w ≠ 0) (ht : t ≠ 0) (hv : phaseLinear v t = 0) :
    phaseLinear w t ≠ 0 := by
  intro hw
  by_cases ht1 : t.1 = 0
  · have ht2 : t.2 ≠ 0 := fun ht2 => ht (Prod.ext ht1 ht2)
    have he : covectorDet v w * t.2 = v.1 * phaseLinear w t-w.1 * phaseLinear v t := by
      dsimp [covectorDet,phaseLinear_apply]
      ring
    rw [hv,hw,mul_zero,mul_zero,sub_self] at he
    exact hdet ((mul_eq_zero.mp he).resolve_right ht2)
  · have he : covectorDet v w * t.1 = w.2 * phaseLinear v t-v.2 * phaseLinear w t := by
      dsimp [covectorDet,phaseLinear_apply]
      ring
    rw [hv,hw,mul_zero,mul_zero,sub_self] at he
    exact hdet ((mul_eq_zero.mp he).resolve_right ht1)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma independent_pulled_covectors_open_dense {i j : ι} (hij : i ≠ j)
    (A B : CurvePlane →L[ℝ] CurvePlane) (hA : coordDet A ≠ 0) (hB : coordDet B ≠ 0)
    (a b : CurvePlane) :
    IsOpen {ell : ι → CurvePlane |
      covectorDet (pullCovector A (ell i+a)) (pullCovector B (ell j+b)) ≠ 0} ∧
    Dense {ell : ι → CurvePlane |
      covectorDet (pullCovector A (ell i+a)) (pullCovector B (ell j+b)) ≠ 0} := by
  let T : (CurvePlane × CurvePlane) →L[ℝ] (CurvePlane × CurvePlane) :=
    ((pullCovectorMap A).comp (ContinuousLinearMap.fst ℝ CurvePlane CurvePlane)).prod
      ((pullCovectorMap B).comp (ContinuousLinearMap.snd ℝ CurvePlane CurvePlane))
  have hT : Function.Surjective T := by
    intro y
    obtain ⟨v,hv⟩ := pullCovectorMap_surjective A hA y.1
    obtain ⟨w,hw⟩ := pullCovectorMap_surjective B hB y.2
    exact ⟨(v,w),Prod.ext hv hw⟩
  let F : (ι → CurvePlane) → CurvePlane × CurvePlane :=
    fun ell => T (phasePairProjection i j ell+(a,b))
  have hF : Continuous F := by fun_prop
  have hopen : IsOpenMap F := (T.isOpenMap hT).comp
    ((isOpenMap_add_right (a,b)).comp
      ((phasePairProjection i j).isOpenMap (phasePairProjection_surjective hij)))
  have he : {ell : ι → CurvePlane |
      covectorDet (pullCovector A (ell i+a)) (pullCovector B (ell j+b)) ≠ 0} =
      F ⁻¹' {z | covectorDet z.1 z.2 ≠ 0} := by
    ext ell
    change covectorDet (pullCovector A (ell i+a)) (pullCovector B (ell j+b)) ≠ 0 ↔
      covectorDet (pullCovectorMap A (ell i+a)) (pullCovectorMap B (ell j+b)) ≠ 0
    rw [pullCovectorMap_apply,pullCovectorMap_apply]
  rw [he]
  exact ⟨covectorDet_open_dense.1.preimage hF,covectorDet_open_dense.2.preimage hopen⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
