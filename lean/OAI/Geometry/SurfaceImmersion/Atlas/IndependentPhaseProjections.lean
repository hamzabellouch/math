import OAI.Geometry.SurfaceImmersion.Atlas.NonparallelPhaseCovectors

namespace OAI

/-! Independent linear phase parameters give open surjective projections.
This transfers the elementary nonparallel-covector condition to any finite
family of independently perturbed phases. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.PhaseGeometry
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def phasePairProjection (i j : ι) : (ι → CurvePlane) →L[ℝ] (CurvePlane × CurvePlane) :=
  (ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j)

omit [Fintype ι] in
lemma phasePairProjection_surjective {i j : ι} (hij : i ≠ j) :
    Function.Surjective (phasePairProjection i j) := by
  intro y
  refine ⟨Function.update (Function.update (fun _ => 0) i y.1) j y.2,?_⟩
  apply Prod.ext
  · simp [phasePairProjection,hij]
  · simp [phasePairProjection]

omit [Fintype ι] [DecidableEq ι] in
lemma phaseProjection_surjective (i : ι) :
    Function.Surjective (ContinuousLinearMap.proj i : (ι → CurvePlane) →L[ℝ] CurvePlane) := by
  intro y
  exact ⟨fun _ => y,rfl⟩

lemma shifted_covectorDet_open_dense (a b : CurvePlane) :
    IsOpen {z : CurvePlane × CurvePlane | covectorDet (z.1+a) (z.2+b) ≠ 0} ∧
      Dense {z : CurvePlane × CurvePlane | covectorDet (z.1+a) (z.2+b) ≠ 0} := by
  have he : (fun z : CurvePlane × CurvePlane => (z.1+a,z.2+b)) =
      (fun z => z + (a,b)) := rfl
  constructor
  · have hc : Continuous (fun z : CurvePlane × CurvePlane => (z.1+a,z.2+b)) := by fun_prop
    exact covectorDet_open_dense.1.preimage hc
  · change Dense ((fun z : CurvePlane × CurvePlane => (z.1+a,z.2+b)) ⁻¹'
        {z | covectorDet z.1 z.2 ≠ 0})
    rw [he]
    exact covectorDet_open_dense.2.preimage (isOpenMap_add_right (a,b))

lemma independent_covectorDet_open_dense {i j : ι} (hij : i ≠ j) (a b : CurvePlane) :
    IsOpen {ell : ι → CurvePlane | covectorDet (ell i+a) (ell j+b) ≠ 0} ∧
      Dense {ell : ι → CurvePlane | covectorDet (ell i+a) (ell j+b) ≠ 0} := by
  have h := shifted_covectorDet_open_dense a b
  exact ⟨h.1.preimage (phasePairProjection i j).continuous,
    h.2.preimage ((phasePairProjection i j).isOpenMap
      (phasePairProjection_surjective hij))⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
