import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapLinearCoordinates

namespace OAI

/-! An invertible target frame from two transverse planes sharing their
second coordinate direction. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma baseLinear_pair (P : Base →L[ℝ] ProjectionTarget 3) (r s : ℝ) :
    P ![r,s] = r • P ![1,0] + s • P ![0,1] := by
  have he : (![r,s] : Base) = r • ![1,0]+s • ![0,1] := by
    ext i
    fin_cases i <;> simp
  rw [he,map_add,map_smul,map_smul]

def crossingLeft : (Base × ℝ) →L[ℝ] Base :=
  ContinuousLinearMap.pi ![(ContinuousLinearMap.proj (0 : Fin 2)).comp
    (ContinuousLinearMap.fst ℝ Base ℝ),ContinuousLinearMap.snd ℝ Base ℝ]

def crossingRight : (Base × ℝ) →L[ℝ] Base :=
  ContinuousLinearMap.pi ![(ContinuousLinearMap.proj (1 : Fin 2)).comp
    (ContinuousLinearMap.fst ℝ Base ℝ),ContinuousLinearMap.snd ℝ Base ℝ]

def crossingAxis : (Base × ℝ) →L[ℝ] Base :=
  ContinuousLinearMap.pi ![0,ContinuousLinearMap.snd ℝ Base ℝ]

lemma crossingLeft_apply (z : Base × ℝ) : crossingLeft z = ![z.1 0,z.2] := by
  ext i
  fin_cases i <;> rfl

lemma crossingRight_apply (z : Base × ℝ) : crossingRight z = ![z.1 1,z.2] := by
  ext i
  fin_cases i <;> rfl

lemma crossingAxis_apply (z : Base × ℝ) : crossingAxis z = ![0,z.2] := by
  ext i
  fin_cases i <;> rfl

def crossingTargetLinear (P Q : Base →L[ℝ] ProjectionTarget 3) :
    (Base × ℝ) →L[ℝ] ProjectionTarget 3 :=
  P.comp crossingLeft + Q.comp crossingRight - P.comp crossingAxis

lemma crossingTargetLinear_apply (P Q : Base →L[ℝ] ProjectionTarget 3) (z : Base × ℝ) :
    crossingTargetLinear P Q z = P ![z.1 0,z.2]+Q ![z.1 1,z.2]-P ![0,z.2] := by
  change P (crossingLeft z)+Q (crossingRight z)-P (crossingAxis z) = _
  rw [crossingLeft_apply,crossingRight_apply,crossingAxis_apply]

theorem crossingTargetLinear_bijective (P Q : Base →L[ℝ] ProjectionTarget 3)
    (hcommon : P ![0,1] = Q ![0,1])
    (hsurj : Function.Surjective (fun z : Base × Base => P z.1-Q z.2)) :
    Function.Bijective (crossingTargetLinear P Q) := by
  have hs : Function.Surjective (crossingTargetLinear P Q) := by
    intro w
    obtain ⟨⟨x,y⟩,hxy⟩ := hsurj w
    refine ⟨(![x 0,-y 0],x 1-y 1),?_⟩
    rw [crossingTargetLinear_apply]
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    have hx : P x = x 0 • P ![1,0]+x 1 • P ![0,1] := by
      convert baseLinear_pair P (x 0) (x 1) using 1
      congr 1
      ext i
      fin_cases i <;> rfl
    have hy : Q y = y 0 • Q ![1,0]+y 1 • Q ![0,1] := by
      convert baseLinear_pair Q (y 0) (y 1) using 1
      congr 1
      ext i
      fin_cases i <;> rfl
    change P x-Q y = w at hxy
    rw [baseLinear_pair P (x 0) (x 1-y 1),
      baseLinear_pair Q (-y 0) (x 1-y 1),baseLinear_pair P 0 (x 1-y 1),hcommon]
    rw [hx,hy,hcommon] at hxy
    convert hxy using 1
    module
  refine ⟨?_,hs⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (crossingTargetLinear P Q).toLinearMap) (by simp [Base])).mpr hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
