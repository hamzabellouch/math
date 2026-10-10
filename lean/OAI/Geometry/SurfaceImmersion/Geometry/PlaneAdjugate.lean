import OAI.Geometry.Immersion.ClosedSurface.JacobianBounds

namespace OAI

/-! The explicit two-dimensional inverse matrix used for phase charts. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes

def planeAdjugate (A : Base →L[ℝ] Base) : Base →L[ℝ] Base :=
  (((A dy).2 • ContinuousLinearMap.fst ℝ ℝ ℝ -
    (A dy).1 • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (-(A dx).2 • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (A dx).1 • ContinuousLinearMap.snd ℝ ℝ ℝ))

lemma planeAdjugate_apply (A : Base →L[ℝ] Base) (v : Base) :
    planeAdjugate A v = ((A dy).2*v.1-(A dy).1*v.2,
      -(A dx).2*v.1+(A dx).1*v.2) := rfl

lemma planeAdjugate_comp (A : Base →L[ℝ] Base) :
    (planeAdjugate A).comp A = coordDet A • ContinuousLinearMap.id ℝ Base := by
  apply ContinuousLinearMap.ext
  intro v
  change planeAdjugate A (A v) = coordDet A • v
  rw [planeAdjugate_apply,linear_apply_basis A v]
  apply Prod.ext <;>
    simp only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,coordDet] <;> ring

lemma planeAdjugate_norm_le (A : Base →L[ℝ] Base) : ‖planeAdjugate A‖ ≤ 2*‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [planeAdjugate_apply,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_le_iff]
  have hdx : ‖A dx‖ ≤ ‖A‖ := by simpa [dx] using A.le_opNorm dx
  have hdy : ‖A dy‖ ≤ ‖A‖ := by simpa [dy] using A.le_opNorm dy
  have ha := (norm_fst_le (A dx)).trans hdx
  have hb := (norm_snd_le (A dx)).trans hdx
  have hc := (norm_fst_le (A dy)).trans hdy
  have hd := (norm_snd_le (A dy)).trans hdy
  have hv1 := norm_fst_le v
  have hv2 := norm_snd_le v
  simp only [Real.norm_eq_abs] at ha hb hc hd hv1 hv2
  constructor
  · calc
      _ ≤ |(A dy).2*v.1|+|(A dy).1*v.2| := abs_sub _ _
      _ ≤ ‖A‖*‖v‖+‖A‖*‖v‖ := by rw [abs_mul,abs_mul]; gcongr
      _ = _ := by ring
  · calc
      _ ≤ |-(A dx).2*v.1|+|(A dx).1*v.2| := abs_add_le _ _
      _ ≤ ‖A‖*‖v‖+‖A‖*‖v‖ := by rw [abs_mul,abs_neg,abs_mul]; gcongr
      _ = _ := by ring

def planeAdjugateOperator : (Base →L[ℝ] Base) →L[ℝ] (Base →L[ℝ] Base) :=
  LinearMap.mkContinuous
    { toFun := planeAdjugate
      map_add' := by
        intro A B
        apply ContinuousLinearMap.ext
        intro v
        change planeAdjugate (A+B) v = planeAdjugate A v + planeAdjugate B v
        simp only [planeAdjugate_apply,add_apply,Prod.fst_add,Prod.snd_add]
        ext <;> dsimp <;> ring
      map_smul' := by
        intro c A
        apply ContinuousLinearMap.ext
        intro v
        change planeAdjugate (c • A) v = c • planeAdjugate A v
        simp only [planeAdjugate_apply,smul_apply,Prod.smul_fst,
          Prod.smul_snd,smul_eq_mul,Prod.smul_mk]
        ext <;> dsimp <;> ring }
    2 planeAdjugate_norm_le

lemma planeAdjugateOperator_norm_le : ‖planeAdjugateOperator‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num) planeAdjugate_norm_le

lemma inverse_matrix_comp (A : Base →L[ℝ] Base) (hA : coordDet A ≠ 0) :
    ((coordDet A)⁻¹ • planeAdjugate A).comp A = ContinuousLinearMap.id ℝ Base := by
  rw [ContinuousLinearMap.smul_comp,planeAdjugate_comp,smul_smul,inv_mul_cancel₀ hA,one_smul]

end ClosedSurfaceR4.RealModes

end

end OAI
