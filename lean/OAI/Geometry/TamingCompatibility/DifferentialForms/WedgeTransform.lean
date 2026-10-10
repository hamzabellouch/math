import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.PlaneNormalization

namespace OAI

section

noncomputable section
open scoped RealInnerProductSpace ContDiff
namespace TamingCompatibility.UnitaryFrame
open FormMetric

def wedgeTransform (b : Fin 4 → V) : W →L[ℝ] W :=
  ∑ i : Fin 6, (PiLp.proj 2 (fun _ : Fin 6 => ℝ) i).smulRight
    (wedge (b (pairLeft i)) (b (pairRight i)))

lemma wedgeTransform_apply (b : Fin 4 → V) (w : W) :
    wedgeTransform b w = ∑ i : Fin 6, w i • wedge (b (pairLeft i)) (b (pairRight i)) := by
  simp [wedgeTransform]

lemma wedgeTransform_wedge (b : Fin 4 → V) (u v : V) :
    wedgeTransform b (wedge u v) =
      wedge (∑ i : Fin 4, u i • b i) (∑ i : Fin 4, v i • b i) := by
  rw [wedgeTransform_apply]
  ext i
  fin_cases i <;> simp [wedge,pairLeft,pairRight,Fin.sum_univ_succ] <;> ring

lemma wedge_smul_left (c : ℝ) (u v : V) : wedge (c • u) v = c • wedge u v := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma wedge_smul_right (c : ℝ) (u v : V) : wedge u (c • v) = c • wedge u v := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma wedge_sub_right (u v w : V) : wedge u (v-w) = wedge u v - wedge u w := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma wedge_self (u : V) : wedge u u = 0 := by
  ext i
  fin_cases i <;> simp [wedge] <;> ring

lemma norm_wedge_orthonormal (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ⟪u,v⟫ = 0) :
    ‖wedge u v‖ = 1 := by
  have h := wedge_inner u v u v
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,
    hu,hv,huv,zero_mul,sub_zero,one_pow,mul_one] at h
  nlinarith [norm_nonneg (wedge u v)]

lemma wedge_normalized (a b : V) (_ha : a ≠ 0) :
    wedge (PlaneVariation.first a) (PlaneVariation.second a b) =
      (PlaneVariation.area a b)⁻¹ • wedge a b := by
  simp only [PlaneVariation.first,PlaneVariation.second,PlaneVariation.normalPart,
    PlaneVariation.area,wedge_smul_left,wedge_smul_right,wedge_sub_right,wedge_self,
    smul_zero,sub_zero,smul_smul,mul_inv_rev]

lemma norm_wedge_area (a b : V) (ha : a ≠ 0) (hab : PlaneVariation.normalPart a b ≠ 0) :
    ‖wedge a b‖ = PlaneVariation.area a b := by
  have hh := norm_wedge_orthonormal _ _ (PlaneVariation.norm_first ha)
    (PlaneVariation.norm_second hab) (PlaneVariation.first_second_orthogonal ha b)
  rw [wedge_normalized a b ha,norm_smul,Real.norm_eq_abs,abs_inv,
    abs_of_pos (PlaneVariation.area_pos ha hab)] at hh
  exact ((inv_mul_eq_one₀ (ne_of_gt (PlaneVariation.area_pos ha hab))).mp hh).symm

lemma wedge_contDiff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : WithTop ℕ∞} {u v : D → V} (hu : ContDiff ℝ n u) (hv : ContDiff ℝ n v) :
    ContDiff ℝ n (fun x => wedge (u x) (v x)) := by
  apply (contDiff_piLp _).mpr
  intro i
  have huc (j : Fin 4) := (contDiff_piLp _).mp hu j
  have hvc (j : Fin 4) := (contDiff_piLp _).mp hv j
  fin_cases i <;> simp [wedge] <;> fun_prop

lemma wedgeTransform_contDiff {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : WithTop ℕ∞} {b : Fin 4 → D → V} (hb : ∀ i, ContDiff ℝ n (b i)) :
    ContDiff ℝ n (fun z => wedgeTransform (fun i => b i z)) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.smulRight (wedge_contDiff (hb _) (hb _))

end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.PlaneVariation
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma first_lipschitz_bound {a b : V} {m : ℝ} (hm : 0 < m) (ha : m ≤ ‖a‖) (hb : b ≠ 0) :
    ‖first a-first b‖ ≤ (2/m)*‖a-b‖ := by
  have han : 0 < ‖a‖ := lt_of_lt_of_le hm ha
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have he : first a-first b = ‖a‖⁻¹ • (a-b) + (‖a‖⁻¹-‖b‖⁻¹) • b := by
    simp only [first,smul_sub,sub_smul]
    abel
  have hc : |‖a‖⁻¹-‖b‖⁻¹| * ‖b‖ = |‖b‖-‖a‖|/‖a‖ := by
    rw [inv_sub_inv han.ne' hbn.ne',abs_div,abs_mul,abs_of_pos han,abs_of_pos hbn]
    field_simp
  calc
    _ ≤ ‖‖a‖⁻¹ • (a-b)‖+‖(‖a‖⁻¹-‖b‖⁻¹) • b‖ := by rw [he]; exact norm_add_le _ _
    _ = (‖a-b‖+|‖b‖-‖a‖|)/‖a‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,hc]
      ring
    _ ≤ (2*‖a-b‖)/‖a‖ := by
      apply div_le_div_of_nonneg_right _ han.le
      have hh := abs_norm_sub_norm_le a b
      rw [abs_sub_comm] at hh
      linarith
    _ ≤ _ := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_left (by positivity) hm ha
end TamingCompatibility.PlaneVariation

end
end

end OAI
