import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldGradient
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldHeightHessian
import OAI.Probability.InvariantIsing.Fields.FieldHeightBox

namespace OAI

/-! The prescribed-magnetization functional has the uniform one-half
height modulus on a fixed strict partition. This uses the envelope
derivative and bounded spin products, independently of concavity. -/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma abs_weighted_unit_sum_le {I : Type*} [Fintype I] (w q d : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) :
    |∑ i, (-w i / 2 * q i) * d i| ≤ (1 / 2 : ℝ) * ∑ i, w i * |d i| := by
  calc
    _ ≤ ∑ i, |(-w i / 2 * q i) * d i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (w i / 2) * |d i| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_mul, abs_div, abs_neg, abs_of_nonneg (hw i),
        abs_of_nonneg (hq i).1, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (div_nonneg (hw i) (by norm_num)) (hq i).2) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

lemma magneticHeight_gradient_sum (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h)) {s : ℝ} (hs : |s| < 1)
    (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    (∑ i, F.P i (r, magneticHeightBias h s r) * d i) - d (Fin.last h.depth) / 2 =
      ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 *
        magneticFieldLevel (fieldStepOfStrictHeights h r hrs) s i) * d i := by
  have hc : (∑ i, (F.P i (r, magneticHeightBias h s r) -
      (if i = Fin.last h.depth then 1 / 2 else 0)) * d i) =
      (∑ i, F.P i (r, magneticHeightBias h s r) * d i) - d (Fin.last h.depth) / 2 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul]
    simp [div_eq_mul_inv, mul_comm]
  rw [← hc]
  apply Finset.sum_congr rfl
  intro i _
  rw [magneticHeight_optimized_gradient h F hU hs r hr hrs i]
  rfl

theorem constrainedFieldValue_strict_lipschitz (h : FieldStep) {s : ℝ} (hs : |s| < 1)
    (r q : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) (hq : q ∈ fieldStrictHeightCone h.depth) :
    |constrainedFieldValue (fieldStepOfStrictHeights h q hq) s -
      constrainedFieldValue (fieldStepOfStrictHeights h r hr) s| ≤
      (1 / 2 : ℝ) * ∑ i, (h.cut i.succ - h.cut i.castSucc) * |q i - r i| := by
  classical
  obtain ⟨lo, V, hlo, hrI, hqI⟩ := fieldHeightBox_pair r q hr hq
  let I := fieldHeightBox h.depth lo V
  have hI : IsOpen I := isOpen_fieldHeightBox _ _ _
  obtain ⟨F, hF⟩ := fieldHeightBox_family h lo V hlo
  let d := q - r
  let f := fun t : ℝ => constrainedHeightFieldValue h s (r + t • d)
  let g := fun t : ℝ => (∑ i, F.P i (r + t • d,
    magneticHeightBias h s (r + t • d)) * d i) - d (Fin.last h.depth) / 2
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : r + t • d ∈ I := by
    have he : r + t • d = (1 - t) • r + t • q := by dsimp only [d]; module
    rw [he]
    exact convex_fieldHeightBox _ _ _ hrI hqI (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hstrict (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      r + t • d ∈ fieldStrictHeightCone h.depth :=
    fieldHeightBox_subset_strict hlo.le (hp t ht)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (g t) t :=
    hasDerivAt_constrainedHeightFieldValue_line_at h F hI hF hs r d t (hp t ht) (hstrict t ht)
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖g t‖ ≤ (1 / 2 : ℝ) * ∑ i, (h.cut i.succ - h.cut i.castSucc) * |q i - r i| := by
    rw [Real.norm_eq_abs]
    dsimp only [g]
    rw [magneticHeight_gradient_sum h F hF hs _ d (hp t ht) (hstrict t ht)]
    exact abs_weighted_unit_sum_le _ _ d
      (fun i => (sub_pos.mpr (h.ordered_cut i.castSucc_lt_succ)).le)
      (fun i => magneticFieldLevel_mem_unit (fieldStepOfStrictHeights h (r + t • d)
        (hstrict t ht)) s i)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt) hb (convex_Icc (0 : ℝ) 1)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
  have he0 : f 0 = constrainedFieldValue (fieldStepOfStrictHeights h r hr) s := by
    simp only [f, zero_smul, add_zero, constrainedHeightFieldValue, dite_eq_left hr]
  have he1 : f 1 = constrainedFieldValue (fieldStepOfStrictHeights h q hq) s := by
    have he : r + (1 : ℝ) • d = q := by dsimp only [d]; module
    simp only [f, he, constrainedHeightFieldValue, dite_eq_left hq]
  simpa only [he0, he1, Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh

end InvariantIsing

end

end OAI
