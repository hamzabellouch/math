import OAI.Probability.InvariantIsing.Magnetic.MagneticOffDiagonalHessian
import OAI.Probability.InvariantIsing.Fields.FieldHeightBox

namespace OAI

/-! A supporting plane for the actual finite constrained field on the
strict height cone. The optimizing bias is varied along the segment. -/

noncomputable section
open Set Filter
open scoped BigOperators

namespace InvariantIsing

private lemma magnetic_gradient_line_at (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (t : ℝ)
    (hr : r + t • d ∈ I) (hrs : r + t • d ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (fun q : ℝ =>
      (∑ i, F.P i (r + q • d, magneticHeightBias h s (r + q • d)) * d i) -
        d (Fin.last h.depth) / 2)
      (∑ i, ∑ j, magneticHeightSchur h F s (r + t • d) i j * d i * d j) t := by
  have hi (i : Fin (h.depth + 1)) :=
    (hasDerivAt_magneticHeightP_line h F hI hU hs (r + t • d) d hr hrs i).mul_const (d i)
  have hd := (HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hi i)).sub_const
    (d (Fin.last h.depth) / 2)
  have heq : (∑ i, (∑ j, magneticHeightSchur h F s (r + t • d) i j * d j) * d i) =
      ∑ i, ∑ j, magneticHeightSchur h F s (r + t • d) i j * d i * d j := by
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq] at hd
  have hd' : HasDerivAt (fun q : ℝ =>
      (∑ i, F.P i (r + t • d + q • d,
        magneticHeightBias h s (r + t • d + q • d)) * d i) - d (Fin.last h.depth) / 2)
      (∑ i, ∑ j, magneticHeightSchur h F s (r + t • d) i j * d i * d j) (t - t) := by
    simpa only [sub_self, Finset.sum_apply] using hd
  have hc := hd'.comp (h := fun q : ℝ => q - t) t ((hasDerivAt_id t).sub_const t)
  have hv (q : ℝ) : r + t • d + (q - t) • d = r + q • d := by module
  simpa only [Function.comp_def, hv, mul_one] using hc

theorem magneticHeight_support_strict (h : FieldStep) {m : ℝ} (hm : |m| < 1)
    (r q : Fin (h.depth + 1) → ℝ)
    (hr : r ∈ fieldStrictHeightCone h.depth) (hq : q ∈ fieldStrictHeightCone h.depth) :
    constrainedFieldValue (fieldStepOfStrictHeights h q hq) m ≤
      constrainedFieldValue (fieldStepOfStrictHeights h r hr) m +
        ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 *
          magneticFieldLevel (fieldStepOfStrictHeights h r hr) m i) * (q i - r i) := by
  classical
  obtain ⟨lo, V, hlo, hrI, hqI⟩ := fieldHeightBox_pair r q hr hq
  let I := fieldHeightBox h.depth lo V
  have hI : IsOpen I := isOpen_fieldHeightBox _ _ _
  obtain ⟨F, hF⟩ := fieldHeightBox_family h lo V hlo
  let d := q - r
  let f := fun t : ℝ => constrainedHeightFieldValue h m (r + t • d)
  let g := fun t : ℝ =>
    (∑ i, F.P i (r + t • d, magneticHeightBias h m (r + t • d)) * d i) -
      d (Fin.last h.depth) / 2
  let z := fun t : ℝ => ∑ i, ∑ j,
    magneticHeightSchur h F m (r + t • d) i j * d i * d j
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : r + t • d ∈ I := by
    have he : r + t • d = (1 - t) • r + t • q := by dsimp only [d]; module
    rw [he]
    exact convex_fieldHeightBox _ _ _ hrI hqI (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hstrict (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      r + t • d ∈ fieldStrictHeightCone h.depth :=
    fieldHeightBox_subset_strict hlo.le (hp t ht)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (g t) t :=
    hasDerivAt_constrainedHeightFieldValue_line_at h F hI hF hm r d t (hp t ht) (hstrict t ht)
  have hg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt g (z t) t :=
    magnetic_gradient_line_at h F hI hF hm r d t (hp t ht) (hstrict t ht)
  have hz (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : z t ≤ 0 :=
    magneticHeightSchur_quadratic_nonpos h F hI hF hm _ (hp t ht) (hstrict t ht) d
  have hanti : AntitoneOn g (Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hg t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hz t (interior_subset ht))
  have hbound : ∀ t ∈ interior (Icc (0 : ℝ) 1), deriv f t ≤ g 0 := by
    intro t ht
    rw [(hf t (interior_subset ht)).deriv]
    exact hanti (by simp) (interior_subset ht) (interior_subset ht).1
  have hsup := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hf t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    hbound 0 (by simp) 1 (by simp) zero_le_one
  let G : Fin (h.depth + 1) → ℝ := fun i =>
    -(h.cut i.succ - h.cut i.castSucc) / 2 *
      magneticFieldLevel (fieldStepOfStrictHeights h r hr) m i
  have hgrad (i : Fin (h.depth + 1)) :
      F.P i (r, magneticHeightBias h m r) =
        G i + (if i = Fin.last h.depth then (1 / 2 : ℝ) else 0) := by
    have he := magneticHeight_optimized_gradient h F hF hm r hrI hr i
    dsimp only [G]
    linarith
  have hsum : (∑ i, F.P i (r, magneticHeightBias h m r) * d i) =
      (∑ i, G i * d i) + d (Fin.last h.depth) / 2 := by
    simp_rw [hgrad, add_mul]
    rw [Finset.sum_add_distrib]
    congr 1
    simp [div_eq_mul_inv, mul_comm]
  have hg0 : g 0 = ∑ i, (-(h.cut i.succ - h.cut i.castSucc) / 2 *
      magneticFieldLevel (fieldStepOfStrictHeights h r hr) m i) * (q i - r i) := by
    simp only [g, zero_smul, add_zero]
    change (∑ i, F.P i (r, magneticHeightBias h m r) * d i) -
      d (Fin.last h.depth) / 2 = ∑ i, G i * (q i - r i)
    rw [hsum, add_sub_cancel_right]
    rfl
  have he0 : f 0 = constrainedFieldValue (fieldStepOfStrictHeights h r hr) m := by
    simp only [f, zero_smul, add_zero, constrainedHeightFieldValue, dite_eq_left hr]
  have he1 : f 1 = constrainedFieldValue (fieldStepOfStrictHeights h q hq) m := by
    have he : r + (1 : ℝ) • d = q := by dsimp only [d]; module
    simp only [f, he, constrainedHeightFieldValue, dite_eq_left hq]
  rw [he0, he1, hg0] at hsup
  linarith

end InvariantIsing

end

end OAI
