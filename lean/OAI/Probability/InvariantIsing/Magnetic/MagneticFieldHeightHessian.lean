import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldHeightDerivative

namespace OAI

/-! The actual constrained finite-height Hessian.  Differentiating the
physical optimizing bias gives the scalar Schur-complement correction;
no twice-differentiable optimizer is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology BigOperators

namespace InvariantIsing

lemma hasDerivAt_constrainedHeightFieldValue_line_at (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (t : ℝ)
    (hr : r + t • d ∈ I) (hrs : r + t • d ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (fun q : ℝ => constrainedHeightFieldValue h s (r + q • d))
      ((∑ i, F.P i (r + t • d, magneticHeightBias h s (r + t • d)) * d i) -
        d (Fin.last h.depth) / 2) t := by
  have h0 := hasDerivAt_constrainedHeightFieldValue_line h F hI hU hs
    (r + t • d) d hr hrs
  have h0' : HasDerivAt (fun q : ℝ =>
      constrainedHeightFieldValue h s (r + t • d + q • d))
      ((∑ i, F.P i (r + t • d, magneticHeightBias h s (r + t • d)) * d i) -
        d (Fin.last h.depth) / 2) (id t - t) := by
    simpa only [id_eq, sub_self] using h0
  have hd := h0'.comp (h := fun q : ℝ => q - t) t ((hasDerivAt_id t).sub_const t)
  have he : (fun q : ℝ => constrainedHeightFieldValue h s
      (r + t • d + (q - t) • d)) =
      (fun q : ℝ => constrainedHeightFieldValue h s (r + q • d)) := by
    funext q
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [Function.comp_def, sub_self, mul_one, sub_zero, he] using hd

lemma hasDerivAt_magneticHeight_gradient (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (fun t : ℝ =>
      (∑ i, F.P i (r + t • d, magneticHeightBias h s (r + t • d)) * d i) -
        d (Fin.last h.depth) / 2)
      ((∑ i, ∑ j, F.PP i j (r, magneticHeightBias h s r) * d i * d j) -
        (∑ i, F.PX i (r, magneticHeightBias h s r) * d i) ^ 2 /
          F.XX (r, magneticHeightBias h s r)) 0 := by
  let b := fun t : ℝ => magneticHeightBias h s (r + t • d)
  let A := ∑ i, F.PX i (r, magneticHeightBias h s r) * d i
  let C := F.XX (r, magneticHeightBias h s r)
  have hb : HasDerivAt b (-A / C) 0 :=
    hasDerivAt_magneticHeightBias_line h F hI hU hs r d hr hrs
  have hp := ((hasDerivAt_const (0 : ℝ) r).add
    ((hasDerivAt_id (0 : ℝ)).smul_const d)).prodMk hb
  have hd (i : Fin (h.depth + 1)) :
      HasDerivAt (fun t => F.P i (r + t • d, b t) * d i)
        (((∑ j, F.PP i j (r, magneticHeightBias h s r) * d j) +
          F.PX i (r, magneticHeightBias h s r) * (-A / C)) * d i) 0 := by
    have hF := F.derivativeP i (r + (0 : ℝ) • d, b 0)
      (by simpa only [zero_smul, add_zero] using hr)
    have hh := (hF.comp_hasDerivAt (0 : ℝ) hp).mul_const (d i)
    simpa only [fieldFiniteLinear_apply, Pi.smul_apply, one_mul,
      b, zero_smul, add_zero, one_smul, zero_add, Function.comp_def, Pi.add_apply,
      id_eq] using hh
  have hsum := (HasDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hd i)).sub_const
    (d (Fin.last h.depth) / 2)
  convert hsum using 1
  · funext t
    simp only [Finset.sum_apply, b]
  · simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    have he : (∑ i, F.PX i (r, magneticHeightBias h s r) * (-A / C) * d i) =
        A * (-A / C) := by
      dsimp only [A]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he]
    have hpp : (∑ i, ∑ j, F.PP i j (r, magneticHeightBias h s r) * d j * d i) =
        ∑ i, ∑ j, F.PP i j (r, magneticHeightBias h s r) * d i * d j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hpp]
    dsimp only [A, C]
    ring

/-- The second height derivative is the Hessian at the physical bias minus
the rank-one correction from keeping the mean spin fixed. -/
lemma hasDerivAt_deriv_constrainedHeightFieldValue_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (deriv (fun t : ℝ => constrainedHeightFieldValue h s (r + t • d)))
      ((∑ i, ∑ j, F.PP i j (r, magneticHeightBias h s r) * d i * d j) -
        (∑ i, F.PX i (r, magneticHeightBias h s r) * d i) ^ 2 /
          F.XX (r, magneticHeightBias h s r)) 0 := by
  have hp : ContinuousAt (fun t : ℝ => r + t • d) 0 := by fun_prop
  have hn : ∀ᶠ t : ℝ in 𝓝 0, r + t • d ∈ I ∩ fieldStrictHeightCone h.depth :=
    hp.eventually ((hI.inter (isOpen_fieldStrictHeightCone _)).mem_nhds
      (by simpa only [zero_smul, add_zero, Set.mem_inter_iff] using And.intro hr hrs))
  apply (hasDerivAt_magneticHeight_gradient h F hI hU hs r d hr hrs).congr_of_eventuallyEq
  filter_upwards [hn] with t ht
  exact (hasDerivAt_constrainedHeightFieldValue_line_at h F hI hU hs r d t
    ht.1 ht.2).deriv

end InvariantIsing

end

end OAI
