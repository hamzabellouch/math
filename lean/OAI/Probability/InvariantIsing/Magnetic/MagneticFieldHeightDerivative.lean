import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldFamily

namespace OAI

/-! Actual height-direction envelope differentiation at fixed magnetization.
The bias response is obtained by implicit differentiation of the finite
physical mean, using its strictly positive curvature. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter Classical
open scoped Topology BigOperators

namespace InvariantIsing

lemma hasFDerivAt_field_line_restriction {n : ℕ} {U : FieldCovariate n → ℝ}
    {r d A : Fin n → ℝ} {b c : ℝ}
    (hU : HasFDerivAt U (fieldFiniteLinear A c) (r, b)) :
    HasFDerivAt (fun p : ℝ × ℝ => U (r + p.1 • d, p.2))
      (pairLinear (∑ i, A i * d i) c) (0, b) := by
  let L : (ℝ × ℝ) →L[ℝ] FieldCovariate n :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight d).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hm : HasFDerivAt (fun p : ℝ × ℝ => (r + p.1 • d, p.2)) L ((0 : ℝ), b) := by
    have hf : HasFDerivAt (fun p : ℝ × ℝ => p.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) ((0 : ℝ), b) := hasFDerivAt_fst
    have hs : HasFDerivAt (fun p : ℝ × ℝ => p.2)
        (ContinuousLinearMap.snd ℝ ℝ ℝ) ((0 : ℝ), b) := hasFDerivAt_snd
    simpa only [zero_add, L, Pi.add_apply] using
      (((hasFDerivAt_const r ((0 : ℝ), b)).add (hf.smul_const d)).prodMk hs)
  have hu : HasFDerivAt U (fieldFiniteLinear A c)
      ((fun p : ℝ × ℝ => (r + p.1 • d, p.2)) (0, b)) := by
    simpa only [zero_smul, add_zero] using hU
  have hd := hu.comp ((0 : ℝ), b) hm
  convert hd using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro p
    simp only [ContinuousLinearMap.comp_apply, L, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smulRight_apply, fieldFiniteLinear_apply, Pi.smul_apply,
      smul_eq_mul, pairLinear_apply]
    change (∑ i, A i * d i) * p.1 + c * p.2 =
      (∑ i, A i * (p.1 * d i)) + c * p.2
    rw [Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- An arbitrary strict height direction has the explicitly differentiated
physical optimizing bias. -/
lemma hasDerivAt_magneticHeightBias_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (fun t : ℝ => magneticHeightBias h s (r + t • d))
      (-(∑ i, F.PX i (r, magneticHeightBias h s r) * d i) /
        F.XX (r, magneticHeightBias h s r)) 0 := by
  let b := fun t : ℝ => magneticHeightBias h s (r + t • d)
  have hb := continuousAt_magneticHeightBias_line h F hI hU hs r d hr hrs
  have hpos := fieldFiniteFamily_curvature_pos h F hU r hr hrs (b 0)
  have hmean := hasFDerivAt_field_line_restriction (d := d) (F.derivativeX (r, b 0) hr)
  have hN : ∀ᶠ t : ℝ in 𝓝 0, r + t • d ∈ I ∩ fieldStrictHeightCone h.depth := by
    have hp : ContinuousAt (fun t : ℝ => r + t • d) 0 := by fun_prop
    exact hp.eventually ((hI.inter (isOpen_fieldStrictHeightCone _)).mem_nhds
      (by simpa only [zero_smul, add_zero, Set.mem_inter_iff] using And.intro hr hrs))
  have he : ∀ᶠ t : ℝ in 𝓝 0, F.X (r + t • d, b t) = s := by
    filter_upwards [hN] with t ht
    exact fieldFiniteFamily_magneticHeightBias h F hU hs _ ht.1 ht.2
  simpa only [b, zero_smul, add_zero] using
    parametric_bias_hasDerivAt hb hpos.ne' hmean he

/-- The centered constrained field value on the strict height cone. -/
def constrainedHeightFieldValue (h : FieldStep) (s : ℝ)
    (r : Fin (h.depth + 1) → ℝ) : ℝ :=
  if hrs : r ∈ fieldStrictHeightCone h.depth then
    constrainedFieldValue (fieldStepOfStrictHeights h r hrs) s else 0

lemma constrainedHeightFieldValue_eq (h : FieldStep) {s : ℝ} (hs : |s| < 1)
    (r : Fin (h.depth + 1) → ℝ) (hrs : r ∈ fieldStrictHeightCone h.depth) :
    constrainedHeightFieldValue h s r =
      fieldHeightJointValue h r (magneticHeightBias h s r) - magneticHeightBias h s r * s := by
  rw [constrainedHeightFieldValue, dite_eq_left hrs,
    constrainedFieldValue_magneticBias _ hs, magneticHeightBias_eq h s r hrs,
    fieldHeightJointValue_strict h r hrs]

lemma hasDerivAt_constrainedHeightFieldValue_line (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hI : IsOpen I) (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (hs : |s| < 1) (r d : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) :
    HasDerivAt (fun t : ℝ => constrainedHeightFieldValue h s (r + t • d))
      ((∑ i, F.P i (r, magneticHeightBias h s r) * d i) - d (Fin.last h.depth) / 2) 0 := by
  let b := fun t : ℝ => magneticHeightBias h s (r + t • d)
  have hdb := hasDerivAt_magneticHeightBias_line h F hI hU hs r d hr hrs
  have hp := ((hasDerivAt_const (0 : ℝ) r).add
    ((hasDerivAt_id (0 : ℝ)).smul_const d)).prodMk hdb
  have hF := F.derivative (r + (0 : ℝ) • d, b 0)
    (by simpa only [zero_smul, add_zero] using hr)
  have hd := hF.comp_hasDerivAt (0 : ℝ) hp
  have hemean : F.X (r, b 0) = s := by
    simpa only [b, zero_smul, add_zero] using
      fieldFiniteFamily_magneticHeightBias h F hU hs r hr hrs
  have hemean' : F.X (r, magneticHeightBias h s r) = s := by
    simpa only [b, zero_smul, add_zero] using hemean
  have hcenter : HasDerivAt (fun t : ℝ => (r + t • d) (Fin.last h.depth) / 2)
      (d (Fin.last h.depth) / 2) 0 := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, id_eq] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (d (Fin.last h.depth))).const_add
        (r (Fin.last h.depth))).div_const 2
  have hdf := (hd.sub hcenter).sub (hdb.mul_const s)
  have hvalue : (fun t : ℝ => F.U (r + t • d, b t) -
      (r + t • d) (Fin.last h.depth) / 2 - b t * s) =ᶠ[𝓝 (0 : ℝ)]
      (fun t => constrainedHeightFieldValue h s (r + t • d)) := by
    have hp : ContinuousAt (fun t : ℝ => r + t • d) 0 := by fun_prop
    filter_upwards [hp.eventually ((isOpen_fieldStrictHeightCone _).mem_nhds
      (by simpa only [zero_smul, add_zero] using hrs))] with t ht
    rw [constrainedHeightFieldValue_eq h hs _ ht, fieldHeightJointValue, ← hU]
  convert hdf.congr_of_eventuallyEq hvalue.symm using 1
  simp only [zero_smul, add_zero, zero_add, one_smul, fieldFiniteLinear_apply, b, hemean']
  ring

end InvariantIsing

end

end OAI
