import OAI.Probability.InvariantIsing.Cavity.CavityScalarRecursion

namespace OAI

/-! The root-averaged scalar spin recursion occurring after the cavity
quadratic change of measure, in the manuscript's field normalization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

def cavityScalarCascadeMean (N n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (root residual : ℝ≥0) (c : ℝ) : ℝ :=
  ∫ z : Fin N → ℝ, cascadeRecursion n b (fun i => vectorGaussianLaw N (v i))
    (fun _ p => p.1 + p.2) (cavityResidualSpinLog N residual c) z
      ∂(vectorGaussianLaw N root : Measure (Fin N → ℝ))

theorem cavityScalarCascadeMean_normalized (N : ℕ) (hN : 0 < N)
    (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : CascadeExponents n b)
    (root residual : ℝ≥0) (c : ℝ) (U : Rotation N) :
    (N : ℝ)⁻¹ * cavityScalarCascadeMean N n b v root residual c =
      rotatedEnrichedPressure n b v root (fun _ => 0) U (fun _ => 0) + (c + residual) / 2 := by
  have ht : rotatedFieldTerminal (fun _ : Fin N => 0) U (fun _ => 0) =
      (fun y => ∑ i, Real.log (Real.cosh (y i))) := by
    funext y
    simp only [rotatedFieldTerminal, rotatedEnergy_constant, zero_mul, zero_div, zero_add]
    change logPartition (fieldEnergy ((0 : Fin N → ℝ) + y)) = _
    simpa only [zero_add] using logPartition_fieldEnergy y
  have he (z : Fin N → ℝ) :
      cascadeRecursion n b (fun i => vectorGaussianLaw N (v i)) (fun _ p => p.1 + p.2)
        (cavityResidualSpinLog N residual c) z =
        (N : ℝ) * (c + residual) / 2 +
          rotatedCascadeValue n b v (fun _ => 0) U (fun _ => 0) z := by
    rw [cavityResidualSpinLog_recursion N hN n b v (fun i hi => (hb.1 i hi).1),
      rotatedCascadeValue, ht]
    congr 1
    simpa only [zero_add] using
      (vectorCascade_logCosh_sum N n b v (fun i hi => (hb.1 i hi).1) (fun _ => 0) z).symm
  have hi := integrable_rotatedCascadeValue hN n b v hb (fun _ => 0) U (fun _ => 0) root
  unfold cavityScalarCascadeMean
  simp_rw [he]
  rw [integral_add (integrable_const _) hi, integral_const]
  simp only [probReal_univ, one_smul]
  unfold rotatedEnrichedPressure
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp [hn]
  ring

/-- The scalar part in `cav:before-parts`, with the root interval and
ordinary residual both included. -/
theorem cavityScalarCascadeMean_fieldStep (N : ℕ) (hN : 0 < N)
    (h : FieldStep) (residual : ℝ≥0) (c : ℝ) (U : Rotation N) :
    (N : ℝ)⁻¹ * cavityScalarCascadeMean N h.depth (chainExponent h.cut)
      (fieldCascadeVariance h) (NNReal.mk (h.height 0) (h.nonneg 0)) residual c =
      fieldValue h 0 + h.height (Fin.last h.depth) / 2 + (c + residual) / 2 := by
  rw [cavityScalarCascadeMean_normalized N hN h.depth (chainExponent h.cut)
    (fieldCascadeVariance h) (chainExponent_admissible h.ordered_cut h.first h.last)
    (NNReal.mk (h.height 0) (h.nonneg 0)) residual c U]
  have he := rotatedEnrichedPressure_field_zero_time hN h U
  linarith

/-- A residual variance equal to the gap from the final common-level
variance to the diagonal removes that final height from the normalized
spin contribution. -/
theorem cavityScalarCascadeMean_diagonal (N : ℕ) (hN : 0 < N)
    (h : FieldStep) (diagonal : ℝ) (hd : h.height (Fin.last h.depth) ≤ diagonal)
    (c : ℝ) (U : Rotation N) :
    (N : ℝ)⁻¹ * cavityScalarCascadeMean N h.depth (chainExponent h.cut)
      (fieldCascadeVariance h) (NNReal.mk (h.height 0) (h.nonneg 0))
      (NNReal.mk (diagonal - h.height (Fin.last h.depth)) (sub_nonneg.mpr hd)) c =
      fieldValue h 0 + (c + diagonal) / 2 := by
  rw [cavityScalarCascadeMean_fieldStep N hN h _ c U]
  simp only [NNReal.coe_mk]
  ring

end InvariantIsing

end

end OAI
