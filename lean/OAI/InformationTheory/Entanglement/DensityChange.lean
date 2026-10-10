import OAI.InformationTheory.Entanglement.MatrixTraceMeasure

namespace OAI

noncomputable section
open MeasureTheory Matrix
open scoped MeasureTheory BigOperators ComplexOrder MatrixOrder Kronecker
namespace SecretKey
open ChannelCompletion
variable {n : Type} [Fintype n] [DecidableEq n]
lemma traceNorm_smul_nonneg (c : ℝ) (hc : 0≤c) (A : Mat n) :
    traceNorm ((c : ℂ) • A)=c*traceNorm A := by
  obtain ⟨V,hV,he⟩ := MatrixPolar.polar A
  have hH : (CFC.sqrt (Aᴴ*A)).PosSemidef := sqrt_psd _
  have hcp : (((c : ℂ) • CFC.sqrt (Aᴴ*A))).PosSemidef :=
    hH.smul (by rw [Complex.nonneg_iff]; exact ⟨hc,rfl⟩)
  conv_lhs => rw [he,← Matrix.mul_smul,traceNorm_unitary_left _ hV,traceNorm_of_psd hcp]
  simp only [Matrix.trace_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl
lemma eveBlock_smul (c : ℂ) (R D : Mat n) : eveBlock R (c • D)=c • eveBlock R D := by
  simp only [eveBlock,Matrix.mul_smul,Matrix.smul_mul,Matrix.transpose_smul]
variable {Ω : Type*} [MeasurableSpace Ω]
variable (μ ν : Measure Ω)
def densityWeight (x : Ω) : ℝ := (μ.rnDeriv ν x).toReal
lemma densityWeight_nonneg (x : Ω) : 0≤densityWeight μ ν x := ENNReal.toReal_nonneg
lemma densityWeight_measurable : Measurable (densityWeight μ ν) :=
  (Measure.measurable_rnDeriv μ ν).ennreal_toReal
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
lemma densityWeight_integrable (hμν : μ≪ν) {f : Ω → E} (hf : Integrable f μ) :
    Integrable (fun x => densityWeight μ ν x • f x) ν := by
  rw [← Measure.withDensity_rnDeriv_eq μ ν hμν] at hf
  exact (integrable_withDensity_iff_integrable_smul' (Measure.measurable_rnDeriv μ ν)
    (Measure.rnDeriv_lt_top μ ν)).mp hf
lemma densityWeight_integral (hμν : μ≪ν) (f : Ω → E) :
    (∫ x, densityWeight μ ν x • f x ∂ν)=∫ x, f x ∂μ := by
  conv_rhs => rw [← Measure.withDensity_rnDeriv_eq μ ν hμν]
  exact (integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv μ ν)
    (Measure.rnDeriv_lt_top μ ν) f).symm
lemma densityWeight_setIntegral (hμν : μ≪ν) (f : Ω → E) {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x in s, densityWeight μ ν x • f x ∂ν)=∫ x in s, f x ∂μ := by
  conv_rhs => rw [← Measure.withDensity_rnDeriv_eq μ ν hμν]
  exact (setIntegral_withDensity_eq_setIntegral_toReal_smul (Measure.measurable_rnDeriv μ ν)
    (ae_restrict_of_ae (Measure.rnDeriv_lt_top μ ν)) f hs).symm

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
lemma densityWeight_eveBlock {m : Type} [Fintype m] [DecidableEq m]
    (R : Mat (n×m)) (X : Ω → Mat n) (Y : Ω → Mat m) (x : Ω) :
    (densityWeight μ ν x : ℂ) • eveBlock R (X x ⊗ₖ Y x)=
      eveBlock R (((densityWeight μ ν x : ℂ) • X x) ⊗ₖ Y x) := by
  rw [Matrix.smul_kronecker,eveBlock_smul]

lemma densityWeight_traceNorm_integral (hμν : μ≪ν) (D : Ω → Mat n) :
    (∫ x, traceNorm ((densityWeight μ ν x : ℂ) • D x) ∂ν)=∫ x, traceNorm (D x) ∂μ := by
  simp only [traceNorm_smul_nonneg _ (densityWeight_nonneg μ ν _)]
  exact densityWeight_integral μ ν hμν (fun x => traceNorm (D x))

end SecretKey

end

end OAI
