import OAI.InformationTheory.Entanglement.FiniteInputInstrument

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder MeasureTheory Kronecker ENNReal NNReal
open MeasureTheory Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {Ω : Type*} [MeasurableSpace Ω]
variable {n e d : Type} [Fintype n] [Fintype e] [Fintype d]
  [DecidableEq n] [DecidableEq e] [DecidableEq d]
namespace PositiveMatrixMeasure

omit [DecidableEq n] [DecidableEq e] [DecidableEq d] in
theorem filter_comp (W : PositiveMatrixMeasure Ω n) (B : Matrix e n ℂ)
    (C : Matrix d e ℂ) : (W.filter B).filter C=W.filter (C*B) := by
  apply ext_entry_default
  ext i j s hs
  change ((W.filter B).filter C).value s i j=(W.filter (C*B)).value s i j
  rw [filter_value,filter_value,filter_value,Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
end PositiveMatrixMeasure
namespace FiniteInputInstrument
variable (I : FiniteInputInstrument n Ω)

def normalizedProbe : PositiveMatrixMeasure Ω n :=
  I.rawProbe.filter (((Real.sqrt (Fintype.card n : ℝ) : ℂ)⁻¹) • (1 : Mat n))
omit [DecidableEq n] in
lemma sqrt_card_ne_zero [Nonempty n] : (Real.sqrt (Fintype.card n : ℝ) : ℂ)≠0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)).ne'
omit [DecidableEq n] in
lemma sqrt_card_mul : (Real.sqrt (Fintype.card n : ℝ) : ℂ)*
    (Real.sqrt (Fintype.card n : ℝ) : ℂ)=(Fintype.card n : ℂ) := by
  rw [← Complex.ofReal_mul,Real.mul_self_sqrt (by positivity),Complex.ofReal_natCast]

theorem normalizedProbe_value (s : Set Ω) :
    I.normalizedProbe.value s=(Fintype.card n : ℂ)⁻¹ • I.rawProbe.value s := by
  unfold normalizedProbe
  rw [PositiveMatrixMeasure.filter_value,Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one]
  simp only [map_inv₀,Complex.star_def,Complex.conj_ofReal,Matrix.smul_mul,
    Matrix.one_mul,Matrix.mul_smul,Matrix.mul_one,smul_smul]
  rw [← mul_inv,sqrt_card_mul]

omit [DecidableEq e] in
theorem normalizedProbe_filter [Nonempty n] (B : Matrix e n ℂ) :
    I.normalizedProbe.filter ((Real.sqrt (Fintype.card n : ℝ) : ℂ) • B)=
      I.purificationLaw B := by
  rw [purificationLaw_eq_filter]
  unfold normalizedProbe
  rw [PositiveMatrixMeasure.filter_comp]
  congr 1
  rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_one,smul_smul,
    mul_inv_cancel₀ sqrt_card_ne_zero,one_smul]
theorem normalizedProbe_trace [Nonempty n] :
    Matrix.trace (I.normalizedProbe.value Set.univ)=1 := by
  rw [normalizedProbe_value,rawProbe_total,Matrix.trace_smul,Matrix.trace_one]
  change (Fintype.card n : ℂ)⁻¹*(Fintype.card n : ℂ)=1
  exact inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos : 0<Fintype.card n).ne')
instance normalizedProbe_probability [Nonempty n] :
    IsProbabilityMeasure I.normalizedProbe.traceMeasure := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
  change I.normalizedProbe.traceMeasure.real Set.univ=(1 : ℝ≥0∞).toReal
  rw [PositiveMatrixMeasure.traceMeasure_real _ MeasurableSet.univ,I.normalizedProbe_trace]
  simp
end FiniteInputInstrument

lemma product_normalized_probe_amplitude {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] :
    (((Real.sqrt (Fintype.card a : ℝ) : ℂ)⁻¹ • (1 : Mat a)) ⊗ₖ
      ((Real.sqrt (Fintype.card b : ℝ) : ℂ)⁻¹ • (1 : Mat b)))=
      (Real.sqrt (Fintype.card (a×b) : ℝ) : ℂ)⁻¹ • (1 : Mat (a×b)) := by
  rw [Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,Matrix.one_kronecker_one,
    ← mul_inv,← Complex.ofReal_mul,← Real.sqrt_mul (by positivity)]
  simp only [Fintype.card_prod,Nat.cast_mul]

theorem normalized_product_probe_filter {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] [Nonempty a] [Nonempty b]
    (I : FiniteInputInstrument (a×b) Ω) (R : Mat (a×b)) :
    I.normalizedProbe.filter (canonicalProbeFilter R)=
      I.purificationLaw (CFC.sqrt R)ᵀ := by
  convert I.normalizedProbe_filter (CFC.sqrt R)ᵀ using 1
  simp only [canonicalProbeFilter,Fintype.card_prod,Nat.cast_mul]

end SecretKey

end

end OAI
