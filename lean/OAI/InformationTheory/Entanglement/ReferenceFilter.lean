import OAI.InformationTheory.Entanglement.MatrixTraceMeasure
import OAI.InformationTheory.Entanglement.ProbeMatrices

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder MeasureTheory Kronecker
open Matrix MeasureTheory
namespace SecretKey
open ChannelCompletion
variable {Ω : Type*} [MeasurableSpace Ω]
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
namespace PositiveMatrixMeasure
omit [Fintype m] [DecidableEq n] [DecidableEq m] in
lemma filter_entry_value (W : PositiveMatrixMeasure Ω n) (K : Matrix m n ℂ) (s : Set Ω) :
    (fun a b => (∑ i, ∑ j, (K a i*star (K b j)) • W.entry i j) s)=K*W.value s*Kᴴ := by
  ext a b
  simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Finset.sum_mul,value]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def filter (W : PositiveMatrixMeasure Ω n) (K : Matrix m n ℂ) : PositiveMatrixMeasure Ω m where
  entry a b := ∑ i, ∑ j, (K a i*star (K b j)) • W.entry i j
  positive s hs := by
    rw [filter_entry_value]
    exact (W.positive s hs).mul_mul_conjTranspose_same K
omit [DecidableEq n] [DecidableEq m] in
lemma filter_value (W : PositiveMatrixMeasure Ω n) (K : Matrix m n ℂ) (s : Set Ω) :
    (W.filter K).value s=K*W.value s*Kᴴ := filter_entry_value W K s
end PositiveMatrixMeasure
omit [Fintype m] [DecidableEq n] [DecidableEq m] in
lemma filter_density_integrable {μ : Measure Ω} {D : Ω → Mat n}
    (hD : ∀ a b, Integrable (fun x => D x a b) μ) (K : Matrix m n ℂ) (a b : m) :
    Integrable (fun x => (K*D x*Kᴴ) a b) μ := by
  simp only [Matrix.mul_apply,Finset.sum_mul]
  exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun i _ =>
    ((hD i j).const_mul _).mul_const _
omit [Fintype m] [DecidableEq n] [DecidableEq m] in
lemma filter_density_measurable {D : Ω → Mat n} (hD : Measurable D) (K : Matrix m n ℂ) :
    Measurable (fun x => K*D x*Kᴴ) := by
  have hc : Continuous (fun M : Mat n => K*M*Kᴴ) := by fun_prop
  exact hc.measurable.comp hD
omit [DecidableEq n] [DecidableEq m] in
lemma filter_setIntegral {μ : Measure Ω} (W : PositiveMatrixMeasure Ω n) (K : Matrix m n ℂ)
    (D : Ω → Mat n) (hD : ∀ a b, Integrable (fun x => D x a b) μ)
    (hs : ∀ s, MeasurableSet s → ∀ a b, (∫ x in s, D x a b ∂μ)=W.value s a b)
    {s : Set Ω} (hsm : MeasurableSet s) (a b : m) :
    (∫ x in s, (K*D x*Kᴴ) a b ∂μ)=(W.filter K).value s a b := by
  rw [PositiveMatrixMeasure.filter_value]
  simp only [Matrix.mul_apply,Finset.sum_mul]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const,integral_const_mul, hs s hsm]
    · intro i hi
      exact (((hD i j).const_mul _).mul_const _).integrableOn
  · intro j hj
    exact (integrable_finsetSum _ fun i _ => ((hD i j).const_mul _).mul_const _).integrableOn

def canonicalProbeFilter (R : Mat (n×m)) : Mat (n×m) :=
  (Real.sqrt ((Fintype.card n : ℝ)*Fintype.card m) : ℂ) • (CFC.sqrt R)ᵀ
lemma canonicalProbeFilter_hermitian (R : Mat (n×m)) :
    (canonicalProbeFilter R)ᴴ=canonicalProbeFilter R := by
  unfold canonicalProbeFilter
  rw [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal]
  exact congrArg (_ • ·) (sqrt_psd R).isHermitian.transpose.eq
lemma canonicalProbeFilter_product (R : Mat (n×m)) (U : Mat n) (V : Mat m) :
    canonicalProbeFilter R*(U ⊗ₖ V)*(canonicalProbeFilter R)ᴴ =
      eveBlock R (((Fintype.card n : ℂ) • Uᵀ) ⊗ₖ ((Fintype.card m : ℂ) • Vᵀ)) := by
  rw [canonicalProbeFilter_hermitian]
  unfold canonicalProbeFilter eveBlock
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [← Complex.ofReal_mul,Real.mul_self_sqrt (by positivity)]
  simp only [Complex.ofReal_mul,Complex.ofReal_natCast]
  rw [Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,Matrix.mul_smul,Matrix.smul_mul,
    Matrix.transpose_smul,Matrix.transpose_mul,Matrix.transpose_mul,Matrix.kroneckerMap_transpose,
    Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

end SecretKey

end

end OAI
