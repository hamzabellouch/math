import OAI.Probability.InvariantIsing.Haar.HaarPolynomialSpace
import OAI.Probability.InvariantIsing.Haar.HaarContinuousDerivative

namespace OAI

/-! Finite polynomial averaging kernels on the actual special orthogonal group. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory
open scoped BigOperators
namespace InvariantIsing

def haarKernelAtom {N : ℕ} (V : SpecialOrthogonal N) : Option (Fin N × Fin N) → ℝ
  | none => N
  | some ij => (V : Matrix (Fin N) (Fin N) ℝ) ij.1 ij.2

def haarKernelBase {N : ℕ} (U V : SpecialOrthogonal N) : ℝ :=
  N + ∑ i, ∑ j, (U : Matrix (Fin N) (Fin N) ℝ) i j *
    (V : Matrix (Fin N) (Fin N) ℝ) i j

def haarKernelAverage {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    (f : SpecialOrthogonal N → ℝ) (n : ℕ) : MatrixPolynomial N :=
  ∑ w : Fin n → Option (Fin N × Fin N),
    (∫ V, f V * ∏ k, haarKernelAtom V (w k) ∂μ) • haarPolynomialWord w

lemma continuous_haarKernelAtom {N : ℕ} (a : Option (Fin N × Fin N)) :
    Continuous (fun V : SpecialOrthogonal N => haarKernelAtom V a) := by
  cases a with
  | none => exact continuous_const
  | some ij =>
    exact (continuous_apply ij.2).comp
      ((continuous_apply ij.1).comp continuous_subtype_val)

lemma haarKernelBase_sum {N : ℕ} (U V : SpecialOrthogonal N) :
    haarKernelBase U V = ∑ a : Option (Fin N × Fin N),
      haarKernelAtom V a * haarPolynomialValue (haarPolynomialAtom a) U := by
  simp only [Fintype.sum_option,haarKernelAtom,haarPolynomialAtom,
    haarPolynomialValue,map_one,mul_one,matrixPolynomialEval_X,Fintype.sum_prod_type]
  unfold haarKernelBase
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem haarKernelAverage_value {N : ℕ} (μ : Measure (SpecialOrthogonal N))
    [IsFiniteMeasure μ] (f : SpecialOrthogonal N → ℝ) (hf : Continuous f)
    (n : ℕ) (U : SpecialOrthogonal N) :
    haarPolynomialValue (haarKernelAverage μ f n) U =
      ∫ V, f V * (haarKernelBase U V)^n ∂μ := by
  have hi (w : Fin n → Option (Fin N × Fin N)) :
      Integrable (fun V => f V * ∏ k, haarKernelAtom V (w k)) μ :=
    continuous_haar_integrable μ _ (hf.mul (continuous_finsetProd _ fun k _ =>
      continuous_haarKernelAtom (w k)))
  simp only [haarKernelAverage,haarPolynomialValue,map_sum,map_smul,
    smul_eq_mul,haarPolynomialWord,map_prod]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ (fun w _ => (hi w).mul_const _)]
  apply integral_congr_ae
  exact ae_of_all μ fun V => by
    change (∑ w : Fin n → Option (Fin N × Fin N),
      (f V * ∏ k, haarKernelAtom V (w k)) *
        ∏ k, matrixPolynomialEval (U : Matrix (Fin N) (Fin N) ℝ) (haarPolynomialAtom (w k))) =
      f V * haarKernelBase U V ^ n
    rw [haarKernelBase_sum,Fintype.sum_pow]
    simp only [Finset.mul_sum,Finset.prod_mul_distrib,mul_assoc]
    rfl

end InvariantIsing

end

end OAI
