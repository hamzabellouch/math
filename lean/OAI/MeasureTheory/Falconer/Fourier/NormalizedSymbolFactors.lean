import OAI.MeasureTheory.Falconer.Fourier.SymbolProductBounds
import OAI.MeasureTheory.Falconer.Recursion.DescriptorMaskSymmetry

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

noncomputable def symbolDerivativeConstant (B : ℕ) : ℝ :=
  1 + ∑ n ∈ Finset.range (B+1), (100:ℝ)^n * angleDerivativeConstant n

theorem symbolDerivativeConstant_one_le (B : ℕ) : 1 ≤ symbolDerivativeConstant B := by
  have : 0 ≤ ∑ n ∈ Finset.range (B+1), (100:ℝ)^n * angleDerivativeConstant n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (angleDerivativeConstant_nonneg n)
  unfold symbolDerivativeConstant
  linarith

theorem symbolDerivativeConstant_dominates {B n : ℕ} (hn : n ≤ B) :
    (100:ℝ)^n * angleDerivativeConstant n ≤ symbolDerivativeConstant B := by
  have h := Finset.single_le_sum
    (fun i (_ : i ∈ Finset.range (B+1)) =>
      mul_nonneg (by positivity : 0 ≤ (100:ℝ)^i) (angleDerivativeConstant_nonneg i))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))
  unfold symbolDerivativeConstant
  linarith

theorem iteratedDeriv_shift (f : ℝ → ℝ) (j k : ℕ) :
    iteratedDeriv j (iteratedDeriv k f) = iteratedDeriv (j+k) f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ,ih,Nat.succ_add,iteratedDeriv_succ]

theorem smooth_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

noncomputable def normalizedMaskFactor (w : ℝ → ℝ) (d : ℝ) (k : ℕ) : ℝ → ℝ :=
  fun θ => d^k * iteratedDeriv k w θ

 theorem normalizedMaskFactor_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (d : ℝ) (k : ℕ) : ContDiff ℝ ∞ (normalizedMaskFactor w d k) :=
  contDiff_const.mul (smooth_iteratedDeriv hw k)

 theorem normalizedMaskFactor_support (w : ℝ → ℝ) (d : ℝ) (k : ℕ) :
    tsupport (normalizedMaskFactor w d k) ⊆ tsupport w :=
  tsupport_mul_subset_right.trans (iteratedDeriv_tsupport k)

 theorem normalizedMaskFactor_derivative_bound {w : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hzero : ∀ θ, ‖w θ‖ ≤ 1)
    (hall : ∀ n θ, ‖iteratedDeriv n w θ‖ ≤
      ((100:ℝ)^n*angleDerivativeConstant n)*(d⁻¹)^n)
    {B k j : ℕ} (hkj : k+j ≤ B) (θ : ℝ) :
    ‖iteratedDeriv j (normalizedMaskFactor w d k) θ‖ ≤
      (symbolDerivativeConstant B)^k * (symbolDerivativeConstant B*d⁻¹)^j := by
  have hA := symbolDerivativeConstant_one_le B
  have hA0 : 0 ≤ symbolDerivativeConstant B := le_trans zero_le_one hA
  unfold normalizedMaskFactor
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_shift]
  simp only [norm_mul, Real.norm_eq_abs, abs_pow, abs_of_pos hd]
  by_cases hz : j+k = 0
  · have hj : j = 0 := by omega
    have hk : k = 0 := by omega
    subst j; subst k
    simpa only [Nat.zero_add,pow_zero,one_mul,mul_one,iteratedDeriv_zero,Real.norm_eq_abs] using hzero θ
  · have hbudget : j+k ≤ B := by omega
    have hC : (100:ℝ)^(j+k)*angleDerivativeConstant (j+k) ≤
        symbolDerivativeConstant B^(j+k) := by
      apply (symbolDerivativeConstant_dominates hbudget).trans
      exact le_self_pow₀ hA (by omega)
    calc
      _ ≤ d^k * (((100:ℝ)^(j+k)*angleDerivativeConstant (j+k))*(d⁻¹)^(j+k)) :=
        mul_le_mul_of_nonneg_left (hall (j+k) θ) (by positivity)
      _ ≤ d^k * (symbolDerivativeConstant B^(j+k)*(d⁻¹)^(j+k)) := by gcongr
      _ = _ := by
        rw [pow_add,pow_add,mul_pow]
        have he : d^k*(d⁻¹)^k = 1 := by rw [← mul_pow,mul_inv_cancel₀ hd.ne',one_pow]
        calc
          _ = (d^k*(d⁻¹)^k) * (symbolDerivativeConstant B)^k *
              (symbolDerivativeConstant B)^j * (d⁻¹)^j := by ring
          _ = _ := by rw [he]; ring

end PlanarFalconer

end OAI
