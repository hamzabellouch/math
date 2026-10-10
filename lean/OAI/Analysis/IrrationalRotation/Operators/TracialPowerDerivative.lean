import OAI.Analysis.IrrationalRotation.Model.Spectral

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233
namespace TracialState

variable {A : Type*} [CStarAlgebra A]

theorem power_derivative_term (τ : TracialState A) (a b : A) (n i : ℕ)
    (hi : i < n) :
    τ (a ^ (n.pred - i) * b * a ^ i) = τ (b * a ^ n.pred) := by
  rw [mul_assoc, τ.tracial, mul_assoc, ← pow_add]
  have hi' : i + (n.pred - i) = n.pred := by
    simp only [Nat.pred_eq_sub_one]
    omega
  rw [hi']

theorem power_derivative_sum (τ : TracialState A) (a b : A) (n : ℕ) :
    τ (∑ i ∈ Finset.range n, a ^ (n.pred - i) * b * a ^ i) =
      (n : ℂ) * τ (b * a ^ n.pred) := by
  rw [map_sum]
  have hterms : ∀ i ∈ Finset.range n,
      τ.toContinuousLinearMap (a ^ (n.pred - i) * b * a ^ i) =
        τ (b * a ^ n.pred) := by
    intro i hi
    exact τ.power_derivative_term a b n i (Finset.mem_range.mp hi)
  rw [Finset.sum_congr rfl hterms]
  simp [nsmul_eq_mul]

theorem hasDerivAt_power (τ : TracialState A) {f : ℝ → A} {f' : A} {t : ℝ}
    (hf : HasDerivAt f f' t) (n : ℕ) :
    HasDerivAt (fun s => τ (f s ^ n))
      ((n : ℂ) * τ (f' * f t ^ n.pred)) t := by
  have h := (τ.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hf.fun_pow' n)
  change HasDerivAt (fun s => τ (f s ^ n))
    (τ (∑ i ∈ Finset.range n, f t ^ (n.pred - i) * f' * f t ^ i)) t at h
  rw [τ.power_derivative_sum] at h
  exact h

theorem hasDerivAt_re_power (τ : TracialState A) {f : ℝ → A} {f' : A} {t : ℝ}
    (hf : HasDerivAt f f' t) (n : ℕ) :
    HasDerivAt (fun s => (τ (f s ^ n)).re)
      ((n : ℝ) * (τ (f' * f t ^ n.pred)).re) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (τ.hasDerivAt_power hf n)
  simpa [Function.comp_def, Complex.mul_re] using h

theorem hasDerivAt_logarithmic_power (τ : TracialState A)
    {f : ℝ → A} {f' : A} {t : ℝ} (hf : HasDerivAt f f' t) (n : ℕ) :
    HasDerivAt (fun s => ((n + 1 : ℝ)⁻¹) • τ (f s ^ (n + 1)))
      (τ (f' * f t ^ n)) t := by
  have h := (τ.hasDerivAt_power hf (n + 1)).const_smul ((n + 1 : ℝ)⁻¹)
  change HasDerivAt (fun s => ((n + 1 : ℝ)⁻¹) • τ (f s ^ (n + 1))) _ t at h
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simpa [Pi.smul_apply, Nat.pred_succ, Complex.real_smul, Complex.ofReal_inv,
    mul_assoc, ← mul_assoc, hn] using h

theorem hasDerivAt_logarithmic_partialSum (τ : TracialState A)
    {f : ℝ → A} {f' : A} {t : ℝ} (hf : HasDerivAt f f' t) (N : ℕ) :
    HasDerivAt (fun s => ∑ n ∈ Finset.range N,
      ((n + 1 : ℝ)⁻¹) • τ (f s ^ (n + 1)))
      (∑ n ∈ Finset.range N, τ (f' * f t ^ n)) t := by
  exact HasDerivAt.fun_sum (fun n _ => τ.hasDerivAt_logarithmic_power hf n)

end TracialState
end Invariant233

end

end OAI
