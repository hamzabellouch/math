import OAI.Probability.SignedSweeps.BaseCases

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma power_on_eigenvector {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : E →ₗ[ℂ] E) {x : E} {c : ℂ} (hx : T x = c • x) (r : ℕ) :
    (T ^ r) x = c ^ r • x := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

lemma trace_power_spectral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (r : ℕ) :
    (LinearMap.trace ℂ E (T ^ r)).re =
      ∑ i : Fin (finrank ℂ E), hT.eigenvalues rfl i ^ r := by
  classical
  rw [LinearMap.trace_eq_sum_inner _ (hT.eigenvectorBasis rfl), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [power_on_eigenvector T (hT.apply_eigenvectorBasis rfl i), inner_smul_right,
    inner_self_eq_norm_sq_to_K]
  simp only [RCLike.ofReal_eq_complex_ofReal, OrthonormalBasis.norm_eq_one, Complex.ofReal_one, one_pow, mul_one,
    ← Complex.ofReal_pow, Complex.ofReal_re]

lemma positive_contraction_eigenvalue_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (hc : ∀ x, ‖T x‖ ≤ ‖x‖) (i : Fin (finrank ℂ E)) :
    0 ≤ hT.isSymmetric.eigenvalues rfl i ∧ hT.isSymmetric.eigenvalues rfl i ≤ 1 := by
  have hnonneg := hT.nonneg_eigenvalues rfl i
  refine ⟨hnonneg, ?_⟩
  have hb := hc (hT.isSymmetric.eigenvectorBasis rfl i)
  simpa only [hT.isSymmetric.apply_eigenvectorBasis, norm_smul,
    OrthonormalBasis.norm_eq_one, mul_one, RCLike.norm_ofReal,
    Real.norm_eq_abs, abs_of_nonneg hnonneg] using hb

lemma trace_power_antitone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (T : E →ₗ[ℂ] E) (hT : T.IsPositive)
    (hc : ∀ x, ‖T x‖ ≤ ‖x‖) :
    Antitone (fun r : ℕ => (LinearMap.trace ℂ E (T ^ r)).re) := by
  intro r t hrt
  change (LinearMap.trace ℂ E (T ^ t)).re ≤ (LinearMap.trace ℂ E (T ^ r)).re
  rw [trace_power_spectral T hT.isSymmetric t, trace_power_spectral T hT.isSymmetric r]
  apply Finset.sum_le_sum
  intro i hi
  obtain ⟨hn, hu⟩ := positive_contraction_eigenvalue_bounds T hT hc i
  exact pow_le_pow_of_le_one hn hu hrt

lemma weightedMoment_antitone {d : ℕ} (lam : Partition (2 ^ d)) :
    Antitone (weightedMoment lam) := by
  intro r t hrt
  exact mul_le_mul_of_nonneg_left
    (trace_power_antitone _ (sweepSquare_positive lam) (sweepSquare_contraction lam) hrt)
    (Nat.cast_nonneg _)

lemma moment_bound_of_le_one {d : ℕ} (hd : 1 ≤ d) (lam : Partition (2 ^ d))
    (r : ℕ) (hr : weightedMoment lam r ≤ 1)
    {u v : ℕ} (α : Partition u) (β : Partition v) {η : ℝ} (hη : 0 ≤ η)
    (κ : ℝ) (l : ℕ) :
    logMoment (weightedMoment lam r) ≤
      ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by
  rw [logMoment_le_iff (weightedMoment_nonneg lam r)]
  apply hr.trans
  apply Real.one_le_exp
  exact add_nonneg (mul_nonneg (coefficient_nonneg hη hd) (signedEntropy_nonneg α β))
    (remainderBudget_nonneg κ d l)

lemma finite_depth_signed_moment_bound (d₀ : ℕ) {η : ℝ} (hη : 0 ≤ η) (κ : ℝ) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r ≥ r₀, ∀ d, 1 ≤ d → d ≤ d₀ →
      ∀ lam : Partition (2 ^ d),
        ∀ (u v l : ℕ) (h : u + v + l = 2 ^ d)
          (α : Partition u) (β : Partition v) (γ : Partition l),
          SignedOccurrence h α β γ lam →
            logMoment (weightedMoment lam r) ≤
              ((coefficient η d * signedEntropy α β + remainderBudget κ d l : ℝ) : EReal) := by
  obtain ⟨r₀, hr₀, hrange⟩ := finite_base_moments d₀
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr d hd hd₀ lam u v l h α β γ hocc
  exact moment_bound_of_le_one hd lam r (hrange r hr d hd₀ lam) α β hη κ l

end SignedSweeps
end

end OAI
