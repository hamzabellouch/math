import OAI.NumberTheory.DirichletL.Hecke.DeletionBounds

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDeletionDerivative
open HeckeFamily HeckeDeletionBounds

theorem factor_deriv {N : ℝ} (hN : 0 < N) (a s : ℂ) :
    deriv (EulerFactors.factor N a) s = a*(N : ℂ)^(-s)*Complex.log (N : ℂ) := by
  have h := (hasDerivAt_const s (1 : ℂ)).sub
    (((hasDerivAt_id s).neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))).const_mul a)
  have h' : HasDerivAt (EulerFactors.factor N a)
      (a*(N : ℂ)^(-s)*Complex.log (N : ℂ)) s := by
    convert h using 1
    · funext z
      rfl
    · dsimp
      ring
  exact h'.deriv

theorem factor_logDeriv_norm {σ N : ℝ} (hσ : 0 < σ) (hN : 2 ≤ N)
    {a s : ℂ} (ha : ‖a‖ ≤ 1) (hs : σ ≤ s.re) :
    ‖logDeriv (EulerFactors.factor N a) s‖ ≤ localBound σ * Real.log N := by
  have hn0 : 0 < N := by linarith
  have hl : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have ht := term_bound hσ hN ha hs
  have hδ : (2 : ℝ)^(-σ) ≤ 1 :=
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).le
  have hf := (factor_bounds hσ hN ha hs).2
  rw [logDeriv_apply, factor_deriv hn0, div_eq_mul_inv, norm_mul, norm_mul,
    ← Complex.ofReal_log hn0.le, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl]
  have hterm : ‖a*(N : ℂ)^(-s)‖ ≤ 1 := ht.trans hδ
  calc
    _ ≤ (1*Real.log N)*localBound σ := by gcongr
    _ = _ := by ring

theorem factors_logDeriv_norm (σ : ℝ) (hσ : 0 < σ) (M : Ideal O)
    (ψ : Character) {s : ℂ} (hs : σ ≤ s.re) :
    ‖logDeriv (HeckeFiniteDeletion.factors M ψ) s‖ ≤
      localBound σ * Real.log ((radical M).absNorm : ℝ) := by
  have hp0 (P : SmoothMobiusCorrection.PrimeIdeal) : 0 < (P.val.absNorm : ℝ) := by
    have h := SmoothMobiusCorrection.prime_norm_two_le P
    exact_mod_cast (by omega : 0 < P.val.absNorm)
  have hp2 (P : SmoothMobiusCorrection.PrimeIdeal) : 2 ≤ (P.val.absNorm : ℝ) := by
    exact_mod_cast SmoothMobiusCorrection.prime_norm_two_le P
  have he : logDeriv (HeckeFiniteDeletion.factors M ψ) s =
      ∑ P ∈ SmoothMobiusCorrection.primeSet M,
        logDeriv (EulerFactors.factor (P.val.absNorm : ℝ) (idealCoeff ψ P.val)) s := by
    apply logDeriv_fun_prod
    · intro P _
      exact EulerFactors.factor_ne_zero (by linarith [hp2 P]) (idealCoeff_norm_le_one ψ P.val)
        (hσ.trans_le hs)
    · intro P _
      exact EulerFactors.differentiable_factor (hp0 P) _ s
  rw [he]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ P ∈ SmoothMobiusCorrection.primeSet M, localBound σ*Real.log (P.val.absNorm : ℝ) := by
      apply Finset.sum_le_sum
      intro P _
      exact factor_logDeriv_norm hσ (hp2 P) (idealCoeff_norm_le_one ψ P.val) hs
    _ = localBound σ * Real.log ((radical M).absNorm : ℝ) := by
      rw [← Finset.mul_sum, ← Real.log_prod (fun P _ => (hp0 P).ne')]
      simp only [radical, SmoothMobiusCorrection.primeProduct, map_prod, Nat.cast_prod]

end SevenEighths.HeckeDeletionDerivative

end

end OAI
