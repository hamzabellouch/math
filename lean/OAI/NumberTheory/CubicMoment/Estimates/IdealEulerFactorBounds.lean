import OAI.NumberTheory.CubicMoment.Estimates.IdealEulerSeries

namespace OAI

/-! The finite Euler correction is entire and has an explicit norm bound
in the strip used by the angular prime zero-free argument. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma idealEulerFactor_differentiable (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) : Differentiable ℂ (idealEulerFactor S χ) := by
  unfold idealEulerFactor
  apply Differentiable.fun_finsetProd
  intro p _
  have hN : NeZero (idealExponentNorm (Finsupp.single p 1) : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr (idealExponentNorm_pos _).ne'⟩
  apply Differentiable.sub (differentiable_const (1:ℂ))
  apply Differentiable.mul (differentiable_const (χ (Finsupp.single p 1)))
  exact (differentiable_const_cpow_of_neZero _).comp differentiable_neg

lemma idealEulerFactor_norm_bound (S : Finset EisensteinIdealPrime)
    (χ : EisensteinIdealExponent → ℂ) (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {s : ℂ}
    (hs : -(3/2:ℝ) ≤ s.re) :
    ‖idealEulerFactor S χ s‖ ≤ (idealExponentNorm (primeSetExponent S))^3 := by
  have hsingle (p : EisensteinIdealPrime) :
      ‖1-χ (Finsupp.single p 1)*(idealExponentNorm (Finsupp.single p 1):ℂ)^(-s)‖ ≤
        (idealExponentNorm (Finsupp.single p 1))^3 := by
    let N := idealExponentNorm (Finsupp.single p 1)
    have hN : 2 ≤ N := by
      dsimp only [N]
      rw [idealExponentNorm_single,pow_one]
      exact_mod_cast idealPrimeRepresentative_normNat_ge_two p
    have hp : 0 < N := by linarith
    have he : N^(-s.re) ≤ N^(2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_two] at he
    calc
      _ ≤ 1+‖χ (Finsupp.single p 1)‖*N^(-s.re) := by
        simpa only [norm_one,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp,Complex.neg_re]
          using norm_sub_le (1:ℂ) (χ (Finsupp.single p 1)*(N:ℂ)^(-s))
      _ ≤ 1+N^2 := by
        have hh := mul_le_of_le_one_left (Real.rpow_nonneg hp.le (-s.re)) (hχ (Finsupp.single p 1))
        linarith
      _ ≤ N^3 := by nlinarith [sq_nonneg (N-1)]
  rw [idealEulerFactor,norm_prod]
  calc
    _ ≤ ∏ p ∈ S, (idealExponentNorm (Finsupp.single p 1))^3 :=
      Finset.prod_le_prod₀ (fun p _ => _root_.norm_nonneg _) (fun p _ => hsingle p)
    _ = _ := by rw [Finset.prod_pow,idealExponentNorm_primeSet]

end CubicFirstMoment

end

end OAI
