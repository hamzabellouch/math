import OAI.NumberTheory.DirichletL.CubicSieve.DualShell

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

@[simp] lemma cubicRow_one (z : O) : cubicRow 1 z = 1 := by
  simp only [cubicRow, CubicJacobiGlobal.idealSymbol_one, map_one]

theorem cubicDualRow_zero_bound {n : Type*} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hinj : Function.Injective cols) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M N : ℝ)
    (hN : 0 < N) (hcols : ∀ j, N/2 ≤ (Ideal.absNorm (cols j) : ℝ)) :
    ‖cubicDualRow cols hc a W M 0‖ ≤
      ((2/N) * ∑ j, ‖a j‖^2) * ‖paperRadialFourier W 0‖ := by
  by_cases hu : ∃ j, cols j = 1
  · obtain ⟨j₀, hj₀⟩ := hu
    have ho (j : n) (hj : j ≠ j₀) : cols j ≠ 1 := by
      intro he
      exact hj (hinj (he.trans hj₀.symm))
    have he : cubicDualRow cols hc a W M 0 =
        (star (cubicDualCoefficient cols hc a j₀) * cubicDualCoefficient cols hc a j₀) *
          paperRadialFourier W 0 := by
      rw [cubicDualRow_eq_gram]
      rw [Finset.sum_eq_single j₀]
      · rw [Finset.sum_eq_single j₀]
        · simp only [hj₀, cubicRow_one, one_mul, Ideal.span_singleton_zero,
            Ideal.absNorm_bot, Nat.cast_zero, mul_zero, zero_div, ite_eq_left isCoprime_one_left]
        · intro k hk hkj
          rw [cubicRow_zero_of_ne_one _ (hc k) (ho k hkj)]
          simp
        · simp
      · intro j hj hjj
        rw [cubicRow_zero_of_ne_one _ (hc j) (ho j hjj)]
        simp
      · simp
    rw [he, norm_mul, norm_mul, norm_star, ← pow_two]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (Finset.single_le_sum (fun j hj => sq_nonneg ‖cubicDualCoefficient cols hc a j‖)
      (Finset.mem_univ j₀)).trans (cubicDualCoefficient_energy cols hc a N hN hcols)
  · have hz : ∀ j, cols j ≠ 1 := fun j hj => hu ⟨j,hj⟩
    rw [cubicDualRow_zero cols hc hz a W M, norm_zero]
    positivity

end
end SevenEighths.CubicSieve

end OAI
