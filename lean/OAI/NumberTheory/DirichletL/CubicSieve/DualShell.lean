import OAI.NumberTheory.DirichletL.CubicSieve.DualCoefficients

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma cubicDualRow_zero {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hc : ∀ j, Admissible (cols j))
    (hunit : ∀ j, cols j ≠ 1) (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) :
    cubicDualRow cols hc a W M 0 = 0 := by
  unfold cubicDualRow
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro k hk
  rw [cubicRow_zero_of_ne_one _ (hc j) (hunit j)]
  simp

theorem cubic_dual_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N) (a : n → ℂ),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖cubicDualRow cols (fun j => (hcols j).1) a W M (rows i)‖) ≤
          C * (elementSieveNorm K N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) *
              ((2 / N) * ∑ j, ‖a j‖ ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := cubic_frequency_shell_bound W A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a
  have he := cubicDualCoefficient_energy cols (fun j => (hcols j).1) a N hN
    (fun j => (hcols j).2.1)
  have h := hb ε hε M K N hM hK hN rows cols hr hc hrows hcols
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    (cubicDualCoefficient cols (fun j => (hcols j).1) a)
    ((2 / N) * ∑ j, ‖a j‖ ^ 2) (by positivity) he he
  simpa only [cubicDualRow_eq_gram] using h

end
end SevenEighths.CubicSieve

end OAI
