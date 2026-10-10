import OAI.NumberTheory.DirichletL.CubicSieve.FullNorm
import OAI.NumberTheory.DirichletL.CubicSieve.PairPoisson

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson FourierBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem cubic_radial_kernel_transfer (W : 𝓢(ℝ, ℂ)) (Lr Lc : ℝ)
    (hLr : 0 ≤ Lr) (hLc : 0 ≤ Lc) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M N : ℝ) (_hN : 0 ≤ N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ M)
        (_hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E)
        (x : m → ℝ) (y : n → ℝ) (_hx : ∀ i, |x i| ≤ Lr) (_hy : ∀ j, |y j| ≤ Lc),
        (1 + R) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (R * Real.exp (x i + (y j + y k)))‖) ≤
          C * (elementSieveNorm M N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, htransfer⟩ := QuadraticKernelTransfer.radial_matrix_kernel_transfer
    W Lr (2 * Lc) hLr (by positivity) A
  refine ⟨C, hC, ?_⟩
  intro R hR m n _ _ _ _ ε hε M N hN rows cols hr hc hrows hcols a b E hE ha hb x y hx hy
  let c : m → n × n → ℂ := fun i p => if IsCoprime (cols p.1) (cols p.2) then
    star (cubicRow (cols p.1) (rows i) * a p.1) *
      (cubicRow (cols p.2) (rows i) * b p.2) else 0
  let H := elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E
  have hfac : 0 ≤ elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) :=
    mul_nonneg (elementSieveNorm_nonneg _ _)
      (mul_nonneg (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le (Real.rpow_nonneg hN _))
  have hH : 0 ≤ H := mul_nonneg hfac hE
  have hyy (p : n × n) : |y p.1 + y p.2| ≤ 2 * Lc :=
    (abs_add_le _ _).trans (by linarith [hy p.1, hy p.2])
  have hphase (t : ℝ) : (∑ i, ‖∑ p : n × n, c i p * logPhase t (y p.1 + y p.2)‖) ≤ H := by
    let aTwist : n → ℂ := fun j => a j * star (logPhase t (y j))
    let bTwist : n → ℂ := fun j => b j * logPhase t (y j)
    have ha' : (∑ j, ‖aTwist j‖ ^ 2) ≤ E := by simpa only [aTwist, norm_mul, norm_star, logPhase_norm, mul_one] using ha
    have hb' : (∑ j, ‖bTwist j‖ ^ 2) ≤ E := by simpa only [bTwist, norm_mul, logPhase_norm, mul_one] using hb
    have he (i : m) : (∑ p : n × n, c i p * logPhase t (y p.1 + y p.2)) =
        ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
          star (cubicRow (cols j) (rows i) * aTwist j) *
            (cubicRow (cols k) (rows i) * bTwist k) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [c, aTwist, bTwist]
      split_ifs
      · rw [logPhase_add]
        simp only [star_mul, star_star]
        ring
      · simp only [zero_mul]
    simp_rw [he]
    have hbil := element_coprime_bilinear_bound ε hε M N hN rows cols hr hc hrows hcols aTwist bTwist
    apply (sq_le_sq₀ (by positivity) hH).mp
    apply hbil.trans
    calc
      _ ≤ (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) *
          (elementSieveNorm M N * (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) :=
        mul_le_mul (mul_le_mul_of_nonneg_left ha' hfac) (mul_le_mul_of_nonneg_left hb' hfac)
          (by positivity) hH
      _ = H ^ 2 := by ring
  have ht := htransfer R hR c x (fun p : n × n => y p.1 + y p.2) H hH hx hyy hphase
  simpa only [Fintype.sum_prod_type, c, H] using ht

end
end SevenEighths.CubicSieve

end OAI
