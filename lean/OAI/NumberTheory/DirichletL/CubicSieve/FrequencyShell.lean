import OAI.NumberTheory.DirichletL.CubicSieve.KernelTransfer

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson FourierBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma log_shell_ratio (K q : ℝ) (hK : 0 < K) (hq : K / 2 ≤ q ∧ q ≤ K) :
    |Real.log (q / K)| ≤ 4 := by
  apply CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hK).mpr
    linarith [hq.1]
  · apply (div_le_iff₀ hK).mpr
    linarith [hq.2]

lemma log_inverse_shell_ratio (N q : ℝ) (hN : 0 < N) (hq : N / 2 ≤ q ∧ q ≤ N) :
    |Real.log (N / q)| ≤ 4 := by
  have hq0 : 0 < q := by linarith [hq.1]
  apply CanonicalQuadraticSieve.middleRatio_log_bound
  constructor
  · apply (le_div_iff₀ hq0).mpr
    linarith [hq.2]
  · apply (div_le_iff₀ hq0).mpr
    linarith [hq.1]

lemma radial_product_log_identity (M K N q u v : ℝ)
    (hK : 0 < K) (hN : 0 < N) (hq : 0 < q) (hu : 0 < u) (hv : 0 < v) :
    (M * K / N ^ 2) * Real.exp (Real.log (q / K) + (Real.log (N / u) + Real.log (N / v))) =
      M * q / (u * v) := by
  rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hq hK),
    Real.exp_log (div_pos hN hu), Real.exp_log (div_pos hN hv)]
  field_simp

theorem cubic_frequency_shell_bound (W : 𝓢(ℝ, ℂ)) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0 < ε) (M K N : ℝ) (_hM : 0 < M) (_hK : 0 < K) (_hN : 0 < N)
        (rows : m → O) (cols : n → Ideal O)
        (_hr : Function.Injective rows) (_hc : Function.Injective cols)
        (_hrows : ∀ i, K / 2 ≤ (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ∧
          (Ideal.absNorm (Ideal.span {rows i}) : ℝ) ≤ K)
        (_hcols : ∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧
          (Ideal.absNorm (cols j) : ℝ) ≤ N)
        (a b : n → ℂ) (E : ℝ) (_hE : 0 ≤ E)
        (_ha : (∑ j, ‖a j‖ ^ 2) ≤ E) (_hb : (∑ j, ‖b j‖ ^ 2) ≤ E),
        (1 + M * K / N ^ 2) ^ A *
          (∑ i, ‖∑ j, ∑ k, (if IsCoprime (cols j) (cols k) then
            star (cubicRow (cols j) (rows i) * a j) *
              (cubicRow (cols k) (rows i) * b k) else 0) *
            paperRadialFourier W (M * (Ideal.absNorm (Ideal.span {rows i}) : ℝ) /
              ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)))‖) ≤
          C * (elementSieveNorm K N *
            (IdealCoprimeSieveOperator.supportConstant ε hε * N ^ ε) * E) := by
  obtain ⟨C, hC, ht⟩ := cubic_radial_kernel_transfer W 4 4 (by norm_num) (by norm_num) A
  refine ⟨C, hC, ?_⟩
  intro m n _ _ _ _ ε hε M K N hM hK hN rows cols hr hc hrows hcols a b E hE ha hb
  have hq (i : m) : 0 < (Ideal.absNorm (Ideal.span {rows i}) : ℝ) := by linarith [(hrows i).1]
  have hn (j : n) : 0 < (Ideal.absNorm (cols j) : ℝ) := by linarith [(hcols j).2.1]
  have hr0 (i : m) : rows i ≠ 0 := by
    intro hz
    simpa [hz] using hq i
  have hp := ht (M * K / N ^ 2) (by positivity) ε hε K N hN.le rows cols hr hc
    (fun i => ⟨hr0 i, (hrows i).2⟩) (fun j => ⟨(hcols j).1, (hcols j).2.2⟩)
    a b E hE ha hb
    (fun i => Real.log ((Ideal.absNorm (Ideal.span {rows i}) : ℝ) / K))
    (fun j => Real.log (N / (Ideal.absNorm (cols j) : ℝ)))
    (fun i => log_shell_ratio K _ hK (hrows i))
    (fun j => log_inverse_shell_ratio N _ hN (hcols j).2)
  simp_rw [radial_product_log_identity M K N _ _ _ hK hN (hq _) (hn _) (hn _)] at hp
  exact hp

end
end SevenEighths.CubicSieve

end OAI
