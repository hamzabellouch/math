import OAI.NumberTheory.Ostmann.Construction.GiantDiscreteTransport

namespace OAI

/-! # Measure transport for the concrete bounded moving kernel -/

namespace Ostmann
open MeasureTheory
open scoped Classical SchwartzMap

theorem measurable_exp_pair_mul (K : ℝ → ℝ → ℂ)
    (hK : Measurable (Function.uncurry K)) (c : ℂ) :
    Measurable (Function.uncurry (fun x y => c * K (Real.exp x) (Real.exp y))) := by
  have he : Measurable (fun z : ℝ × ℝ => (Real.exp z.1, Real.exp z.2)) :=
    (Real.continuous_exp.comp continuous_fst).measurable.prodMk
      (Real.continuous_exp.comp continuous_snd).measurable
  exact measurable_const.mul (hK.comp he)

theorem moving_kernel_pair_transport {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (c : ℂ) (q a b : ℕ) (u v r s : ℝ) (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (δ ε : ℝ)
    (hleft : ∀ y, ‖complexPrimeInterval q a u v (fun x =>
      c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)) -
      ∫ x, c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) ∂μ‖ ≤ δ)
    (hright : ∀ x, ‖complexPrimeInterval q b r s (fun y =>
      c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)) -
      ∫ y, c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) ∂ν‖ ≤ ε) :
    ‖complexPrimeInterval q b r s (fun y => complexPrimeInterval q a u v (fun x =>
        c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y))) -
      ∫ x, ∫ y, c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) ∂ν ∂μ‖ ≤
      δ * reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + ε * μ.real Set.univ := by
  let H := fun x y => c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
  have hbase := measurable_movingRealKernel value T nodes ψ X lo hi hlo hhi φ G B D
    hB hD hφ hlip hout
  have hmeas : Measurable (Function.uncurry H) :=
    measurable_exp_pair_mul (movingRealKernel value T nodes ψ X lo hi hlo hhi φ G) hbase c
  have hnorm (x y : ℝ) : ‖H x y‖ ≤ ‖c‖ *
      ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) := by
    dsimp only [H]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (movingRealKernel_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _) (norm_nonneg _)
  exact prime_pair_integral_transport q a b u v r s μ ν H hmeas _ hnorm δ ε hleft hright

theorem moving_kernel_mixed_transport {σ : Type*} (value : σ → ℕ) {n : ℕ}
    (T : MovingSlotData σ n) (nodes : List MovingFormulaNode) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ) (G : ℕ → ℝ)
    (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (hφ : ∀ x, |φ x| ≤ B)
    (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|) (hout : ∀ x, 1 ≤ |x| → φ x = 0)
    (c : ℂ) (q a b : ℕ) (u v r s J : ℝ) (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (δ ε : ℝ)
    (hleft : ∀ y, ‖complexIntegerInterval q a u v J (fun x =>
      c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)) -
      ∫ x, c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) ∂μ‖ ≤ δ)
    (hright : ∀ x, ‖complexPrimeInterval q b r s (fun y =>
      c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)) -
      ∫ y, c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) ∂ν‖ ≤ ε) :
    ‖complexPrimeInterval q b r s (fun y => complexIntegerInterval q a u v J (fun x =>
        c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y))) -
      ∫ x, ∫ y, c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y) ∂ν ∂μ‖ ≤
      δ * reciprocalPrimeInterval q b (Real.exp r) (Real.exp s) + ε * μ.real Set.univ := by
  let H := fun x y => c * movingRealKernel value T nodes ψ X lo hi hlo hhi φ G (Real.exp x) (Real.exp y)
  have hbase := measurable_movingRealKernel value T nodes ψ X lo hi hlo hhi φ G B D
    hB hD hφ hlip hout
  have hmeas : Measurable (Function.uncurry H) :=
    measurable_exp_pair_mul (movingRealKernel value T nodes ψ X lo hi hlo hhi φ G) hbase c
  have hnorm (x y : ℝ) : ‖H x y‖ ≤ ‖c‖ *
      ((SchwartzMap.seminorm ℝ 0 0 ψ) ^ (2 ^ n) * B ^ (2 ^ n - 1)) := by
    dsimp only [H]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (movingRealKernel_norm value T nodes ψ X lo hi hlo hhi φ G B hB hφ _ _) (norm_nonneg _)
  exact mixed_pair_integral_transport q a b u v r s J μ ν H hmeas _ hnorm δ ε hleft hright

end Ostmann

end OAI
