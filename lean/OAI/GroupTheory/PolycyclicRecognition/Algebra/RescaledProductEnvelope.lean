import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentBoxes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialPrefixEnvelope

namespace OAI

/-! # Common vanishing envelopes for products of nilpotent box points -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Manifold Topology

variable {I L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- Multiplying two varying points with a common sublinear coordinate error
preserves that type of error, uniformly over the points. This is used to
attach a bounded-prefix chain to an already allowed sheet suffix. -/
theorem exists_rescaled_product_envelope
    (dynkin : NilpotentDynkinExpansionInput E G)
    (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
    (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hExp : IsGroupExponential Exp)
    (X : I → L) {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥)
    (b₀ : Basis (Fin (finrank ℝ L)) ℝ L)
    (s : I → ℝ) (β : WordBasisSelections X (boundedBracketWords c))
    (hβ : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords c) b₀)
      (fun w => bracketWordExponent s w) β.val)
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop) (hscale1 : ∀ n, 1 ≤ scale n)
    (ε₁ ε₂ : ℕ → ℝ) (hε₁0 : ∀ n, 0 ≤ ε₁ n) (hε₂0 : ∀ n, 0 ≤ ε₂ n)
    (hε₁ : Tendsto ε₁ atTop (𝓝 0)) (hε₂ : Tendsto ε₂ atTop (𝓝 0)) :
    ∃ η : ℕ → ℝ, (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      ∀ n x y,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
        (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun x‖ ≤
          Real.exp (scale n * ε₁ n) →
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
        (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun y‖ ≤
          Real.exp (scale n * ε₂ n) →
      ∃ z, Exp (e z) = Exp (e x) * Exp (e y) ∧
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
          (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun z‖ ≤
            Real.exp (scale n * η n) := by
  obtain ⟨C, hC, hprod⟩ := exists_uniform_word_box_product_bound dynkin e Exp hExp X hc b₀
  obtain ⟨η, hη0, hη, hηbound⟩ := exists_polynomial_exponential_envelope
    scale hscale hscale1 (fun n => ε₁ n + ε₂ n) (fun n => add_nonneg (hε₁0 n) (hε₂0 n))
    (by simpa only [zero_add] using hε₁.add hε₂) (C * (1 + (2 : ℝ)) ^ c)
    (mul_nonneg hC (by positivity)) c
  refine ⟨η, hη0, hη, ?_⟩
  intro n x y hx hy
  have hr : 0 ≤ scale n := le_trans (by norm_num) (hscale1 n)
  let R := Real.exp (scale n * (ε₁ n + ε₂ n))
  have hxR : Real.exp (scale n * ε₁ n) ≤ R :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hε₂0 n)) hr)
  have hyR : Real.exp (scale n * ε₂ n) ≤ R :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hε₁0 n)) hr)
  have hg := hprod s β hβ (scale n) hr 2 R (Real.exp_pos _).le
    ![Exp (e x), Exp (e y)] (by
      intro j
      fin_cases j
      · exact ⟨x, rfl, hx.trans hxR⟩
      · exact ⟨y, rfl, hy.trans hyR⟩)
  obtain ⟨z, hz, hb⟩ := hg
  refine ⟨z, ?_, hb.trans (hηbound n)⟩
  simpa [List.ofFn_succ] using hz

end PolycyclicRecognition

end

end OAI
