import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledProductEnvelope

namespace OAI

/-! # Translating bounded-prefix chains by an allowed sheet suffix -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Manifold Topology

variable {I L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- The original suffix and every translated prefix share a single
vanishing envelope. Multiplication preserves all actual generator edges;
the new initial logarithm is exactly the original suffix. -/
theorem exists_translated_rescaled_chain
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
    (hε₁ : Tendsto ε₁ atTop (𝓝 0)) (hε₂ : Tendsto ε₂ atTop (𝓝 0))
    (hinj : Function.Injective (Exp ∘ e))
    {K : Type*} {N : ℕ}
    (base : ℕ → L) (vertex : ℕ → K → Fin (N + 1) → L)
    (hbase : ∀ n,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
        (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun (base n)‖ ≤
          Real.exp (scale n * ε₁ n))
    (hvertex : ∀ n q j,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
        (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun (vertex n q j)‖ ≤
          Real.exp (scale n * ε₂ n))
    (hzero : ∀ n q, vertex n q 0 = 0)
    (step : ℕ → K → Fin N → G)
    (hstep : ∀ n q j, Exp (e (vertex n q j.succ)) =
      Exp (e (vertex n q j.castSucc)) * step n q j) :
    ∃ (η : ℕ → ℝ) (translated : ℕ → K → Fin (N + 1) → L),
      (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n q, translated n q 0 = base n) ∧
      (∀ n q j, Exp (e (translated n q j)) = Exp (e (base n)) * Exp (e (vertex n q j))) ∧
      (∀ n q j,
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
          (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun (translated n q j)‖ ≤
            Real.exp (scale n * η n)) ∧
      (∀ n q j, Exp (e (translated n q j.succ)) =
        Exp (e (translated n q j.castSucc)) * step n q j) := by
  obtain ⟨η, hη0, hη, hprod⟩ := exists_rescaled_product_envelope
    dynkin e Exp hExp X hc b₀ s β hβ scale hscale hscale1 ε₁ ε₂ hε₁0 hε₂0 hε₁ hε₂
  have hex (n : ℕ) (q : K) (j : Fin (N + 1)) :=
    hprod n (base n) (vertex n q j) (hbase n) (hvertex n q j)
  choose translated hmul hbound using hex
  refine ⟨η, translated, hη0, hη, ?_, hmul, hbound, ?_⟩
  · intro n q
    apply hinj
    change Exp (e (translated n q 0)) = Exp (e (base n))
    rw [hmul, hzero, map_zero, hExp.map_zero, mul_one]
  · intro n q j
    rw [hmul, hstep, hmul, mul_assoc]

end PolycyclicRecognition

end

end OAI
