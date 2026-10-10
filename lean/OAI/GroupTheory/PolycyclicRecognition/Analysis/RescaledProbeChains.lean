import OAI.GroupTheory.PolycyclicRecognition.Algebra.RescaledProductEnvelope

namespace OAI

/-! # Probe-dependent anchors and their translated generator chains -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Manifold Topology

variable {I L E G : Type*} [LieRing L] [LieAlgebra ℝ L]
  [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

/-- A tile anchor may depend on the probe. Uniform box bounds for those
anchors still give one vanishing envelope for all translated prefixes,
and the exact generator edges are preserved. -/
theorem exists_probe_translated_rescaled_chain
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
    {K : ℕ → Type*} {N : ℕ}
    (base : ∀ n, K n → L) (vertex : ∀ n, K n → Fin (N + 1) → L)
    (hbase : ∀ n q,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
        (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun (base n q)‖ ≤
          Real.exp (scale n * ε₁ n))
    (hvertex : ∀ n q j,
      ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
        (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun (vertex n q j)‖ ≤
          Real.exp (scale n * ε₂ n))
    (hzero : ∀ n q, vertex n q 0 = 0)
    (step : ∀ n, K n → Fin N → G)
    (hstep : ∀ n q j, Exp (e (vertex n q j.succ)) =
      Exp (e (vertex n q j.castSucc)) * step n q j) :
    ∃ (η : ℕ → ℝ) (translated : ∀ n, K n → Fin (N + 1) → L),
      (∀ n, 0 ≤ η n) ∧ Tendsto η atTop (𝓝 0) ∧
      (∀ n q, translated n q 0 = base n q) ∧
      (∀ n q j, Exp (e (translated n q j)) = Exp (e (base n q)) * Exp (e (vertex n q j))) ∧
      (∀ n q j,
        ‖(exponentialRescaleBasis (WordBasisSelections.basis X (boundedBracketWords c) β)
          (fun j => bracketWordExponent s (β.val j)) (scale n)).equivFun (translated n q j)‖ ≤
            Real.exp (scale n * η n)) ∧
      (∀ n q j, Exp (e (translated n q j.succ)) =
        Exp (e (translated n q j.castSucc)) * step n q j) := by
  obtain ⟨η, hη0, hη, hprod⟩ := exists_rescaled_product_envelope
    dynkin e Exp hExp X hc b₀ s β hβ scale hscale hscale1 ε₁ ε₂ hε₁0 hε₂0 hε₁ hε₂
  have hex (n : ℕ) (q : K n) (j : Fin (N + 1)) :=
    hprod n (base n q) (vertex n q j) (hbase n q) (hvertex n q j)
  choose translated hmul hbound using hex
  refine ⟨η, translated, hη0, hη, ?_, hmul, hbound, ?_⟩
  · intro n q
    apply hinj
    change Exp (e (translated n q 0)) = Exp (e (base n q))
    rw [hmul, hzero, map_zero, hExp.map_zero, mul_one]
  · intro n q j
    rw [hmul, hstep, hmul, mul_assoc]

end PolycyclicRecognition

end

end OAI
