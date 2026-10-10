import OAI.Analysis.ModularTheory.WeightGNS

namespace OAI

/-! Closedness estimate for the concrete core weight. Strong convergence of
operators and norm convergence of their finite-weight vectors bound the
weight of the limiting operator. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

lemma modularCoreSquareWeight_le_of_strong_weightVectors
    (R : ℕ → (Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)))
    (hR : ∀ n, R n ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (hfin : ∀ n, modularCoreSquareWeight S (R n) < ⊤)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hstrong : ∀ f, Tendsto (fun n => R n f) atTop (𝓝 (T f)))
    (ζ : Lp H 2 (volume : Measure ℝ))
    (hζ : Tendsto (fun n => modularWeightVector S (R n) (hR n) (hfin n))
      atTop (𝓝 ζ)) :
    modularCoreSquareWeight S T ≤ ENNReal.ofReal (‖ζ‖ ^ 2) := by
  apply iSup_le
  intro m
  have hl := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (((hstrong (modularCoreWeightVector S m)).norm).pow 2)
  have hr := ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hζ.norm).pow 2)
  apply le_of_tendsto_of_tendsto hl hr
  apply Eventually.of_forall
  intro n
  apply ENNReal.ofReal_le_ofReal
  dsimp only
  rw [modularWeightVector_norm_sq]
  exact modularCoreWeightVector_norm_sq_le S (R n) (hfin n) m

end WeakPureInfiniteness

end

end OAI
