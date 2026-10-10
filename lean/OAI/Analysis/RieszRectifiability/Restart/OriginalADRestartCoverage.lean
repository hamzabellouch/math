import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.SelectedRestartGeometry
import OAI.Analysis.RieszRectifiability.Nets.OriginalADCellBadCountBudget

namespace OAI

/-!
# Selected restart assembly with controlled mass deficit

`HasSelectedRestartAssembly` records how parent charts incorporate selected
child charts while preserving range and Lipschitz bounds. For a fixed regular
AD measure with a bounded Riesz transform, restart-loss and bad-count budgets
then produce a root-ball chart with arbitrarily small relative mass deficit.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

def HasSelectedRestartAssembly {d : ℕ} {μ : Measure (Ambient d)}
    {R : ℝ} {hR : 0 < R} {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (n : ℕ) (Bad : SupportCellDescendant μ R hR k z → Prop)
    (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
    (step : ℝ≥0 → ℝ≥0) : Prop :=
  ∀ (q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q}) (M : ℝ≥0)
    (child : ∀ w : selectedRestartNext Bad q.val (E q),
      ball (0 : Ambient n) w.val.val.radius → Ambient d),
    (∀ w, LipschitzWith M (child w)) →
    (∀ w, Set.range (child w) ⊆ closedBall w.val.val.center (2 * w.val.val.radius)) →
    ∃ g : ball (0 : Ambient n) q.val.radius → Ambient d,
      LipschitzWith (step M) g ∧ Set.range g ⊆ closedBall q.val.center (2 * q.val.radius) ∧
      selectedRestartParent Bad q.val (E q) ⊆ Set.range g ∧
      ∀ w, w.val.val.cell ∩ Set.range (child w) ⊆ Set.range g

theorem original_AD_Riesz_selected_restart_uniform_deficit {p d : ℕ} (hnd : p + 1 ≤ d)
    (μ : Measure (Ambient d)) [μ.Regular] (hAD : ADRegular (p + 1) μ)
    (hRiesz : RieszL2Bounded (p + 1) μ) (H ε : ℝ) (hH : 1 ≤ H) (hε : 0 < ε)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ b : ℕ, 0 < b ∧
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
        AdmissibleRadius μ (latticeRadius R k / 8) →
        let Bad := fun i : SupportCellDescendant μ R hR k z =>
          ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
        ∀ (E : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} → Set (Ambient d))
          (step : ℝ≥0 → ℝ≥0),
          HasSelectedRestartAssembly (p + 1) Bad E step →
          (∀ q, μ (selectedRestartRemainder Bad q.val (E q)) ≤ ENNReal.ofReal δ * μ q.val.cell) →
          ∃ g : ball (0 : Ambient (p + 1)) (latticeRadius R k) → Ambient d,
            LipschitzWith (badBudgetChartConstant step b) g ∧
            Set.range g ⊆ closedBall (z : Ambient d) (2 * latticeRadius R k) ∧
            μ (cleanSupportCell μ R hR k z \ Set.range g) ≤
              ENNReal.ofReal ζ * μ (cleanSupportCell μ R hR k z) := by
  obtain ⟨δ, hδ, hregions⟩ := original_AD_Riesz_restart_loss_budget hnd μ hAD hRiesz H ε hH hε
    (ζ / 2) (half_pos hζ)
  obtain ⟨b, hb, hcounts⟩ := original_AD_Riesz_cell_bad_count_budget hnd μ hAD hRiesz H ε hH hε
    (ζ / 2) (half_pos hζ)
  refine ⟨δ, hδ, b, hb, ?_⟩
  intro R hR k z hcore
  dsimp only
  intro E step hassemble hloss
  let Bad := fun i : SupportCellDescendant μ R hR k z =>
    ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius)
  let q : {q : SupportCellDescendant μ R hR k z // cellRestartsAfter Bad q} :=
    ⟨supportCellRoot μ R hR k z, Or.inl rfl⟩
  obtain ⟨A, _, _, hAmass, hAcount⟩ := hcounts R hR k z hcore
  obtain ⟨g, hg, hgrange, _, hdeficit⟩ := exists_restart_chart_with_original_mass_deficit
    μ R hR k z Bad
    (fun r => selectedRestartRemainder Bad r.val (E r))
    (fun r => selectedRestartParent Bad r.val (E r))
    (fun r => selectedRestartNext Bad r.val (E r)) step
    (fun r w hw => selected_restart_next_consumes_bad_cell Bad r.val (E r) w hw)
    (fun r => selected_restart_partition Bad r.val (E r)) hassemble b q A
    (fun x hx => hAcount x hx.2 q.val)
  have hsum := hregions R hR k z hcore
    (fun r => μ (selectedRestartRemainder Bad r.val (E r))) hloss
  have hbound := hdeficit.trans (add_le_add hAmass hsum)
  have heq : ENNReal.ofReal (ζ / 2) + ENNReal.ofReal (ζ / 2) = ENNReal.ofReal ζ := by
    rw [← ENNReal.ofReal_add (half_pos hζ).le (half_pos hζ).le, add_halves]
  refine ⟨g, hg, hgrange, ?_⟩
  simpa only [← add_mul, heq] using! hbound

end

end RieszRectifiability

end OAI
