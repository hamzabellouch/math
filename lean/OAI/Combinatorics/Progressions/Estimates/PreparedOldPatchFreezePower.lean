import OAI.Combinatorics.Progressions.Dynamics.PreparedCanonicalFreezeBudget
import OAI.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget

namespace OAI

section

namespace Erdos3
open scoped BigOperators

theorem exists_preparedOldPatchFreeze_power (s : ℕ) :
    ∃ e : ℕ, 2 ≤ e ∧ ∀ {X J : Type} {p : ℝ}, 2 ≤ p →
      ∀ D E m : ℕ, m ≤ s → ∀ (A : PolynomialPatch X s (D + E)),
      relativePatchComplexity A ≤ p →
      ∀ (L : RankPreparationFamily X J m), L.Sized D (m * D) →
      let M := preparationCoordinateCap m D (m * D)
      ∀ gain : ℝ, Real.exp (-p) ≤ gain →
      (∀ j, (32 * ((D : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) * ((m : ℝ) + 1) / gain) *
        (Fintype.card (L j).Coord : ℝ) * Real.exp (allocatedUniformChartLog (M : ℝ)) ≤
          Real.exp ((p + 2) ^ e)) ∧
      Real.exp (-((p + 2) ^ e)) ≤ gain / (128 * ((D : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1)) := by
  obtain ⟨capPower, _, _, _, hcap⟩ := exists_preparation_input_power_budget s 0
  obtain ⟨e, he, hprecision⟩ := exists_preparedCanonicalFreeze_power s capPower
  refine ⟨e, he, ?_⟩
  intro X J p hp D E m hm A hA L hsize M gain hgain
  have hp0 : 0 ≤ p := by linarith
  have hD : (D : ℝ) ≤ p := by
    have hd := (relativePatchComplexity_rank_le A).trans hA
    push_cast at hd
    linarith [Nat.cast_nonneg (α := ℝ) E]
  have hM := (hcap p hp m D 0 0 hm hD (by simpa using hp0)
    (by simpa using Real.exp_nonneg ((p + 2) ^ (0 : ℕ)))).2.1
  have hprecision' := hprecision hp0 M m hM hm
  have hq0 : 0 ≤ preparedCanonicalFreezeLog p M m := by
    unfold preparedCanonicalFreezeLog allocatedUniformChartLog
    positivity
  have hδ : Real.exp (-((p + 2) ^ e)) ≤
      Real.exp (-(3 * preparedCanonicalFreezeLog p M m + 130)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hcoord (j) : Fintype.card (L j).Coord ≤ M :=
    (preparationCoordinateCap_bounds hsize le_rfl j).1
  obtain ⟨_, _, _, _, _, _, _, hinflate, herr⟩ :=
    preparedCanonicalFreeze_log_bounds A L hp0 hA hcoord hgain hδ
  refine ⟨fun j => (hinflate j).trans (Real.exp_le_exp.mpr ?_), herr⟩
  linarith

end Erdos3

end

end OAI
