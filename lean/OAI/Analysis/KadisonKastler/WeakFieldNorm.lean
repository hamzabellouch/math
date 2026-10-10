import OAI.Analysis.KadisonKastler.WeakOperatorFields
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

/-! # The quotient norm is the essential operator norm

The general Banach quotient supplies arbitrarily close representatives.
A countable intersection gives the exact essential bound, and cutting off
its exceptional set produces a norm-minimizing representative.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every representative satisfies its quotient norm bound almost everywhere. -/
theorem operatorField_ae_norm_le (F : WeakOperatorRepresentative (H := H) μ) :
    ∀ᵐ x ∂μ, ‖WeakOperatorRepresentative.eval F x‖ ≤ ‖operatorFieldQuotient μ F‖ := by
  have hn (n : ℕ) : ∀ᵐ x ∂μ, ‖WeakOperatorRepresentative.eval F x‖ ≤
      ‖operatorFieldQuotient μ F‖ + 1 / (n + 1 : ℝ) := by
    obtain ⟨G, hG, hnorm⟩ := (operatorFieldZeroIdeal (H := H) μ).quotient_norm_lt_rep
      (operatorFieldQuotient μ F) (one_div_pos.mpr (by positivity : 0 < (n + 1 : ℝ)))
    have heq : WeakOperatorRepresentative.eval G =ᵐ[μ] WeakOperatorRepresentative.eval F :=
      (operatorFieldQuotient_eq_iff μ G F).mp hG
    filter_upwards [heq] with x hx
    rw [← hx]
    exact (WeakOperatorRepresentative.eval_norm_le G x).trans hnorm.le
  filter_upwards [ae_all_iff.mpr hn] with x hx
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  exact (hx n).trans (by linarith)

/-- The actual weak-operator quotient admits representatives attaining its norm. -/
theorem exists_operatorFieldRepresentative (T : WeakOperatorField (H := H) μ) :
    ∃ F : WeakOperatorRepresentative (H := H) μ,
      operatorFieldQuotient μ F = T ∧ ‖F‖ ≤ ‖T‖ := by
  classical
  obtain ⟨F, rfl⟩ := operatorFieldQuotient_surjective (H := H) μ T
  let C := ‖operatorFieldQuotient μ F‖
  let f : D → H →L[ℂ] H := fun x =>
    if ‖WeakOperatorRepresentative.eval F x‖ ≤ C then WeakOperatorRepresentative.eval F x else 0
  have hnorm (x : D) : ‖f x‖ ≤ C := by
    dsimp [f]
    split_ifs with hx
    · exact hx
    · simpa only [norm_zero] using norm_nonneg (operatorFieldQuotient μ F)
  have heq : WeakOperatorRepresentative.eval F =ᵐ[μ] f :=
    (operatorField_ae_norm_le F).mono fun x hx => by simp [f, C, hx]
  have hm (ξ : H) : AEStronglyMeasurable (fun x => f x ξ) μ :=
    (WeakOperatorRepresentative.eval_aestronglyMeasurable F ξ).congr
      (heq.mono fun _ hx => congrArg (fun T => T ξ) hx)
  have hs (ξ : H) : AEStronglyMeasurable (fun x => star (f x) ξ) μ :=
    (WeakOperatorRepresentative.star_eval_aestronglyMeasurable F ξ).congr
      (heq.mono fun _ hx => congrArg (fun T : H →L[ℂ] H => star T ξ) hx)
  let G := WeakOperatorRepresentative.mk f C hnorm hm hs
  refine ⟨G, ?_, WeakOperatorRepresentative.norm_mk_le f (norm_nonneg _) hnorm hm hs⟩
  exact ((operatorFieldQuotient_eq_iff μ F G).mpr heq).symm

end

end KadisonKastler

end OAI
