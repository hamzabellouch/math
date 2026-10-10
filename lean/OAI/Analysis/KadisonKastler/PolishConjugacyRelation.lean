import OAI.Analysis.KadisonKastler.StrongUnitaryEvaluation
import OAI.Analysis.KadisonKastler.MeasurableConjugacyTests
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

namespace OAI

/-! # The Borel implementer relation on the Polish unitary model

Measurable evaluation of the countable contraction fields suffices.
No measurability in the operator norm topology is imposed.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [MeasurableSpace H] [BorelSpace H]

instance strongUnitarySpaceMeasurable (ξ : ℕ → H) : MeasurableSpace (StrongUnitarySpace ξ) :=
  borel (StrongUnitarySpace ξ)

instance strongUnitarySpaceBorel (ξ : ℕ → H) : BorelSpace (StrongUnitarySpace ξ) := ⟨rfl⟩

omit [CompleteSpace H] in
theorem measurable_operator_field_apply (T : X → H →L[ℂ] H)
    (hT : ∀ x, Measurable (fun p => T p x)) (v : X → H) (hv : Measurable v) :
    Measurable (fun p => T p (v p)) := by
  have hm : Measurable (fun p : H × X => T p.2 p.1) :=
    measurable_uncurry_of_continuous_of_measurable (fun p => (T p).continuous) hT
  exact hm.comp (hv.prodMk measurable_id)

theorem measurable_conjugation_on_strongUnitarySpace
    (ξ : ℕ → H) (hξ : DenseRange ξ) (T : X → H →L[ℂ] H)
    (hT : ∀ x, Measurable (fun p => T p x)) (x : H) :
    Measurable (fun p : X × StrongUnitarySpace ξ =>
      unitaryConj (decodeStrongUnitary ξ p.2) (T p.1) x) := by
  have : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  have hU (y : H) : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (decodeStrongUnitary ξ p.2 : H →L[ℂ] H) y) :=
    (continuous_decodeStrongUnitary_apply ξ hξ y).measurable.comp measurable_snd
  have hUs : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (star (decodeStrongUnitary ξ p.2) : H →L[ℂ] H) x) :=
    (continuous_star_decodeStrongUnitary_apply ξ hξ x).measurable.comp measurable_snd
  have hTx := measurable_operator_field_apply (fun p : X × StrongUnitarySpace ξ => T p.1)
    (fun y => (hT y).comp measurable_fst) _ hUs
  exact measurable_operator_field_apply
    (fun p : X × StrongUnitarySpace ξ => (decodeStrongUnitary ξ p.2 : H →L[ℂ] H)) hU _ hTx

theorem measurable_star_conjugation_on_strongUnitarySpace
    (ξ : ℕ → H) (hξ : DenseRange ξ) (T : X → H →L[ℂ] H)
    (hT : ∀ x, Measurable (fun p => T p x)) (x : H) :
    Measurable (fun p : X × StrongUnitarySpace ξ =>
      unitaryConj (star (decodeStrongUnitary ξ p.2)) (T p.1) x) := by
  have : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  have hUs (y : H) : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (star (decodeStrongUnitary ξ p.2) : H →L[ℂ] H) y) :=
    (continuous_star_decodeStrongUnitary_apply ξ hξ y).measurable.comp measurable_snd
  have hU : Measurable (fun p : X × StrongUnitarySpace ξ =>
      (decodeStrongUnitary ξ p.2 : H →L[ℂ] H) x) :=
    (continuous_decodeStrongUnitary_apply ξ hξ x).measurable.comp measurable_snd
  have hTx := measurable_operator_field_apply (fun p : X × StrongUnitarySpace ξ => T p.1)
    (fun y => (hT y).comp measurable_fst) _ hU
  simpa only [unitaryConj, Unitary.coe_star, star_star, mul_apply_eq_comp] using
    measurable_operator_field_apply
      (fun p : X × StrongUnitarySpace ξ => (star (decodeStrongUnitary ξ p.2) : H →L[ℂ] H))
      hUs _ hTx

/-- This relation has precisely the algebra-conjugacy and displacement
conditions required by the measurable selection step. -/
theorem measurableSet_bounded_implementer_relation
    (M N : X → VonNeumannAlgebra H)
    (A : ∀ p, StrongUnitBallTestSequence (M p)) (B : ∀ p, StrongUnitBallTestSequence (N p))
    (hA : ∀ j x, Measurable (fun p => (A p).op j x))
    (hB : ∀ j x, Measurable (fun p => (B p).op j x))
    (ξ : ℕ → H) (hξ : DenseRange ξ) {a : ℝ} (ha : 0 ≤ a) :
    MeasurableSet {p : X × StrongUnitarySpace ξ |
      Conjugates (decodeStrongUnitary ξ p.2) (M p.1) (N p.1) ∧
      ‖(decodeStrongUnitary ξ p.2 : H →L[ℂ] H) - 1‖ ≤ a} := by
  have : PolishSpace (StrongUnitarySpace ξ) := strongUnitarySpace_polish ξ hξ
  apply measurableSet_bounded_conjugates_of_vector_tests
    (fun p : X × StrongUnitarySpace ξ => M p.1)
    (fun p : X × StrongUnitarySpace ξ => N p.1)
    (fun p => A p.1) (fun p => B p.1) ξ hξ
    (fun p => decodeStrongUnitary ξ p.2)
  · intro j q l
    simpa only [sub_apply, Pi.sub_def, Function.comp_def] using
      (measurable_conjugation_on_strongUnitarySpace ξ hξ (fun p => (A p).op j)
        (hA j) (ξ l)).sub ((hB q (ξ l)).comp measurable_fst)
  · intro j q l
    simpa only [sub_apply, Pi.sub_def, Function.comp_def] using
      (measurable_star_conjugation_on_strongUnitarySpace ξ hξ (fun p => (B p).op j)
        (hB j) (ξ l)).sub ((hA q (ξ l)).comp measurable_fst)
  · intro l
    simpa only [sub_apply, one_apply_eq_self, Pi.sub_def, Function.comp_def] using
      ((continuous_decodeStrongUnitary_apply ξ hξ (ξ l)).measurable.comp
        measurable_snd).sub measurable_const
  · exact ha

end

end KadisonKastler

end OAI
