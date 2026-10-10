import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac.Def
import Mathlib.MeasureTheory.Measure.Dirac.Basic

namespace OAI

/-!
# Predrawing every conditional seed

A finite table of independent conditional seeds can be sampled before the
observation prefix. Looking up the entry indexed by the observed prefix uses no
later randomness. The whole table, including unused entries, may be disclosed.
These lemmas are probability identities only; an actual prefix law and an actual
history-only online replay remain separate obligations.
-/

namespace MatroidProphet.SecretaryPrecommit

open MeasureTheory
open scoped ENNReal

variable {B A : Type*} [Fintype B] [Fintype A]
  [MeasurableSpace B] [MeasurableSingletonClass B]
  [MeasurableSpace A] [MeasurableSingletonClass A]

omit [Fintype A] [MeasurableSpace B] [MeasurableSingletonClass B]
  [MeasurableSingletonClass A] in
/-- Every precommitted coordinate retains its specified conditional law. -/
theorem table_eval_map (κ : B → Measure A) [∀ b, IsProbabilityMeasure (κ b)]
    (b : B) :
    (Measure.pi κ).map (fun t : B → A => t b) = κ b :=
  (measurePreserving_eval κ b).map_eq

/-- Exact joint atoms of the observed index and the selected precommitted seed.
The index law is independent of the entire table, not merely its selected entry. -/
theorem selected_joint_singleton (ρ : Measure B) (κ : B → Measure A)
    [∀ b, IsProbabilityMeasure (κ b)] (b : B) (a : A) :
    ((ρ.prod (Measure.pi κ)).map
      (fun z : B × (B → A) => (z.1, z.2 z.1))) {(b, a)} =
        ρ {b} * κ b {a} := by
  classical
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  have hpre : (fun z : B × (B → A) => (z.1, z.2 z.1)) ⁻¹' {(b, a)} =
      ({b} : Set B) ×ˢ ((fun t : B → A => t b) ⁻¹' {a}) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
      Set.mem_prod]
    constructor
    · rintro ⟨hb, ha⟩
      exact ⟨hb, by simpa [hb] using ha⟩
    · rintro ⟨hb, ha⟩
      exact ⟨hb, by simpa [hb] using ha⟩
  rw [hpre, Measure.prod_prod]
  congr 1
  rw [← Measure.map_apply (measurable_pi_apply b) (measurableSet_singleton a),
    table_eval_map]

/-- A target joint law is recovered from its conditional-fiber factorization. -/
theorem selected_joint_eq (ρ : Measure B) (κ : B → Measure A)
    [∀ b, IsProbabilityMeasure (κ b)] (ν : Measure (B × A))
    (hν : ∀ b a, ν {(b, a)} = ρ {b} * κ b {a}) :
    (ρ.prod (Measure.pi κ)).map
      (fun z : B × (B → A) => (z.1, z.2 z.1)) = ν := by
  apply Measure.ext_of_singleton
  rintro ⟨b, a⟩
  rw [selected_joint_singleton, hν]

/-- Integrating after table lookup gives precisely the conditional mixture. -/
theorem integral_selected (ρ : Measure B) [IsFiniteMeasure ρ]
    (κ : B → Measure A) [∀ b, IsProbabilityMeasure (κ b)]
    (f : B → A → ℝ) :
    (∫ z : B × (B → A), f z.1 (z.2 z.1) ∂ρ.prod (Measure.pi κ)) =
      ∫ b, ∫ a, f b a ∂κ b ∂ρ := by
  rw [integral_prod _ Integrable.of_finite]
  apply integral_congr_ae
  exact ae_of_all _ fun b => by
    dsimp only
    rw [← table_eval_map κ b,
      integral_map_of_stronglyMeasurable (measurable_pi_apply b)
        (measurable_of_countable (f b)).stronglyMeasurable]

omit [Fintype A] [MeasurableSpace B] [MeasurableSingletonClass B]
  [MeasurableSingletonClass A] in
/-- Every table coordinate satisfies its fiber constraint almost surely,
simultaneously, so an arbitrary later lookup cannot choose a bad coordinate. -/
theorem ae_table_fibers (κ : B → Measure A) [∀ b, IsProbabilityMeasure (κ b)]
    (G : B → A → Prop) (hG : ∀ b, ∀ᵐ a ∂κ b, G b a) :
    ∀ᵐ t : B → A ∂Measure.pi κ, ∀ b, G b (t b) := by
  rw [ae_all_iff]
  intro b
  exact (measurePreserving_eval κ b).quasiMeasurePreserving.ae (hG b)

/-- The observed index may be a function of a larger random-prefix experiment.
Only independence of that experiment from the entire precommitted table is used. -/
theorem selected_joint_of_map {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (ρ : Measure B)
    (P : Ω → B) (hP : Measurable P) (hmap : μ.map P = ρ)
    (κ : B → Measure A) [∀ b, IsProbabilityMeasure (κ b)] :
    (μ.prod (Measure.pi κ)).map
      (fun z : Ω × (B → A) => (P z.1, z.2 (P z.1))) =
    (ρ.prod (Measure.pi κ)).map
      (fun z : B × (B → A) => (z.1, z.2 z.1)) := by
  have hp : MeasurePreserving P μ ρ := ⟨hP, hmap⟩
  have hi := MeasurePreserving.id (Measure.pi κ)
  have hprod := (hp.prod hi).map_eq
  have hcomp := Measure.map_map (μ := μ.prod (Measure.pi κ)) (measurable_of_countable
    (fun z : B × (B → A) => (z.1, z.2 z.1))) (hP.prodMap measurable_id)
  rw [hprod] at hcomp
  simpa [Function.comp_def, Prod.map] using hcomp.symm

end MatroidProphet.SecretaryPrecommit

end OAI
