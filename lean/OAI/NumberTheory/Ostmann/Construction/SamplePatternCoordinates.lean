import OAI.NumberTheory.Ostmann.Tree.SampleEqualityPatterns
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotRelabel

namespace OAI

/-! # Finite coordinates for each actual equality pattern -/

namespace Ostmann
open scoped Classical

/-- The class coordinates used by the finite independent-prior comparison. -/
noncomputable def samplePatternLabels {I : Type*} [Fintype I]
    (s : Setoid I) {N : ℕ} (hcard : Fintype.card (Quotient s) = N + 1) : I → Fin (N + 1) :=
  fun i => (Fintype.equivFinOfCardEq hcard) (Quotient.mk'' i)

theorem samplePatternLabels_surjective {I : Type*} [Fintype I]
    (s : Setoid I) {N : ℕ} (hcard : Fintype.card (Quotient s) = N + 1) :
    Function.Surjective (samplePatternLabels s hcard) :=
  (Fintype.equivFinOfCardEq hcard).surjective.comp Quotient.mk''_surjective

noncomputable def samplePatternRepresentative {I : Type*} [Fintype I]
    (s : Setoid I) {N : ℕ} (hcard : Fintype.card (Quotient s) = N + 1)
    (c : Fin (N + 1)) : {i : I // samplePatternLabels s hcard i = c} :=
  ⟨(samplePatternLabels_surjective s hcard c).choose,
    (samplePatternLabels_surjective s hcard c).choose_spec⟩

noncomputable def samplePatternValues {I A : Type*} [Fintype I]
    (s : Setoid I) {N : ℕ} (hcard : Fintype.card (Quotient s) = N + 1)
    (x : Quotient s → A) : Fin (N + 1) → A :=
  fun c => x ((Fintype.equivFinOfCardEq hcard).symm c)

@[simp] theorem samplePatternValues_labels {I A : Type*} [Fintype I]
    (s : Setoid I) {N : ℕ} (hcard : Fintype.card (Quotient s) = N + 1)
    (x : Quotient s → A) (i : I) :
    samplePatternValues s hcard x (samplePatternLabels s hcard i) = x (Quotient.mk'' i) := by
  simp only [samplePatternValues, samplePatternLabels, Equiv.symm_apply_apply]

theorem samplePatternValues_injective {I A : Type*} [Fintype I]
    (s : Setoid I) {N : ℕ} (hcard : Fintype.card (Quotient s) = N + 1)
    (x : Quotient s → A) (hx : Function.Injective x) :
    Function.Injective (samplePatternValues s hcard x) :=
  hx.comp (Fintype.equivFinOfCardEq hcard).symm.injective

/-- Tier separation of actual primes makes the original tier constant on each
realized class. This derives compatibility instead of requiring a new pattern hypothesis. -/
theorem samplePattern_tier_compatible {I A : Type*} (p : SampleEqualityPattern I A)
    (tier : I → ℕ) (prime : A → ℕ)
    (hdisjoint : ∀ i j, tier i ≠ tier j → prime (p.evaluate i) ≠ prime (p.evaluate j))
    (i j : I) (hij : p.1 i j) : tier i = tier j := by
  by_contra ht
  apply hdisjoint i j ht
  exact congrArg (fun q => prime (p.2.val q)) (Quotient.sound hij)

noncomputable def samplePatternTier {I : Type*} [Fintype I]
    (s : Setoid I) {N : ℕ} (hcard : Fintype.card (Quotient s) = N + 1)
    (tier : I → ℕ) : Fin (N + 1) → ℕ :=
  fun c => tier (samplePatternRepresentative s hcard c).val

theorem samplePatternTier_labels {I : Type*} [Fintype I]
    (s : Setoid I) {N : ℕ} (hcard : Fintype.card (Quotient s) = N + 1)
    (tier : I → ℕ) (htier : ∀ i j, s i j → tier i = tier j) (i : I) :
    samplePatternTier s hcard tier (samplePatternLabels s hcard i) = tier i := by
  apply htier
  apply Quotient.exact
  apply (Fintype.equivFinOfCardEq hcard).injective
  exact (samplePatternRepresentative s hcard (samplePatternLabels s hcard i)).property

theorem MovingSlotData.levels_samplePattern {I : Type*} [Fintype I]
    (s : Setoid I) {N : ℕ} (hcard : Fintype.card (Quotient s) = N + 1)
    (tier : I → ℕ) (htier : ∀ i j, s i j → tier i = tier j)
    {n : ℕ} (T : MovingSlotData I n) (hT : T.Levels tier) :
    (T.map (samplePatternLabels s hcard)).Levels (samplePatternTier s hcard tier) :=
  (T.levels_map (samplePatternLabels s hcard) tier (samplePatternTier s hcard tier)
    (samplePatternTier_labels s hcard tier htier)).mpr hT

end Ostmann

end OAI
