import OAI.MeasureTheory.Falconer.Estimates.SeededInverse
import OAI.MeasureTheory.Falconer.Fourier.MaskJetSeparation

namespace OAI

/-! # Endpoint separation after a new inverse acts on existing jets

Both endpoint families keep all their original labels. Extracted scalar
weights charge only the newly added derivative orders, including the
complex angular multiplier when it is included as an extra label.
-/

namespace Falconer
open scoped ContDiff

variable {ι τ : Type} {X Y : Type*} [Fintype ι] [Fintype τ]
  [DecidableEq ι] [DecidableEq τ]

noncomputable abbrev seededPairJets (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3)) :
    MaskJetExpansion (ι ⊕ τ) (m+3) (Space (m+3)) :=
  (MaskJetExpansion.seed k).inverse m j

noncomputable def seededJetSeparation (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (r : ι ⊕ τ → ℝ) (B : ι → X → Space (m+3) → ℂ)
    (C : τ → Y → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y)) :
    SmoothSeparation X Y (Space (m+3)) where
  index := (seededPairJets m j k).index
  finite := inferInstance
  left := fun a x z => ((seededPairJets m j k).term a).coefficient z *
    ∏ i, (((seededPairJets m j k).term a).jet (.inl i)).scaledValue (r (.inl i)) (B i x) z
  right := fun a y z =>
    ∏ i, (((seededPairJets m j k).term a).jet (.inr i)).scaledValue (r (.inr i)) (C i y) z
  left_smooth := fun a x => ((seededPairJets m j k).term a).coefficient_smooth.mul
    (contDiff_prod (fun i _ => MaskJetIndex.scaledValue_contDiff _ _ _ (hB i x)))
  right_smooth := fun _a y =>
    contDiff_prod (fun i _ => MaskJetIndex.scaledValue_contDiff _ _ _ (hC i y))

theorem seededJetSeparation_left (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (r : ι ⊕ τ → ℝ) (B : ι → X → Space (m+3) → ℂ)
    (C : τ → Y → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (a : (seededPairJets m j k).index) (x : X) (z : Space (m+3)) :
    (seededJetSeparation m j k r B C hB hC).left a x z =
      ((seededPairJets m j k).term a).coefficient z *
        ∏ i, (((seededPairJets m j k).term a).jet (.inl i)).scaledValue
          (r (.inl i)) (B i x) z := rfl

theorem seededJetSeparation_right (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (r : ι ⊕ τ → ℝ) (B : ι → X → Space (m+3) → ℂ)
    (C : τ → Y → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (a : (seededPairJets m j k).index) (y : Y) (z : Space (m+3)) :
    (seededJetSeparation m j k r B C hB hC).right a y z =
      ∏ i, (((seededPairJets m j k).term a).jet (.inr i)).scaledValue
        (r (.inr i)) (C i y) z := rfl

theorem seededJetSeparation_exact (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (r : ι ⊕ τ → ℝ) (hr : ∀ i, r i ≠ 0)
    (B : ι → X → Space (m+3) → ℂ) (C : τ → Y → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y))
    (x : X) (y : Y) (e : Sphere (m+3)) :
    localInverseAmplitude m
      (fun z => (∏ i, (k (.inl i)).scaledValue (r (.inl i)) (B i x) z) *
        (∏ i, (k (.inr i)).scaledValue (r (.inr i)) (C i y) z)) j e =
      ((seededJetSeparation m j k r B C hB hC).scaleTerms
        (fun a => (MaskJetExpansion.seededRadiusWeight m j k r a : ℂ))).value x y e := by
  let F : ι ⊕ τ → X × Y → Space (m+3) → ℂ :=
    fun i xy z => Sum.elim (fun a => B a xy.1 z) (fun b => C b xy.2 z) i
  have hF (i : ι ⊕ τ) (xy : X × Y) : ContDiff ℝ ∞ (F i xy) := by
    cases i with
    | inl i => exact hB i xy.1
    | inr i => exact hC i xy.2
  have heq :
      (fun z => (∏ i, (k (.inl i)).scaledValue (r (.inl i)) (B i x) z) *
        (∏ i, (k (.inr i)).scaledValue (r (.inr i)) (C i y) z)) =
      fun z => ∏ i, (k i).scaledValue (r i) (F i (x,y)) z := by
    funext z
    rw [Fintype.prod_sum_type]
    rfl
  rw [heq,MaskJetExpansion.localInverseAmplitude_seeded_jets m j k r hr F hF (x,y) e,
    SmoothSeparation.scaleTerms_value]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.prod_sum_type,seededJetSeparation_left,seededJetSeparation_right]
  dsimp only [F,Sum.elim_inl,Sum.elim_inr]
  change (((seededPairJets m j k).term a).coefficient e *
      (MaskJetExpansion.seededRadiusWeight m j k r a : ℂ)) * (_ * _) =
    (MaskJetExpansion.seededRadiusWeight m j k r a : ℂ) *
      ((((seededPairJets m j k).term a).coefficient e * _) * _)
  ring

theorem seededJetSeparation_card (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (r : ι ⊕ τ → ℝ) (B : ι → X → Space (m+3) → ℂ)
    (C : τ → Y → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (hC : ∀ i y, ContDiff ℝ ∞ (C i y)) :
    Fintype.card (seededJetSeparation m j k r B C hB hC).index =
      MaskJetExpansion.inverseMultiplicity (m+2) j *
        (1+(Fintype.card ι+Fintype.card τ)*(m+3))^(2*j) := by
  change Fintype.card (seededPairJets m j k).index = _
  rw [MaskJetExpansion.card_inverse_seed,Fintype.card_sum]

theorem seededJetSeparation_added_order (m j : ℕ) (k : ι ⊕ τ → MaskJetIndex (m+3))
    (a : (seededPairJets m j k).index) :
    (∑ i, ((((seededPairJets m j k).term a).jet (.inl i)).order-(k (.inl i)).order)) +
      (∑ i, ((((seededPairJets m j k).term a).jet (.inr i)).order-(k (.inr i)).order)) ≤ 2*j := by
  have h := MaskJetExpansion.seed_inverse_added_order m j k a
  rw [Fintype.sum_sum_type] at h
  exact h

end Falconer

end OAI
