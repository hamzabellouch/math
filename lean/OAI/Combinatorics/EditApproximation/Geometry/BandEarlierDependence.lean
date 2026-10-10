import OAI.Combinatorics.EditApproximation.Geometry.UnskippedBands
import OAI.Combinatorics.EditApproximation.Geometry.WideEarlierInputs

namespace OAI

/-! The band construction and its literal guards use only the child
coordinates of the finite wide action list. The result types retain the
full tables as indices, so acceptance and returned centers are compared
after projecting away proof fields. -/

namespace EditApproximation

open Finset

theorem rationalWidePrefixCost_congr_child {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny) (states : Fin M → TargetInterval ny)
    (left right : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ)
    (heq : ∀ i, left i (states i) = right i (states i)) :
    rationalWidePrefixCost parent r states left j p =
      rationalWidePrefixCost parent r states right j p := by
  unfold rationalWidePrefixCost
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [heq i]

theorem rationalWidePrefixMinimum_congr_child {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (left right : Fin M → TargetInterval ny → ℚ) (j : ℕ) (p : ℚ)
    (heq : ∀ action ∈ actions, ∀ i, left i (action i) = right i (action i)) :
    rationalWidePrefixMinimum parent r actions hne left j p =
      rationalWidePrefixMinimum parent r actions hne right j p := by
  have hcost (action) (ha : action ∈ actions) :=
    rationalWidePrefixCost_congr_child parent r action left right j p (heq action ha)
  unfold rationalWidePrefixMinimum
  rw [hcost _ (List.head_mem hne)]
  congr 1
  exact List.map_congr_left hcost

theorem rationalWideActionMinimum_congr_child {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny) (b P : ℕ)
    (hne : wideActionList M parent r b P ≠ [])
    (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, left i (action i) = right i (action i)) :
    rationalWideActionMinimum parent r b P hne left =
      rationalWideActionMinimum parent r b P hne right := by
  have hcost (action) (ha : action ∈ wideActionList M parent r b P) :
      rationalEndpointActionValue r action left = rationalEndpointActionValue r action right := by
    unfold rationalEndpointActionValue
    congr 1
    exact sum_congr rfl (fun i hi => heq action ha i)
  unfold rationalWideActionMinimum
  rw [hcost _ (List.head_mem hne)]
  congr 1
  exact List.map_congr_left hcost

theorem computedBandActions_congr_child {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, left i (action i) = right i (action i)) :
    computedBandActions parent r b P tau theta velocity left =
      computedBandActions parent r b P tau theta velocity right := by
  unfold computedBandActions
  dsimp only
  split_ifs with hnonempty hvelocity
  · rfl
  · have hprefix (j : ℕ) (p : ℚ) := rationalWidePrefixMinimum_congr_child parent r
      (wideActionList M parent r b P) hnonempty left right j p heq
    simp only [bandActionPredicate, hprefix]
  · rfl

theorem representativeBandActions_congr_child {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (left right : Fin M → TargetInterval target.length → ℚ)
    (heq : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, left i (action i) = right i (action i)) :
    representativeBandActions source target parent r b P tau theta left =
      representativeBandActions source target parent r b P tau theta right := by
  by_cases hnonempty : wideActionList M parent r b P = []
  · simp only [representativeBandActions, dite_eq_left hnonempty]
  · simp only [representativeBandActions, dite_eq_right hnonempty]
    rw [rationalWideActionMinimum_congr_child parent r b P hnonempty left right heq]
    split_ifs
    · exact computedBandActions_congr_child parent r b P tau theta _ left right heq
    · rfl

theorem bandChildEnvelope_congr_initial {ny M : ℕ} (b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ band, ∀ i, left i (action i) = right i (action i)) :
    bandChildEnvelope b band left = bandChildEnvelope b band right := by
  funext i
  have hmap : band.map (fun action => left i (action i)) =
      band.map (fun action => right i (action i)) :=
    List.map_congr_left (fun action ha => heq action ha i)
  simp only [bandChildEnvelope, hmap]

theorem bandRoundSpacing_congr_initial {ny M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ band, ∀ i, left i (action i) = right i (action i)) :
    bandRoundSpacing exponent b band left = bandRoundSpacing exponent b band right := by
  funext i
  have hmap : band.map (fun action => left i (action i)) =
      band.map (fun action => right i (action i)) :=
    List.map_congr_left (fun action ha => heq action ha i)
  simp only [bandRoundSpacing, bandEnvelopeExponent, hmap]

theorem canonicalRoundedBandAction_congr_initial {ny M : ℕ} (exponent b : ℕ)
    (band : List (Fin M → TargetInterval ny)) (hne : band ≠ [])
    (left right : Fin M → TargetInterval ny → ℚ)
    (heq : ∀ action ∈ band, ∀ i, left i (action i) = right i (action i)) :
    canonicalRoundedBandAction exponent b band hne left =
      canonicalRoundedBandAction exponent b band hne right := by
  unfold canonicalRoundedBandAction roundedBandAction
  rw [bandRoundSpacing_congr_initial exponent b band left right heq]

theorem representativeBandEnvelope_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    bandChildEnvelope b (representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial =
    bandChildEnvelope b (representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child') initial' := by
  rw [← representativeBandActions_congr_child source target parent r b P tau _ child child' hchild]
  apply bandChildEnvelope_congr_initial
  intro action ha i
  exact hinitial action
    (representativeBandActions_wide source target parent r b P tau _ child action ha) i

theorem testUnskippedBand_isSome_iff {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (b P exponent : ℕ) (tau F : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) (r : TargetInterval target.length) :
    (testUnskippedBand source target parent b P exponent tau F child initial r).isSome = true ↔
      ∃ hne : representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child ≠ [],
        (∑ i, bandChildEnvelope b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial i) ≤ 64 * F * b ∧
        canonicalRoundedBandAction exponent b (representativeBandActions source target parent r b P tau
          ((2 : ℚ) ^ (-(exponent : ℤ))) child) hne initial ∈ wideActionList M parent r b P ∧
        ∀ i, |rationalStateGap
          (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target
          (canonicalRoundedBandAction exponent b (representativeBandActions source target parent r b P tau
            ((2 : ℚ) ^ (-(exponent : ℤ))) child) hne initial i)| ≤
              2 * bandChildEnvelope b (representativeBandActions source target parent r b P tau
                ((2 : ℚ) ^ (-(exponent : ℤ))) child) initial i := by
  unfold testUnskippedBand
  dsimp only
  split_ifs with hband hsum hwide hgap
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨hne, _⟩
    exact hne hband
  · constructor
    · intro _
      exact ⟨hband, hsum, hwide, hgap⟩
    · intro _
      rfl
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨hne, _, _, hg⟩
    exact hgap hg
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨hne, _, hw, _⟩
    exact hwide hw
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨hne, hs, _⟩
    exact hsum hs

theorem testUnskippedBand_isSome_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau F : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    (testUnskippedBand source target parent b P exponent tau F child initial r).isSome =
      (testUnskippedBand source target parent b P exponent tau F child' initial' r).isSome := by
  apply Bool.eq_iff_iff.mpr
  rw [testUnskippedBand_isSome_iff, testUnskippedBand_isSome_iff]
  have hband := representativeBandActions_congr_child source target parent r b P tau
    ((2 : ℚ) ^ (-(exponent : ℤ))) child child' hchild
  rw [← hband]
  have hinitialBand : ∀ action ∈ representativeBandActions source target parent r b P tau
      ((2 : ℚ) ^ (-(exponent : ℤ))) child, ∀ i, initial i (action i) = initial' i (action i) := by
    intro action ha i
    exact hinitial action
      (representativeBandActions_wide source target parent r b P tau _ child action ha) i
  have henv := bandChildEnvelope_congr_initial b _ initial initial' hinitialBand
  have hrounded (hne) := canonicalRoundedBandAction_congr_initial exponent b _ hne
    initial initial' hinitialBand
  simp only [henv, hrounded]

theorem testUnskippedBand_center_projection {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau F : ℚ)
    (child initial : Fin M → TargetInterval target.length → ℚ) :
    (testUnskippedBand source target parent b P exponent tau F child initial r).map
      UnskippedBand.center =
      if (testUnskippedBand source target parent b P exponent tau F child initial r).isSome
      then some r else none := by
  unfold testUnskippedBand
  dsimp only
  split_ifs <;> simp_all

theorem testUnskippedBand_center_congr {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P exponent : ℕ) (tau F : ℚ)
    (child child' initial initial' : Fin M → TargetInterval target.length → ℚ)
    (hchild : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, child i (action i) = child' i (action i))
    (hinitial : ∀ action ∈ wideActionList M parent r b P,
      ∀ i, initial i (action i) = initial' i (action i)) :
    (testUnskippedBand source target parent b P exponent tau F child initial r).map
        UnskippedBand.center =
      (testUnskippedBand source target parent b P exponent tau F child' initial' r).map
        UnskippedBand.center := by
  rw [testUnskippedBand_center_projection, testUnskippedBand_center_projection,
    testUnskippedBand_isSome_congr source target parent r b P exponent tau F
      child child' initial initial' hchild hinitial]

/-- The actual wide coordinates are in the earlier-input cover at every
stored history time. This specializes the congruence premise without
requiring equality of a full child table. -/
theorem wideAction_child_agreement_of_cover {nx ny M : ℕ} (parent : TargetInterval nx)
    (P history b t : ℕ) (r : TargetInterval ny)
    (representatives : List (ℕ × TargetInterval ny)) (hrep : (b, r) ∈ representatives)
    (ht : t < history) (left right : PhysicalChildTables M ny)
    (heq : ∀ i s q, (i, s, q) ∈ wideEarlierInputCover parent P history representatives →
      left i s q = right i s q) :
    ∀ action ∈ wideActionList M parent r b P,
      ∀ i, left i t (action i) = right i t (action i) := by
  intro action ha i
  exact heq i t (action i)
    (wideEarlierInputCover_mem parent P history representatives b r hrep t ht action ha i)

end EditApproximation

end OAI
