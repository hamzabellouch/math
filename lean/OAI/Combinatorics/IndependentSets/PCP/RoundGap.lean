import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.AmplificationRound
import OAI.Combinatorics.IndependentSets.Expansion.PoweringGap

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.RoundGap

open AmplificationRound

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

def poweredLower (epsilon : ℝ) : ℝ :=
  PoweringSoundness.gain (Fintype.card Label) FinalConstants.windowHalf (31 / 32) *
    min (epsilon / (Preprocessing.sizeFactor : ℝ)) FinalConstants.cap

theorem poweredLower_nonnegative (epsilon : ℝ) (he : 0 ≤ epsilon) :
    0 ≤ poweredLower epsilon := by
  have hg := PoweringGap.gain_nonneg (Fintype.card Label)
    FinalConstants.windowHalf (31 / 32) (by norm_num)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  exact mul_nonneg hg (le_min (div_nonneg he hs.le) FinalConstants.cap_positive.le)

theorem powered_count_gap (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label)
    (labeling : Preprocessing.Vertex G → PoweredAlphabet) :
    poweredLower G.gap * (Fintype.card (PoweredDart G) : ℝ) ≤
      ((powered addresses complete G).rejectionCount labeling : ℝ) := by
  let H := Overlay.originalPortGraph (Preprocessing.overlayGraph G)
  have certificate : SpectralReturn.SpectralCertificate
      (PoweringWalks.lazyGraph H) (31 / 32 : ℝ) :=
    Preprocessing.spectral_certificate G
  have lower : ∀ assignment : Preprocessing.Vertex G → Label,
      (G.gap / (Preprocessing.sizeFactor : ℝ)) *
          (Fintype.card (Preprocessing.Vertex G × Preprocessing.Port) : ℝ) ≤
        ((Preprocessing.graph G).rejectionCount assignment : ℝ) :=
    Preprocessing.gap_transfer_real G G.gap G.gap_nonnegative
      ((G.le_gap_iff G.gap).mp le_rfl)
  have hs : (0 : ℝ) < Preprocessing.sizeFactor := by
    exact_mod_cast Preprocessing.sizeFactor_positive
  have h := PoweringGap.uniform_count_gap H (31 / 32) certificate
    (Preprocessing.graph G).accepts (Preprocessing.accepts_reverse G)
    FinalConstants.windowHalf FinalConstants.windowHalf_positive
    (selectors addresses complete G)
    (G.gap / (Preprocessing.sizeFactor : ℝ)) (div_nonneg G.gap_nonnegative hs.le)
    lower labeling
  convert h using 1 <;>
    simp only [poweredLower, powered, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq]
  rfl

theorem amplifies (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) :
    min (2 * G.gap) FinalConstants.cap ≤ (graph addresses complete G).gap := by
  apply ((graph addresses complete G).le_gap_iff _).mpr
  intro labeling
  have hcount := AlphabetGraphBounds.gap_transfer_real (powered addresses complete G)
    (poweredLower G.gap) (poweredLower_nonnegative G.gap G.gap_nonnegative)
    (powered_count_gap addresses complete G) labeling
  have hscalar : min (2 * G.gap) FinalConstants.cap ≤ poweredLower G.gap / 12288 := by
    simpa only [poweredLower, FinalConstants.cap, FinalConstants.walkLength,
      PoweringFinalConstants.center_eq] using
      PoweringFinalConstants.composed_scaled_gap G.gap G.gap_nonnegative
  exact (mul_le_mul_of_nonneg_right hscalar (Nat.cast_nonneg _)).trans hcount

end IndependentSetsGames.Foundations.PCP.RoundGap
namespace IndependentSetsGames.Foundations.PCP.RoundSize

open scoped BigOperators

theorem card_padded_alphabet {D A : Type*} [Fintype D] [DecidableEq D]
    [Fintype A] (t : Nat) :
    Fintype.card (PoweringLabels.PaddedLabel D t A) =
      Fintype.card A ^ (∑ k : Fin (t + 1), Fintype.card D ^ k.val) := by
  simpa only [Nat.card_eq_fintype_card] using
    PoweringLabels.card_paddedLabel (D := D) (A := A) t

theorem card_powered_dart {V D : Type*} [Fintype V] [Fintype D]
    (n : Nat) : Fintype.card (PoweringTest.Dart V D n) =
      Fintype.card V * (2 * Fintype.card D ^ (n + 1)) := by
  simp only [PoweringTest.Dart, PoweringWalks.Walk, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fun, Fintype.card_fin]
  ring

private opaque lockedNat (n : Nat) : {m : Nat // m = n} := ⟨n, rfl⟩

def poweredAlphabetSize : Nat :=
  (lockedNat (64 ^ (∑ k : Fin (FinalConstants.walkLength + 1),
    Preprocessing.degree ^ k.val))).val

def poweredDartFactor : Nat :=
  (lockedNat (2 * Preprocessing.degree ^ (2 * FinalConstants.endpointLength + 1))).val

def sizeFactor : Nat :=
  (lockedNat (AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
    (1 + poweredDartFactor) * ExpanderFamily.growth ^ 2)).val

theorem poweredAlphabetSize_eq : poweredAlphabetSize =
    64 ^ (∑ k : Fin (FinalConstants.walkLength + 1), Preprocessing.degree ^ k.val) :=
  (lockedNat _).property

theorem poweredDartFactor_eq : poweredDartFactor =
    2 * Preprocessing.degree ^ (2 * FinalConstants.endpointLength + 1) :=
  (lockedNat _).property

theorem sizeFactor_eq : sizeFactor = AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
    (1 + poweredDartFactor) * ExpanderFamily.growth ^ 2 :=
  (lockedNat _).property

private theorem coefficient_positive (q d g : Nat) (hg : 0 < g) :
    0 < AlphabetGraphBounds.sizeFactor q * (1 + d) * g ^ 2 := by
  exact Nat.mul_pos (Nat.mul_pos (AlphabetGraphBounds.sizeFactor_positive q)
    (Nat.zero_lt_one.trans_le (Nat.le_add_right 1 d))) (pow_pos hg 2)

theorem poweredAlphabet_card : Fintype.card AmplificationRound.PoweredAlphabet =
    poweredAlphabetSize := by
  have h := PoweringLabels.card_paddedLabel (D := Preprocessing.Port)
    (A := QueryIncidence.Label 6) FinalConstants.walkLength
  change Nat.card AmplificationRound.PoweredAlphabet = _ at h
  simp only [Nat.card_eq_fintype_card, ← Preprocessing.degree_eq_card,
    QueryIncidence.six_query_alphabet] at h
  exact h.trans poweredAlphabetSize_eq.symm

theorem sizeFactor_positive : 0 < sizeFactor := by
  have hG : 0 < ExpanderFamily.growth :=
    Nat.zero_lt_one.trans ExpanderFamily.growth_gt_one
  rw [sizeFactor_eq]
  exact coefficient_positive _ _ _ hG

private theorem factor_total (c v d : Nat) : c * (v + v * d) = c * (1 + d) * v := by
  ring

private theorem nat_card_output_vertex {V E A : Type*}
    [Fintype V] [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A] :
    Nat.card (AlphabetGraphBounds.OutputVertex V E A) =
      Nat.card V * 2 ^ Nat.card A +
        Nat.card E * AlphabetGraphBounds.vertexFactor (Nat.card A) := by
  simpa only [← Nat.card_eq_fintype_card] using
    AlphabetGraphBounds.card_output_vertex (V := V) (E := E) (A := A)

private theorem nat_card_output_dart {E A : Type*}
    [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A] :
    Nat.card (AlphabetGraphBounds.OutputDart E A) =
      Nat.card E * AlphabetGraphBounds.dartFactor (Nat.card A) := by
  simpa only [← Nat.card_eq_fintype_card] using
    AlphabetGraphBounds.card_output_dart (E := E) (A := A)

private theorem nat_card_output_total_le {V E A : Type*}
    [Fintype V] [Fintype E] [Fintype A] [DecidableEq A] [Nonempty A] :
    Nat.card (AlphabetGraphBounds.OutputVertex V E A) +
        Nat.card (AlphabetGraphBounds.OutputDart E A) ≤
      AlphabetGraphBounds.sizeFactor (Nat.card A) * (Nat.card V + Nat.card E) := by
  simpa only [← Nat.card_eq_fintype_card] using
    AlphabetGraphBounds.card_output_total_le (V := V) (E := E) (A := A)

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

omit [DecidableEq E] [Nonempty E] in
theorem poweredDart_card (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.PoweredDart G) =
      Fintype.card (Preprocessing.Vertex G) * poweredDartFactor := by
  have h := card_powered_dart (V := Preprocessing.Vertex G) (D := Preprocessing.Port)
    (2 * FinalConstants.endpointLength)
  rw [← Preprocessing.degree_eq_card] at h
  exact h.trans (congrArg (fun d => Fintype.card (Preprocessing.Vertex G) * d)
    poweredDartFactor_eq.symm)

omit [DecidableEq E] [Nonempty E] in

theorem output_vertex_card (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Vertex G) =
      Fintype.card (Preprocessing.Vertex G) * 2 ^ poweredAlphabetSize +
        (Fintype.card (Preprocessing.Vertex G) * poweredDartFactor) *
          AlphabetGraphBounds.vertexFactor poweredAlphabetSize := by
  have h := nat_card_output_vertex (V := Preprocessing.Vertex G)
    (E := AmplificationRound.PoweredDart G) (A := AmplificationRound.PoweredAlphabet)
  change Nat.card (AmplificationRound.Vertex G) =
    Nat.card (Preprocessing.Vertex G) * 2 ^ Nat.card AmplificationRound.PoweredAlphabet +
      Nat.card (AmplificationRound.PoweredDart G) *
        AlphabetGraphBounds.vertexFactor (Nat.card AmplificationRound.PoweredAlphabet) at h
  simpa only [Nat.card_eq_fintype_card, poweredAlphabet_card, poweredDart_card] using h

omit [DecidableEq E] [Nonempty E] in

theorem output_dart_card (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Dart G) =
      (Fintype.card (Preprocessing.Vertex G) * poweredDartFactor) *
        AlphabetGraphBounds.dartFactor poweredAlphabetSize := by
  have h := nat_card_output_dart (E := AmplificationRound.PoweredDart G)
    (A := AmplificationRound.PoweredAlphabet)
  change Nat.card (AmplificationRound.Dart G) = Nat.card (AmplificationRound.PoweredDart G) *
    AlphabetGraphBounds.dartFactor (Nat.card AmplificationRound.PoweredAlphabet) at h
  simpa only [Nat.card_eq_fintype_card, poweredAlphabet_card, poweredDart_card] using h

omit [DecidableEq E] in
theorem output_total_le_darts (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Vertex G) + Fintype.card (AmplificationRound.Dart G) ≤
      sizeFactor * Fintype.card E := by
  have h := nat_card_output_total_le
    (V := Preprocessing.Vertex G) (E := AmplificationRound.PoweredDart G)
    (A := AmplificationRound.PoweredAlphabet)
  change Nat.card (AmplificationRound.Vertex G) + Nat.card (AmplificationRound.Dart G) ≤
    AlphabetGraphBounds.sizeFactor (Nat.card AmplificationRound.PoweredAlphabet) *
      (Nat.card (Preprocessing.Vertex G) + Nat.card (AmplificationRound.PoweredDart G)) at h
  simp only [Nat.card_eq_fintype_card] at h
  rw [poweredAlphabet_card, poweredDart_card] at h
  calc
    _ ≤ AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
        (Fintype.card (Preprocessing.Vertex G) +
          Fintype.card (Preprocessing.Vertex G) * poweredDartFactor) := h
    _ = (AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
        (1 + poweredDartFactor)) * Fintype.card (Preprocessing.Vertex G) :=
      factor_total _ _ _
    _ ≤ (AlphabetGraphBounds.sizeFactor poweredAlphabetSize *
        (1 + poweredDartFactor)) * (ExpanderFamily.growth ^ 2 * Fintype.card E) :=
      Nat.mul_le_mul_left _ (Preprocessing.vertex_count_le G)
    _ = sizeFactor * Fintype.card E := by
      rw [sizeFactor_eq]
      exact (Nat.mul_assoc _ _ _).symm

omit [DecidableEq E] in
theorem output_total_le (G : ConstraintGraph V E AmplificationRound.Label) :
    Fintype.card (AmplificationRound.Vertex G) + Fintype.card (AmplificationRound.Dart G) ≤
      sizeFactor * (Fintype.card V + Fintype.card E) :=
  (output_total_le_darts G).trans (Nat.mul_le_mul_left _ (Nat.le_add_left _ _))

end IndependentSetsGames.Foundations.PCP.RoundSize

end

end OAI
