import OAI.Computability.UniqueGames.PCP.AlphabetGraphLemmas
import OAI.Computability.UniqueGames.PCP.FinalConstantsLemmas

namespace OAI

section

/-!
# Size of the actual fixed amplification round

All constants below depend only on the fixed port alphabet and walk length.
The round itself is the checked preprocessing, powering, and alphabet graph
construction in `AmplificationRound`; no second graph constructor is introduced.
Closed constants are kept symbolic rather than evaluated.
-/

namespace UniqueGamesTheorem.Foundations.PCP.RoundSize

open scoped BigOperators

noncomputable section

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

/- An opaque value with a checked equality prevents the kernel's closed-numeral
evaluator from expanding the astronomical powers. Its body is proved once for
an arbitrary natural number; no axiom or trusted evaluator is introduced.
Only size bounds use these constants, not the graph's algorithm definitions. -/
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
/-- The exact cardinality of the round's output vertex type. -/
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
/-- The exact cardinality of the round's output dart type. -/
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
/-- The actual round has linear total size, even in the old dart count alone. -/
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

end

end UniqueGamesTheorem.Foundations.PCP.RoundSize

end

end OAI
