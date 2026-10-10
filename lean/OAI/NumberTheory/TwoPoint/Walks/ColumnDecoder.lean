import OAI.NumberTheory.TwoPoint.Walks.ForestPathCounting

namespace OAI

/-!
# Decoding complete column patterns

Three binary streams merge regular segments with omitted runs, mark new
runs, and mark imperfect positions. Representative indices supply omitted
labels and imperfect attachments. All decoding is independent of numerical
primes, quotient coordinates, and padding coefficients.
-/

namespace TwoPointCorrelations

/-- A valid path code determines one family; invalid codes decode to empty
lists. The proven uniqueness makes this choice independent of witnesses. -/
noncomputable def decodeForestPaths {N segments : ℕ}
    (code : ForestPathData.Code N segments) : Fin segments → List ℕ := by
  classical
  exact if h : ∃ d : ForestPathData N segments, d.code = code then h.choose.pattern else fun _ => []

theorem decodeForestPaths_code {N segments : ℕ} (d : ForestPathData N segments) :
    decodeForestPaths d.code = d.pattern := by
  classical
  unfold decodeForestPaths
  split_ifs with h
  · exact ForestPathData.pattern_eq_of_code_eq _ _ h.choose_spec
  · exact (h ⟨d, rfl⟩).elim

inductive CanonicalColumnLabel
  | regular : ℕ → CanonicalColumnLabel
  | omitted : ℕ → CanonicalColumnLabel
  | freshImperfect : ℕ → CanonicalColumnLabel
  deriving DecidableEq

/-- Incidence supports start with a line and alternate line/point. -/
def evenEntries {α : Type*} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: rest => a :: evenEntries rest

/-- A true bit consumes a regular segment; a false bit consumes one
omitted run. Unused trailing bits have no effect. -/
def mergeColumnRuns {α : Type*} : List Bool → List (List α) → List α → List α
  | [], _, _ => []
  | true :: mask, regular, omitted =>
      regular.headD [] ++ mergeColumnRuns mask regular.tail omitted
  | false :: mask, regular, omitted =>
      omitted.head?.toList ++ mergeColumnRuns mask regular omitted.tail

lemma mergeColumnRuns_empty {α : Type*} (mask : List Bool) :
    mergeColumnRuns mask ([] : List (List α)) [] = [] := by
  induction mask with
  | nil => rfl
  | cons b mask ih => cases b <;> simp [mergeColumnRuns, ih]

/-- The binary merge data recover any interleaving of regular segments
and omitted single runs, including padding to a fixed code length. -/
theorem mergeColumnRuns_recover {α : Type*} (pieces : List (List α ⊕ α))
    (padding : List Bool) :
    mergeColumnRuns
      (pieces.map (fun x => match x with | .inl _ => true | .inr _ => false) ++ padding)
      (pieces.filterMap (fun x => match x with | .inl a => some a | .inr _ => none))
      (pieces.filterMap (fun x => match x with | .inl _ => none | .inr a => some a)) =
        pieces.flatMap (fun x => match x with | .inl a => a | .inr a => [a]) := by
  induction pieces with
  | nil => exact mergeColumnRuns_empty padding
  | cons piece pieces ih => cases piece <;> simp [mergeColumnRuns, ih]

/-- The first bit marks an imperfect position; the second begins a new
perfect run. Repetition consumes no extra run label. -/
def expandColumnRuns : List (Bool × Bool) → List CanonicalColumnLabel →
    Option CanonicalColumnLabel → List (Option CanonicalColumnLabel)
  | [], _, _ => []
  | (true, _) :: flags, runs, _ => none :: expandColumnRuns flags runs none
  | (false, true) :: flags, runs, _ =>
      runs.head? :: expandColumnRuns flags runs.tail runs.head?
  | (false, false) :: flags, runs, previous =>
      previous :: expandColumnRuns flags runs previous

theorem expandColumnRuns_repeat (n : ℕ) (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    expandColumnRuns (List.replicate n (false, false) ++ flags) runs previous =
      List.replicate n previous ++ expandColumnRuns flags runs previous := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, expandColumnRuns, ih]

/-- Positive constant-run lengths are recovered from their boundary bits. -/
theorem expandColumnRuns_one_run (n : ℕ) (a : CanonicalColumnLabel)
    (flags : List (Bool × Bool)) (runs : List CanonicalColumnLabel)
    (previous : Option CanonicalColumnLabel) :
    expandColumnRuns ((false, true) :: (List.replicate n (false, false) ++ flags))
        (a :: runs) previous =
      List.replicate (n + 1) (some a) ++ expandColumnRuns flags runs (some a) := by
  simp only [expandColumnRuns, List.head?_cons, List.tail_cons, expandColumnRuns_repeat,
    List.replicate_succ, List.cons_append]

@[simp] theorem expandColumnRuns_length (flags : List (Bool × Bool))
    (runs : List CanonicalColumnLabel) (previous : Option CanonicalColumnLabel) :
    (expandColumnRuns flags runs previous).length = flags.length := by
  induction flags generalizing runs previous with
  | nil => rfl
  | cons flag flags ih => cases flag with
    | mk imperfect newRun =>
      cases imperfect <;> cases newRun <;> simp [expandColumnRuns, ih]

/-- References to represented perfect labels reuse those labels. A
reference to an unrepresented imperfect class uses its first position. -/
def attachImperfectLabels (full : List (Option CanonicalColumnLabel)) :
    List (Option CanonicalColumnLabel) → List ℕ → List CanonicalColumnLabel
  | [], _ => []
  | some a :: rest, refs => a :: attachImperfectLabels full rest refs
  | none :: rest, refs =>
      let j := refs.headD 0
      ((full[j]?.join).getD (.freshImperfect j)) ::
        attachImperfectLabels full rest refs.tail

@[simp] theorem attachImperfectLabels_length (full rest : List (Option CanonicalColumnLabel))
    (refs : List ℕ) : (attachImperfectLabels full rest refs).length = rest.length := by
  induction rest generalizing refs with
  | nil => rfl
  | cons a rest ih => cases a <;> simp [attachImperfectLabels, ih]

abbrev ColumnDecoderCode (N segments omitted imperfect : ℕ) :=
  ForestPathData.Code N segments ×
    (Fin N → Bool) × (Fin N → Bool × Bool) ×
    (Fin omitted → Fin N) × (Fin imperfect → Fin N)

noncomputable def decodeColumnLabels {N segments omitted imperfect : ℕ}
    (code : ColumnDecoderCode N segments omitted imperfect) : List CanonicalColumnLabel :=
  let paths := List.ofFn (fun i => (evenEntries (decodeForestPaths code.1 i)).map
    CanonicalColumnLabel.regular)
  let omittedLabels := List.ofFn (fun i => CanonicalColumnLabel.omitted (code.2.2.2.1 i).val)
  let runs := mergeColumnRuns (List.ofFn code.2.1) paths omittedLabels
  let full := expandColumnRuns (List.ofFn code.2.2.1) runs none
  attachImperfectLabels full full (List.ofFn (fun i => (code.2.2.2.2 i).val))

theorem decodeColumnLabels_length {N segments omitted imperfect : ℕ}
    (code : ColumnDecoderCode N segments omitted imperfect) :
    (decodeColumnLabels code).length = N := by
  simp only [decodeColumnLabels, attachImperfectLabels_length, expandColumnRuns_length,
    List.length_ofFn]

/-- An equality pattern contains no numerical label names. -/
noncomputable def decodeColumnPattern {N segments omitted imperfect : ℕ}
    (code : ColumnDecoderCode N segments omitted imperfect) : Fin N → Fin N → Bool :=
  fun i j => decide ((decodeColumnLabels code).getD i (.freshImperfect 0) =
    (decodeColumnLabels code).getD j (.freshImperfect 0))

theorem card_columnDecoderCode_le (N segments omitted imperfect : ℕ) :
    Fintype.card (ColumnDecoderCode N segments omitted imperfect) ≤
      2 ^ (6 * N + 1) * N ^ (2 * segments + omitted + imperfect) := by
  have h := ForestPathData.card_code_le N segments
  calc
    _ = Fintype.card (ForestPathData.Code N segments) *
        (2 ^ N * ((2 * 2) ^ N * (N ^ omitted * N ^ imperfect))) := by
      simp only [ColumnDecoderCode, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_bool]
    _ ≤ (2 ^ (3 * N + 1) * N ^ (2 * segments)) *
        (2 ^ N * ((2 * 2) ^ N * (N ^ omitted * N ^ imperfect))) :=
      Nat.mul_le_mul_right _ h
    _ = _ := by
      rw [mul_pow]
      calc
        _ = (2 ^ (3 * N + 1) * 2 ^ N * 2 ^ N * 2 ^ N) *
            (N ^ (2 * segments) * N ^ omitted * N ^ imperfect) := by ring
        _ = _ := by
          have hb : 2 ^ (3 * N + 1) * 2 ^ N * 2 ^ N * 2 ^ N =
              2 ^ (6 * N + 1) := by
            rw [← pow_add, ← pow_add, ← pow_add]
            congr 1
            omega
          rw [hb, ← pow_add, ← pow_add]

/-- The decoder's image is one universal, coefficient-independent family
of full column equality patterns. -/
theorem card_decoded_column_patterns (N segments omitted imperfect : ℕ) :
    Nat.card (Set.range (@decodeColumnPattern N segments omitted imperfect)) ≤
      2 ^ (6 * N + 1) * N ^ (2 * segments + omitted + imperfect) := by
  let f := @decodeColumnPattern N segments omitted imperfect
  have h : Nat.card (Set.range f) ≤ Nat.card (ColumnDecoderCode N segments omitted imperfect) :=
    Nat.card_le_card_of_surjective (fun c => (⟨f c, c, rfl⟩ : Set.range f)) (by
      rintro ⟨_, c, rfl⟩
      exact ⟨c, rfl⟩)
  exact h.trans (by
    simpa only [Nat.card_eq_fintype_card] using card_columnDecoderCode_le N segments omitted imperfect)

end TwoPointCorrelations

end OAI
