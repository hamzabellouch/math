import OAI.Combinatorics.EditApproximation.Geometry.OccurrencePrefix
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalInitial
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! A symbol dictionary of cached position tries. The target is enumerated
once; interval occurrence queries use two logarithmic prefix counts. -/

namespace EditApproximation

def occurrencePrefixCount : List (ℕ × ℕ) → ℕ → ℕ → ℕ
  | [], _, _ => 0
  | e :: es, a, t => occurrencePrefixCount es a t + if e.1 = a ∧ e.2 < t then 1 else 0

def occurrenceRangeCount : List (ℕ × ℕ) → ℕ → ℕ → ℕ → ℕ
  | [], _, _, _ => 0
  | e :: es, a, lo, hi => occurrenceRangeCount es a lo hi +
      if e.1 = a ∧ lo ≤ e.2 ∧ e.2 < hi then 1 else 0

theorem occurrencePrefixCount_sub (entries : List (ℕ × ℕ)) (a lo hi : ℕ) (h : lo ≤ hi) :
    occurrencePrefixCount entries a hi - occurrencePrefixCount entries a lo =
      occurrenceRangeCount entries a lo hi := by
  have hall : occurrencePrefixCount entries a lo + occurrenceRangeCount entries a lo hi =
      occurrencePrefixCount entries a hi := by
    induction entries with
    | nil => rfl
    | cons e es ih =>
      simp only [occurrencePrefixCount, occurrenceRangeCount]
      by_cases ha : e.1 = a <;> by_cases hlo : e.2 < lo <;>
        by_cases hhi : e.2 < hi <;> by_cases hge : lo ≤ e.2 <;>
        simp only [ha, hlo, hhi, hge, true_and, false_and, and_self, ite_true, ite_false] <;> omega
  omega

theorem occurrenceRangeCount_pos (entries : List (ℕ × ℕ)) (a lo hi : ℕ) :
    0 < occurrenceRangeCount entries a lo hi ↔
      ∃ e ∈ entries, e.1 = a ∧ lo ≤ e.2 ∧ e.2 < hi := by
  induction entries with
  | nil => simp only [occurrenceRangeCount, lt_self_iff_false, List.not_mem_nil, false_and, exists_false]
  | cons e es ih =>
    rw [occurrenceRangeCount]
    by_cases he : e.1 = a ∧ lo ≤ e.2 ∧ e.2 < hi
    · rw [ite_eq_left he]
      constructor
      · intro _
        exact ⟨e, List.mem_cons_self, he⟩
      · intro _
        omega
    · rw [ite_eq_right he, add_zero, ih]
      constructor
      · rintro ⟨f, hf, hp⟩
        exact ⟨f, List.mem_cons_of_mem e hf, hp⟩
      · rintro ⟨f, hf, hp⟩
        rcases List.mem_cons.mp hf with hfe | hf
        · subst f
          exact False.elim (he hp)
        · exact ⟨f, hf, hp⟩



def occurrencePrefix (table : BinaryMemo PositionCounts) (symbolBits positionBits a t : ℕ) : ℕ :=
  ((table.lookup (binaryMemoKey symbolBits a)).getD .empty).prefixCount positionBits t

theorem occurrenceBuild_prefix (symbolBits positionBits : ℕ) (entries : List (ℕ × ℕ))
    (hentries : ∀ e ∈ entries, e.1 < 2 ^ symbolBits ∧ e.2 < 2 ^ positionBits)
    (a t : ℕ) (ha : a < 2 ^ symbolBits) :
    occurrencePrefix (occurrenceBuild symbolBits positionBits entries) symbolBits positionBits a t =
      occurrencePrefixCount entries a t := by
  induction entries with
  | nil => simp only [occurrenceBuild, occurrencePrefix, BinaryMemo.lookup_empty,
      Option.getD_none, PositionCounts.prefix_empty, occurrencePrefixCount]
  | cons e es ih =>
    have he := hentries e (by simp only [List.mem_cons, true_or])
    have hes : ∀ e ∈ es, e.1 < 2 ^ symbolBits ∧ e.2 < 2 ^ positionBits :=
      fun e hm => hentries e (List.mem_cons_of_mem _ hm)
    simp only [occurrenceBuild, occurrencePrefix]
    rw [binaryMemo_lookup_insert _ symbolBits e.1 a he.1 ha]
    by_cases heq : a = e.1
    · subst a
      simp only [ite_true, Option.getD_some, PositionCounts.prefix_add _ _ _ _ he.2]
      have hi := ih hes
      unfold occurrencePrefix at hi
      rw [hi]
      simp only [occurrencePrefixCount, true_and]
    · simp only [heq, ite_false]
      have hi := ih hes
      unfold occurrencePrefix at hi
      rw [hi]
      simp only [occurrencePrefixCount, Ne.symm heq, false_and, ite_false, add_zero]

def occurrenceQuery (table : BinaryMemo PositionCounts) (symbolBits positionBits a lo hi : ℕ) : Bool :=
  decide (occurrencePrefix table symbolBits positionBits a lo <
    occurrencePrefix table symbolBits positionBits a hi)

theorem occurrenceQuery_build (symbolBits positionBits : ℕ) (entries : List (ℕ × ℕ))
    (hentries : ∀ e ∈ entries, e.1 < 2 ^ symbolBits ∧ e.2 < 2 ^ positionBits)
    (a lo hi : ℕ) (ha : a < 2 ^ symbolBits) (h : lo ≤ hi) :
    occurrenceQuery (occurrenceBuild symbolBits positionBits entries) symbolBits positionBits a lo hi = true ↔
      ∃ e ∈ entries, e.1 = a ∧ lo ≤ e.2 ∧ e.2 < hi := by
  rw [occurrenceQuery, decide_eq_true_eq, occurrenceBuild_prefix _ _ _ hentries _ _ ha,
    occurrenceBuild_prefix _ _ _ hentries _ _ ha]
  rw [← occurrenceRangeCount_pos, ← occurrencePrefixCount_sub entries a lo hi h]
  omega



theorem occurrenceBuildWithWork_spec (symbolBits positionBits : ℕ) (entries : List (ℕ × ℕ)) :
    occurrenceBuildWithWork symbolBits positionBits entries =
      (occurrenceBuild symbolBits positionBits entries,
        entries.length * (3 * symbolBits + 2 * positionBits + 5)) := by
  induction entries with
  | nil => simp only [occurrenceBuildWithWork, occurrenceBuild, List.length_nil, zero_mul]
  | cons e es ih =>
    simp only [occurrenceBuildWithWork, ih, BinaryMemo.lookupCosted_spec,
      PositionCounts.addWithWork_spec, BinaryMemo.insertCosted_spec,
      binaryMemoKey_length, occurrenceBuild, List.length_cons]
    congr 1
    ring



theorem occurrenceQueryWithWork_spec (table : BinaryMemo PositionCounts)
    (symbolBits positionBits a lo hi : ℕ) :
    occurrenceQueryWithWork table symbolBits positionBits a lo hi =
      (occurrenceQuery table symbolBits positionBits a lo hi, 2 * symbolBits + 4 * positionBits + 5) := by
  simp only [occurrenceQueryWithWork, BinaryMemo.lookupCosted_spec,
    PositionCounts.prefixWithWork_spec, binaryMemoKey_length, occurrenceQuery, occurrencePrefix]
  congr 1
  ring

/-- Converting the input list to its indexed entries is done only during
preprocessing. Subsequent queries use endpoints and the dictionary. -/
theorem occurrenceQuery_target (symbolBits positionBits : ℕ) (target : List ℕ)
    (hsymbol : ∀ a ∈ target, a < 2 ^ symbolBits) (hposition : target.length ≤ 2 ^ positionBits)
    (a lo hi : ℕ) (ha : a < 2 ^ symbolBits) (hlo : lo ≤ hi) (hhi : hi ≤ target.length) :
    occurrenceQuery (occurrenceBuild symbolBits positionBits target.zipIdx)
      symbolBits positionBits a lo hi = true ↔ a ∈ substring target lo hi := by
  have hentries : ∀ e ∈ target.zipIdx, e.1 < 2 ^ symbolBits ∧ e.2 < 2 ^ positionBits := by
    intro e he
    exact ⟨hsymbol e.1 (List.fst_mem_of_mem_zipIdx he),
      (by have h := List.snd_lt_of_mem_zipIdx he; simp only [Nat.add_zero] at h; omega)⟩
  rw [occurrenceQuery_build _ _ _ hentries _ _ _ ha hlo, List.exists_mem_zipIdx']
  simp only [substring, List.mem_drop_iff_getElem, List.length_take, Nat.min_eq_left hhi]
  constructor
  · rintro ⟨i, hi', heq, hil, hih⟩
    refine ⟨i - lo, by omega, ?_⟩
    simpa only [Nat.add_sub_of_le hil, List.getElem_take] using heq
  · rintro ⟨j, hj, heq⟩
    refine ⟨lo + j, by omega, ?_, by omega, by omega⟩
    simpa only [List.getElem_take] using heq

end EditApproximation

end OAI
