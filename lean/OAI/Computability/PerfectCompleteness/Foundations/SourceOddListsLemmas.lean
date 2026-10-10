import OAI.Computability.PerfectCompleteness.Construction.TreeSourceSpaces
import OAI.Computability.PerfectCompleteness.Foundations.CanonicalEdgesLemmas
import OAI.Computability.PerfectCompleteness.Reduction.OddListGame
import OAI.Computability.PerfectCompleteness.Repetition.SourceAmplification

namespace OAI


namespace PerfectCompleteness.SourceOddLists

open SourceClause OddLists
open UniqueGamesTheorem.Foundations.Games

noncomputable section

abbrev Occurrences (m t : Nat) := Fin t → Occurrence m
abbrev LeftLabels (t : Nat) := Fin t → Fin 7
abbrev RightLabels (t : Nat) := Fin t → Bool

def tupleLaw (m t : Nat) [NeZero m] : FiniteDistribution (Occurrences m t) :=
  (FiniteDistribution.uniform (Occurrence m)).iid t

def left {m t : Nat} (e : Occurrences m t) : Fin t → Fin m :=
  fun i => (e i).1

def right {n m t : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrences m t) : Fin t → Fin n :=
  fun i => occurrenceVariable clauses (e i)

def projection {n m t : Nat} (clauses : Fin m → NormalizedClause n)
    (e : Occurrences m t) (a : LeftLabels t) : RightLabels t :=
  fun i => SourceGame.projection clauses (e i) (a i)

def base {n m : Nat} [NeZero m] (clauses : Fin m → NormalizedClause n) (t : Nat) :
    OccurrenceGame (Occurrences m t) (Fin t → Fin m) (Fin t → Fin n)
      (LeftLabels t) (RightLabels t) :=
  OddListGame.base (tupleLaw m t) left (right clauses) (projection clauses)

theorem base_eq_repetition {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (t : Nat) :
    base clauses t = (SourceGame.game clauses).repetition t := by
  unfold base OddListGame.base tupleLaw left right projection SourceGame.game
  unfold OccurrenceGame.ofProjection OccurrenceGame.repetition
  congr 1
  funext e a b
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact congrFun h
  · intro h
    exact funext h

theorem base_endpointDetermined {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (t : Nat) :
    (base clauses t).EndpointDetermined := by
  rw [base_eq_repetition]
  exact OccurrenceGame.EndpointPresentation.determined
    ((SourceGame.game clauses).repetition t)
    (OccurrenceGame.EndpointPresentation.repetition
      (SourceGame.game clauses) (SourceGame.presentation clauses) t)

def game (s : Nat) {n m : Nat} [NeZero m]
    (clauses : Fin m → NormalizedClause n) (t : Nat) :
    OccurrenceGame (Occurrences m t) (Fin t → Fin m) (Fin t → Fin n)
      (OddList s (LeftLabels t)) (OddList s (RightLabels t)) :=
  OddListGame.game s (tupleLaw m t) left (right clauses) (projection clauses)

def tolerance (s : Nat) : ℚ := 1 / (2 * (s : ℚ) ^ 2)

theorem tolerance_positive (s : Nat) [NeZero s] : 0 < tolerance s := by
  have hs : (0 : ℚ) < s := Nat.cast_pos.mpr (Nat.pos_of_neZero s)
  unfold tolerance
  positivity

def repetitionLength (γ : ℚ) (s : Nat) [NeZero s]
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : Nat :=
  SourceAmplification.repetitionLength γ (tolerance s) hγ hγ1 (tolerance_positive s)

theorem repetitionLength_positive (γ : ℚ) (s : Nat) [NeZero s]
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) : 0 < repetitionLength γ s hγ hγ1 :=
  (SourceAmplification.repetitionLength_spec γ (tolerance s)
    hγ hγ1 (tolerance_positive s)).1

theorem amplified_base_gap {n m s : Nat} [NeZero m] [NeZero s]
    (clauses : Fin m → NormalizedClause n) (γ : ℚ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (gap : SourceAmplification.ClauseGap clauses γ) :
    (s : ℝ) ^ 2 * (base clauses (repetitionLength γ s hγ hγ1)).value ≤ 1 / 2 := by
  rw [base_eq_repetition]
  have h : ((SourceGame.game clauses).repetition (repetitionLength γ s hγ hγ1)).value <
      (tolerance s : ℝ) :=
    SourceAmplification.repeated_source_value_lt clauses γ (tolerance s)
      hγ hγ1 (tolerance_positive s) gap
  have hcast : (tolerance s : ℝ) = 1 / (2 * (s : ℝ) ^ 2) := by
    simp only [tolerance, Rat.cast_div, Rat.cast_one, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast]
  rw [hcast] at h
  have hspos : (0 : ℝ) < s := Nat.cast_pos.mpr (Nat.pos_of_neZero s)
  have hs : 0 < (s : ℝ) ^ 2 := pow_pos hspos 2
  have hscaled := mul_lt_mul_of_pos_left h hs
  have hcancel : (s : ℝ) ^ 2 * (1 / (2 * (s : ℝ) ^ 2)) = 1 / 2 := by
    field_simp [ne_of_gt hspos]
  exact (hscaled.trans_eq hcancel).le

def alphabetLog (s t : Nat) : ℝ :=
  UniqueGamesTheorem.Foundations.Repetition.logTwo
    ((Fintype.card (OddList s (LeftLabels t)) : ℝ) *
      (Fintype.card (OddList s (RightLabels t)) : ℝ))

theorem exists_alphabet_budget (s t : Nat) :
    ∃ L : Nat, 0 < L ∧ alphabetLog s t ≤ L := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max (alphabetLog s t) 0)
  refine ⟨L, ?_, (le_max_left _ _).trans hL.le⟩
  have hpos : (0 : ℝ) < L := (le_max_right _ _).trans_lt hL
  exact_mod_cast hpos

theorem value_le_half {n m s : Nat} [NeZero m] [NeZero s]
    (clauses : Fin m → NormalizedClause n) (γ : ℚ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (gap : SourceAmplification.ClauseGap clauses γ) :
    (game s clauses (repetitionLength γ s hγ hγ1)).value ≤ 1 / 2 := by
  exact (OddListGame.value_le (s := s)
    (tupleLaw m (repetitionLength γ s hγ hγ1)) left (right clauses) (projection clauses)).trans
      (amplified_base_gap clauses γ hγ hγ1 gap)

theorem repetition_halfRate {n m s L : Nat} [NeZero m] [NeZero s]
    (clauses : Fin m → NormalizedClause n) (γ : ℚ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (gap : SourceAmplification.ClauseGap clauses γ)
    (hL : 0 < L) (alphabet : alphabetLog s (repetitionLength γ s hγ hγ1) ≤ L)
    (k : Nat) :
    ((game s clauses (repetitionLength γ s hγ hγ1)).repetition k).value ≤
      (RepetitionRate.halfRate L : ℝ) ^ k :=
  OddListGame.repetition_halfRate (s := s) (L := L)
    (tupleLaw m (repetitionLength γ s hγ hγ1)) left (right clauses) (projection clauses)
    (base_endpointDetermined clauses (repetitionLength γ s hγ hγ1))
    (amplified_base_gap clauses γ hγ hγ1 gap) hL alphabet k

end
end PerfectCompleteness.SourceOddLists



namespace PerfectCompleteness.SourceAnswerEquiv

open SourceClause

variable {v m t : Nat}

def clauseAnswerEquiv (signs : Triple) : ClauseSupport.Answer signs ≃ Fin 7 where
  toFun a := SourceGame.encodeLabel signs a.val ((mem_satisfyingTriples signs a.val).mp a.property)
  invFun a := ⟨SourceGame.decodeLabel signs a, SourceGame.decodeLabel_mem signs a⟩
  left_inv a := by
    apply Subtype.ext
    exact SourceGame.decodeLabel_encodeLabel signs a.val
      ((mem_satisfyingTriples signs a.val).mp a.property)
  right_inv a := by
    apply SourceGame.decodeLabel_injective signs
    exact SourceGame.decodeLabel_encodeLabel signs (SourceGame.decodeLabel signs a)
      (SourceGame.decodeLabel_legal signs a)

@[simp] theorem clauseAnswerEquiv_symm_val (signs : Triple) (a : Fin 7) :
    ((clauseAnswerEquiv signs).symm a).val = SourceGame.decodeLabel signs a := rfl

@[simp] theorem clauseAnswerEquiv_decode (signs : Triple) (a : ClauseSupport.Answer signs) :
    SourceGame.decodeLabel signs (clauseAnswerEquiv signs a) = a.val :=
  SourceGame.decodeLabel_encodeLabel signs a.val
    ((mem_satisfyingTriples signs a.val).mp a.property)

def leftSlots (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin m) :
    Fin t → MixedSupport.Slot :=
  fun i => SourceKeys.slot clauses (.clause (question i))

def rightSlots (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin v) :
    Fin t → MixedSupport.Slot :=
  fun i => SourceKeys.slot clauses (.variable (question i))

abbrev LeftDomain (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin m) :=
  MixedSupport.Assignment (leftSlots clauses question)

abbrev RightDomain (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin v) :=
  MixedSupport.Assignment (rightSlots clauses question)

instance rightDomainDecidableEq (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin v) : DecidableEq (RightDomain clauses question) :=
  inferInstanceAs (DecidableEq (Fin t → Bool))

def leftEquiv (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin m) :
    LeftDomain clauses question ≃ SourceOddLists.LeftLabels t where
  toFun a i := clauseAnswerEquiv (clauses (question i)).signs (a i)
  invFun a i := (clauseAnswerEquiv (clauses (question i)).signs).symm (a i)
  left_inv a := by
    funext i
    exact (clauseAnswerEquiv (clauses (question i)).signs).symm_apply_apply (a i)
  right_inv a := by
    funext i
    exact (clauseAnswerEquiv (clauses (question i)).signs).apply_symm_apply (a i)

def rightEquiv (clauses : Fin m → NormalizedClause v) (question : Fin t → Fin v) :
    RightDomain clauses question ≃ SourceOddLists.RightLabels t :=
  Equiv.refl _

@[simp] theorem leftEquiv_apply (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin m) (a : LeftDomain clauses question) (i : Fin t) :
    leftEquiv clauses question a i = clauseAnswerEquiv (clauses (question i)).signs (a i) := rfl

@[simp] theorem leftEquiv_symm_apply (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin m) (a : SourceOddLists.LeftLabels t) (i : Fin t) :
    (leftEquiv clauses question).symm a i =
      (clauseAnswerEquiv (clauses (question i)).signs).symm (a i) := rfl

@[simp] theorem rightEquiv_apply (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin v) (a : RightDomain clauses question) :
    rightEquiv clauses question a = a := rfl

def slotProjection (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t) :
    ∀ i, MixedSupport.Projection (leftSlots clauses (SourceOddLists.left e) i)
      (rightSlots clauses (SourceOddLists.right clauses e) i) :=
  fun i => (SourceKeys.Step.select (clauses := clauses) (e i).1 (e i).2).projection

def actualProjection (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t) :
    LeftDomain clauses (SourceOddLists.left e) →
      RightDomain clauses (SourceOddLists.right clauses e) :=
  MixedSupport.projectionMap (slotProjection clauses e)

@[simp] theorem actualProjection_apply (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t)
    (a : LeftDomain clauses (SourceOddLists.left e)) (i : Fin t) :
    actualProjection clauses e a i = (a i).val.at (e i).2 := rfl

theorem projection_decode (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t) (a : SourceOddLists.LeftLabels t) :
    actualProjection clauses e ((leftEquiv clauses (SourceOddLists.left e)).symm a) =
      (rightEquiv clauses (SourceOddLists.right clauses e)).symm
        (SourceOddLists.projection clauses e a) := rfl

theorem projection_encode (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t)
    (a : LeftDomain clauses (SourceOddLists.left e)) :
    rightEquiv clauses (SourceOddLists.right clauses e) (actualProjection clauses e a) =
      SourceOddLists.projection clauses e (leftEquiv clauses (SourceOddLists.left e) a) := by
  have h := projection_decode clauses e (leftEquiv clauses (SourceOddLists.left e) a)
  rw [Equiv.symm_apply_apply] at h
  exact congrArg (rightEquiv clauses (SourceOddLists.right clauses e)) h

def encodeOddList {s : Nat} (clauses : Fin m → NormalizedClause v)
    (question : Fin t → Fin m) (L : OddLists.OddList s (LeftDomain clauses question)) :
    OddLists.OddList s (SourceOddLists.LeftLabels t) :=
  ⟨L.val.map (leftEquiv clauses question).toEmbedding, by
    simpa only [Finset.card_map] using L.property⟩

theorem encodeOddList_projection {s : Nat} (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t)
    (L : OddLists.OddList s (LeftDomain clauses (SourceOddLists.left e))) :
    OddLists.OddList.map (SourceOddLists.projection clauses e)
      (encodeOddList clauses (SourceOddLists.left e) L) =
      OddLists.OddList.map (actualProjection clauses e) L := by
  classical
  let nativeProjection : LeftDomain clauses (SourceOddLists.left e) →
      SourceOddLists.RightLabels t := actualProjection clauses e
  change OddLists.OddList.map (SourceOddLists.projection clauses e)
      (encodeOddList clauses (SourceOddLists.left e) L) =
    OddLists.OddList.map nativeProjection L
  have hcomm : ∀ a : LeftDomain clauses (SourceOddLists.left e),
      SourceOddLists.projection clauses e (leftEquiv clauses (SourceOddLists.left e) a) =
        nativeProjection a := fun a => (projection_encode clauses e a).symm
  apply Subtype.ext
  ext b
  change b ∈ OddLists.parityPushforward (SourceOddLists.projection clauses e)
      (L.val.map (leftEquiv clauses (SourceOddLists.left e)).toEmbedding) ↔
    b ∈ OddLists.parityPushforward nativeProjection L.val
  have hfiber :
      (L.val.map (leftEquiv clauses (SourceOddLists.left e)).toEmbedding).filter
          (fun a => SourceOddLists.projection clauses e a = b) =
        (L.val.filter (fun a => nativeProjection a = b)).map
          (leftEquiv clauses (SourceOddLists.left e)).toEmbedding := by
    rw [Finset.filter_map]
    apply congrArg (fun K : Finset (LeftDomain clauses (SourceOddLists.left e)) =>
      K.map (leftEquiv clauses (SourceOddLists.left e)).toEmbedding)
    ext a
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro ha
      exact ⟨ha.1, (hcomm a).symm.trans ha.2⟩
    · intro ha
      exact ⟨ha.1, (hcomm a).trans ha.2⟩
  rw [OddLists.mem_parityPushforward, OddLists.mem_parityPushforward,
    hfiber, Finset.card_map]

theorem encodeOddList_accepted {s : Nat} (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t)
    (L : OddLists.OddList s (LeftDomain clauses (SourceOddLists.left e)))
    (R : OddLists.OddList s (RightDomain clauses (SourceOddLists.right clauses e)))
    (accepted : OddLists.OddList.map (actualProjection clauses e) L = R) :
    OddLists.OddList.map (SourceOddLists.projection clauses e)
      (encodeOddList clauses (SourceOddLists.left e) L) = R :=
  (encodeOddList_projection clauses e L).trans accepted


variable {branch : Nat → Nat} {n : Nat}

def leftTreeSlots (clauses : Fin m → NormalizedClause v)
    (questions : RecursiveSpaces.Slots branch n → Fin t → Fin m) :
    RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot :=
  fun s => leftSlots clauses (questions s)

def rightTreeSlots (clauses : Fin m → NormalizedClause v)
    (questions : RecursiveSpaces.Slots branch n → Fin t → Fin v) :
    RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot :=
  fun s => rightSlots clauses (questions s)

def leftLeafEquiv (clauses : Fin m → NormalizedClause v)
    (questions : RecursiveSpaces.Slots branch n → Fin t → Fin m)
    (s : RecursiveSpaces.Slots branch n) :
    TreeSourceSpaces.LeafDomain (leftTreeSlots clauses questions) s ≃
      SourceOddLists.LeftLabels t :=
  leftEquiv clauses (questions s)

def rightLeafEquiv (clauses : Fin m → NormalizedClause v)
    (questions : RecursiveSpaces.Slots branch n → Fin t → Fin v)
    (s : RecursiveSpaces.Slots branch n) :
    TreeSourceSpaces.LeafDomain (rightTreeSlots clauses questions) s ≃
      SourceOddLists.RightLabels t :=
  rightEquiv clauses (questions s)

theorem leaf_projection_encode (clauses : Fin m → NormalizedClause v)
    (occurrences : RecursiveSpaces.Slots branch n → SourceOddLists.Occurrences m t)
    (s : RecursiveSpaces.Slots branch n)
    (a : TreeSourceSpaces.LeafDomain
      (leftTreeSlots clauses (fun j => SourceOddLists.left (occurrences j))) s) :
    rightLeafEquiv clauses (fun j => SourceOddLists.right clauses (occurrences j)) s
      (MixedSupport.projectionMap (slotProjection clauses (occurrences s)) a) =
      SourceOddLists.projection clauses (occurrences s)
        (leftLeafEquiv clauses (fun j => SourceOddLists.left (occurrences j)) s a) :=
  projection_encode clauses (occurrences s) a


end PerfectCompleteness.SourceAnswerEquiv

end OAI
