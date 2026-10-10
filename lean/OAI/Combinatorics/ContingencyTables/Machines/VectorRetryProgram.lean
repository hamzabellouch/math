import OAI.Combinatorics.ContingencyTables.Machines.RetryNumeratorProgram

namespace OAI

/-! # First-success propagation of an entire vector of integer counts -/

namespace ContingencyTables.VectorRetryPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

/-- Trial marker, denominator, success counts, fallback index. -/
abbrev Input := (List Bool×ℕ)×(List ℕ×ℕ)

def failure (z : Input) : ℕ := z.1.2-z.2.1.sum

def failureRealizer : Realizer failure :=
  composition (pair (composition first second)
    (composition (composition second first) listSum)) subtract

lemma polynomial_failure : PolynomialTime failureRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_listSum)) polynomial_subtract

def entryInput (z : Input×ℕ) : RetryNumeratorPrograms.Input :=
  (z.1.1.1,((z.1.1.2,failure z.1),(z.1.2.1.getD z.2 0,decide (z.2=z.1.2.2))))

def entryInputRealizer : Realizer entryInput := by
  let markers : Realizer (fun z : Input×ℕ => z.1.1.1) :=
    composition (composition first first) first
  let denominator : Realizer (fun z : Input×ℕ => z.1.1.2) :=
    composition (composition first first) second
  let success : Realizer (fun z : Input×ℕ => z.1.2.1.getD z.2 0) :=
    composition (pair (composition (composition first second) first) second) (getDFast 0)
  let hit : Realizer (fun z : Input×ℕ => decide (z.2=z.1.2.2)) :=
    composition (pair second (composition (composition first second) second)) natEqual
  exact pair markers (pair (pair denominator (composition first failureRealizer)) (pair success hit))

lemma polynomial_entryInput : PolynomialTime entryInputRealizer := by
  unfold entryInputRealizer
  exact polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition polynomial_first polynomial_failure))
      (polynomial_pair (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
        polynomial_second) (polynomial_getDFast 0))
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
            polynomial_second)) polynomial_natEqual)))

def indices (z : Input) : List ℕ := List.range z.2.1.length

def indicesRealizer : Realizer indices :=
  composition (composition (composition second first) listLength) range

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition (polynomial_composition
    polynomial_second polynomial_first) polynomial_listLength) Polynomial.X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.2.1).trans ((weight_fst z.2).trans (weight_snd z))

def counts (z : Input) : List ℕ :=
  (indices z).map (fun j => RetryNumeratorPrograms.count (entryInput (z,j)))

def countsRealizer : Realizer counts :=
  composition (pair identity indicesRealizer)
    (mapWith (composition entryInputRealizer RetryNumeratorPrograms.countRealizer))

/-- Binary vector propagation uses time polynomial in the success-vector
encoding and in the supplied number of trial markers. -/
theorem polynomial_counts : PolynomialTime countsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith (polynomial_composition polynomial_entryInput
      RetryNumeratorPrograms.polynomial_count))

lemma failure_ofFn {r Q : ℕ} (p : IntegerLaw (Option (Fin r)) Q)
    (xs : List Bool) (fallback : Fin r) :
    failure ((xs,Q),(List.ofFn (fun a => p.count (some a)),fallback.val))=p.count none := by
  have ht := p.total
  rw [Fintype.sum_option] at ht
  simp only [failure,List.sum_ofFn]
  omega

theorem counts_actual {r Q : ℕ} (p : IntegerLaw (Option (Fin r)) Q)
    (xs : List Bool) (fallback : Fin r) :
    counts ((xs,Q),(List.ofFn (fun a => p.count (some a)),fallback.val))=
      List.ofFn ((p.retry fallback xs.length).count) := by
  unfold counts indices
  rw [List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro j hj _
    have hjr : j<r := by simpa only [List.length_map,List.length_range] using hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    unfold entryInput
    rw [failure_ofFn]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hjr,dite_true,
      Option.getD_some]
    rw [RetryNumeratorPrograms.count_eq]
    have hhit : (j=fallback.val) ↔ (⟨j,hjr⟩ : Fin r)=fallback :=
      ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp only [decide_eq_true_eq,hhit]
    exact RetryNumeratorPrograms.recurrence_retry p fallback ⟨j,hjr⟩ xs.length

end ContingencyTables.VectorRetryPrograms

end OAI
