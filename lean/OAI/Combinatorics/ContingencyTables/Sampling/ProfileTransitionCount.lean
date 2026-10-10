import OAI.Combinatorics.ContingencyTables.Machines.CachedStepCount

namespace OAI

/-! # Counting the short proposal words with a shared dense cache -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped BigOperators Classical

/-- The scalar is the multiplicity of the ignored completion-bit suffix. -/
abbrev TransitionCache := ResidualParameters×(ℕ×List (Option MatrixCode×ℕ))
abbrev TransitionQuery := (TransitionCache×(List ℕ×List ℕ))×List Bool

def cachedWordInput (z : TransitionQuery) : DecisionQuery×List (Option MatrixCode×ℕ) :=
  (((z.1.1.1,z.2),z.1.2),z.1.1.2.2)

def cachedWordInputRealizer : Realizer cachedWordInput := by
  let context : Realizer (fun z : TransitionQuery => z.1.1) := composition first first
  let params := composition context first
  let entries := composition (composition context second) second
  exact pair (pair (pair params second) (composition first second)) entries

lemma polynomial_cachedWordInput : PolynomialTime cachedWordInputRealizer := by
  unfold cachedWordInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first) polynomial_second)
    (polynomial_composition polynomial_first polynomial_second))
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)

def cachedWordCount (z : TransitionQuery) : ℕ :=
  z.1.1.2.1*decisionWeightSum (cachedWordInput z)

def cachedWordCountRealizer : Realizer cachedWordCount := by
  let scalar : Realizer (fun z : TransitionQuery => z.1.1.2.1) :=
    composition (composition (composition first first) second) first
  let value := composition cachedWordInputRealizer decisionWeightSumRealizer
  exact composition (pair scalar value) multiply

lemma polynomial_cachedWordCount : PolynomialTime cachedWordCountRealizer := by
  unfold cachedWordCountRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
    (polynomial_composition polynomial_cachedWordInput polynomial_decisionWeightSum)) polynomial_multiply

def transitionCount (z : TransitionQuery) : ℕ :=
  ((booleanWords z.2).map (fun bits => cachedWordCount (z.1,bits))).sum

def transitionCountRealizer : Realizer transitionCount := by
  let input : Realizer (fun z : TransitionQuery => (z.1,booleanWords z.2)) :=
    pair first (composition (f := fun z : TransitionQuery => z.2) (g := booleanWords)
      second booleanWordsRealizer)
  let counts := composition (mapWith cachedWordCountRealizer) listSum
  exact composition (f := fun z : TransitionQuery => (z.1,booleanWords z.2))
    (g := fun z : (TransitionCache×(List ℕ×List ℕ))×List (List Bool) =>
      (z.2.map (fun bits => cachedWordCount (z.1,bits))).sum) input counts

lemma work_transitionCount : WorkBound transitionCountRealizer
    (fun z => gridStateCount (z.2,2)+weight z) := by
  have hw : WorkBound (composition (second (A := TransitionCache×(List ℕ×List ℕ)))
      booleanWordsRealizer) (fun z : TransitionQuery => gridStateCount (z.2,2)+weight z) := by
    apply work_composition (work_of_polynomial polynomial_second Polynomial.X
      (fun z => by simp)) work_booleanWords Polynomial.X
    intro z
    simp only [Polynomial.eval_X]
    exact Nat.add_le_add_left (weight_snd z) _
  unfold transitionCountRealizer
  apply work_then_polynomial _ (polynomial_composition
    (polynomial_mapWith polynomial_cachedWordCount) polynomial_listSum)
  exact work_pair (work_of_polynomial polynomial_first Polynomial.X (fun z => by
    simp only [Polynomial.eval_X]; omega)) hw Polynomial.X (fun z => by
      simp only [Polynomial.eval_X]; omega)

lemma transitionCount_words (z : TransitionCache×(List ℕ×List ℕ))
    (xs : List Bool) (s : ℕ) (hs : xs.length=s) :
    transitionCount (z,xs)=∑ bits : Fin s → Bool,cachedWordCount (z,List.ofFn bits) :=
  sum_booleanWords xs s hs _

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.IntegerLaw
open scoped BigOperators Classical
noncomputable section

lemma booleanFinish_count {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    {s f : ℕ} (p : IntegerLaw A (2^f)) (finish : (Fin s → Bool) → A → B) (b : B) :
    (booleanFinish p finish).count b=
      ∑ bits : Fin s → Bool,∑ a,if finish bits a=b then p.count a else 0 := by
  change (∑ z : (Fin s → Bool)×A,if finish z.1 z.2=b then 1*p.count z.2 else 0)=_
  rw [Fintype.sum_prod_type]
  simp only [one_mul]

end
end ContingencyTables.IntegerLaw

end OAI
