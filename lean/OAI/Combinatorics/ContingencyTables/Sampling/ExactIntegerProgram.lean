import OAI.Combinatorics.ContingencyTables.Sampling.ExactIntegerChoice
import OAI.Combinatorics.ContingencyTables.Machines.ListWordProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialSums

namespace OAI

/-! # Binary execution of an exact integer-weighted rejection trial -/

namespace ContingencyTables.ExactIntegerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

/-- Fractions share the total integer weight before canonical reduction. -/
def weightsCode (xs : List ℕ) : List TreeFraction.Fraction :=
  xs.map (fun w => TreeFraction.normalize (w,xs.sum))
def weightsCodeRealizer : Realizer weightsCode :=
  composition (f := fun xs : List ℕ => (xs.sum,xs))
    (g := fun z : ℕ×List ℕ => z.2.map (fun w => TreeFraction.normalize (w,z.1)))
    (pair listSum identity)
    (mapWith (composition (pair second first) TreeFraction.normalizeRealizer))

lemma polynomial_weightsCode : PolynomialTime weightsCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_listSum polynomial_identity)
    (polynomial_mapWith (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      TreeFraction.polynomial_normalize))

abbrev Input := List ℕ×List Bool

def choiceInput (z : Input) : List TreeFraction.Fraction×TreeFraction.Fraction :=
  (weightsCode z.1,(StackAddition.value z.2,z.1.sum))
def choiceInputRealizer : Realizer choiceInput :=
  pair (composition first weightsCodeRealizer)
    (pair (composition second bitValue) (composition first listSum))

lemma polynomial_choiceInput : PolynomialTime choiceInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_weightsCode)
    (polynomial_pair (polynomial_composition polynomial_second polynomial_bitValue)
      (polynomial_composition polynomial_first polynomial_listSum))

/-- One trial returns an index or requests another independent word.
All integers are processed in binary; no weight is expanded into copies. -/
def weightedIndex (z : Input) : Option ℕ :=
  if StackAddition.value z.2<z.1.sum then some (ExecutableChoice.choose (choiceInput z)) else none

def weightedIndexRealizer : Realizer weightedIndex :=
  (choose (composition (pair (composition second bitValue) (composition first listSum)) less)
    (composition (composition choiceInputRealizer ExecutableChoice.chooseFast) TreeTyped.some)
    (constant none)).congr (by
      intro z
      simp only [Function.comp_apply,decide_eq_true_eq,weightedIndex])

lemma polynomial_weightedIndex : PolynomialTime weightedIndexRealizer := by
  unfold weightedIndexRealizer
  apply polynomial_congr
  exact polynomial_choose
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_bitValue)
      (polynomial_composition polynomial_first polynomial_listSum)) polynomial_less)
    (polynomial_composition
      (polynomial_composition polynomial_choiceInput ExecutableChoice.polynomial_chooseFast)
      polynomial_some) (polynomial_constant none)

noncomputable section
open ExactIntegerChoice
open scoped BigOperators Classical

lemma weightsCode_ofFn {r : ℕ} (w : Fin r → ℕ) :
    weightsCode (List.ofFn w)=List.ofFn (fun i => TreeFraction.repr (normalized w i)) := by
  simp only [weightsCode,List.sum_ofFn,List.map_ofFn,TreeFraction.normalize_repr]
  rfl

/-- The compiled binary trial is exactly the integer-grid experiment. -/
lemma weightedIndex_ofFn {r k : ℕ} (w : Fin r → ℕ) (h : 0<totalWeight w)
    (hQ : totalWeight w≤2^k) (bits : Fin k → Bool) :
    weightedIndex (List.ofFn w,List.ofFn bits)=
      (weightedTrial w h hQ (FairBits.binaryWordEquiv k bits)).map Fin.val := by
  unfold weightedIndex choiceInput weightedTrial intervalTrial
  rw [weightsCode_ofFn,bitValue_eq_word,List.sum_ofFn]
  change (if (FairBits.binaryWordEquiv k bits).val<totalWeight w then _ else _)=_
  split_ifs with hb
  · exact congrArg Option.some (ExecutableChoice.choose_eq (normalized w) (normalized_nonnegative w)
      (normalized_total w h) h ⟨(FairBits.binaryWordEquiv k bits).val,hb⟩)
  · rfl

end
end ContingencyTables.ExactIntegerPrograms

end OAI
