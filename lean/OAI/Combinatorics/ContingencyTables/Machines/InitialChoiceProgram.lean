import OAI.Combinatorics.ContingencyTables.Machines.FixedCardinalityFlat
import OAI.Combinatorics.ContingencyTables.Machines.InitialFactorialBits
import OAI.Combinatorics.ContingencyTables.Machines.DependentWordProgram

namespace OAI

/-! # Polynomial independent-cell initialization program

The capacities are a supplied list. A polynomial index scan extracts
each disjoint variable-width word block and runs the local subset
program. The resulting rows are exactly the independent cell choices
in the initial finite-word law.
-/

namespace ContingencyTables.InitialChoiceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open DensePrograms FixedCardinalityProgram

def cellWidth (z : ℕ×ℕ) : ℕ := z.1+z.2*z.1

def cellWidthRealizer : Realizer cellWidth :=
  composition (pair first (composition (pair second first) multiply)) add

theorem polynomial_cellWidth : PolynomialTime cellWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_multiply))
    polynomial_add

def widths (z : List ℕ×ℕ) : List ℕ := z.1.map (fun n => cellWidth (z.2,n))

def widthsRealizer : Realizer widths :=
  composition (pair second first) (mapWith cellWidthRealizer)

theorem polynomial_widths : PolynomialTime widthsRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith polynomial_cellWidth)

abbrev Input := (List ℕ×ℕ)×List Bool

def cellCode (z : Input×ℕ) : List Bool :=
  subsetCode ((z.1.1.1.getD z.2 0,z.1.1.2),
    dependentChunk ((widths z.1.1,z.1.2),z.2))

def cellCodeRealizer : Realizer cellCode := by
  let cap : Realizer (fun z : Input×ℕ => z.1.1.1.getD z.2 0) :=
    composition (pair (composition (composition first first) first) second) (getDFast 0)
  let B : Realizer (fun z : Input×ℕ => z.1.1.2) :=
    composition (composition first first) second
  let sizes : Realizer (fun z : Input×ℕ => widths z.1.1) :=
    composition (composition first first) widthsRealizer
  let bits : Realizer (fun z : Input×ℕ => z.1.2) := composition first second
  let block := composition (pair (pair sizes bits) second) dependentChunkRealizer
  exact composition (pair (pair cap B) block) subsetCodeRealizer

theorem polynomial_cellCode : PolynomialTime cellCodeRealizer := by
  unfold cellCodeRealizer
  have hc : PolynomialTime (composition
      (pair (composition (composition (first (A := Input) (B := ℕ)) first) first) second)
      (getDFast 0)) := polynomial_composition
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
    (polynomial_getDFast 0)
  have hb : PolynomialTime (composition
      (composition (first (A := Input) (B := ℕ)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  have hs := polynomial_composition
    (polynomial_composition (polynomial_first (A := Input) (B := ℕ)) polynomial_first) polynomial_widths
  exact polynomial_composition (polynomial_pair (polynomial_pair hc hb)
    (polynomial_composition (polynomial_pair (polynomial_pair hs
      (polynomial_composition polynomial_first polynomial_second)) polynomial_second)
      polynomial_dependentChunk)) polynomial_subsetCode

def indices (z : Input) : List ℕ := List.range z.1.1.length

def indicesRealizer : Realizer indices :=
  composition (composition (composition first first) listLength) range

theorem polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

def choiceCode (z : Input) : List (List Bool) := (indices z).map (fun i => cellCode (z,i))

def choiceCodeRealizer : Realizer choiceCode :=
  composition (pair identity indicesRealizer) (mapWith cellCodeRealizer)

theorem polynomial_choiceCode : PolynomialTime choiceCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_cellCode)

noncomputable section
open FixedCardinalityMixture InitialFactorialBits
open scoped BigOperators

lemma widths_ofFn {q : ℕ} (b : Fin q → ℕ) (B : ℕ) :
    widths (List.ofFn b,B)=List.ofFn (fun i => drawBits B (b i)) := by
  unfold widths
  rw [List.map_ofFn]
  rfl

theorem cellCode_ofFn {q : ℕ} (b : Fin q → ℕ) (B : ℕ) (hB : 0<B)
    (bits : Fin (bitCount b B) → Bool) (i : Fin q) :
    cellCode (((List.ofFn b,B),List.ofFn bits),i.val)=
      List.ofFn (FixedCardinalityMixture.vectorDraw B (b i) (wordEquiv b B bits i)) := by
  unfold cellCode
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,dite_true,
    Option.getD_some,Fin.eta,widths_ofFn]
  have hd := dependentChunk_ofFn (fun i => drawBits B (b i)) bits i
  have he := congrArg (fun block : List Bool => subsetCode ((b i,B),block)) hd
  exact he.trans (subsetCode_ofFn B (b i) hB (wordEquiv b B bits i))

/-- The executable product of cell programs gives exactly the Boolean
rows whose support is the initial independent choice vector. -/
theorem choiceCode_ofFn {q : ℕ} (b : Fin q → ℕ) (B : ℕ) (hB : 0<B)
    (bits : Fin (bitCount b B) → Bool) :
    choiceCode ((List.ofFn b,B),List.ofFn bits)=
      List.ofFn (fun i => List.ofFn (vectorDraw B (b i) (wordEquiv b B bits i))) := by
  apply List.ext_getElem
  · simp only [choiceCode,indices,List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have hiq : i<q := by
      simpa only [choiceCode,indices,List.length_map,List.length_range,List.length_ofFn] using hi
    simp only [choiceCode,indices,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact cellCode_ofFn b B hB bits ⟨i,hiq⟩

end
end ContingencyTables.InitialChoiceProgram

end OAI
