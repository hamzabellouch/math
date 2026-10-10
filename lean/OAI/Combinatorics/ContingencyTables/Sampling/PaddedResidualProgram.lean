import OAI.Combinatorics.ContingencyTables.Sampling.SmallMarginTestProgram
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperPreparedProposal

namespace OAI

/-! # Computing padded residual margins from the stored small profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

def largeFlag (z : ℕ×ℕ) : ℕ := if z.1≤z.2 then 1 else 0

def largeFlagRealizer : Realizer largeFlag :=
  (choose leNat (constant 1) (constant 0)).congr
    (by intro z; simp only [largeFlag,decide_eq_true_eq])

theorem polynomial_largeFlag : PolynomialTime largeFlagRealizer :=
  polynomial_congr _ (polynomial_choose polynomial_leNat (polynomial_constant 1) (polynomial_constant 0))

def largeCount (z : ℕ×List ℕ) : ℕ := (z.2.map (fun a => largeFlag (z.1,a))).sum

def largeCountRealizer : Realizer largeCount := composition (mapWith largeFlagRealizer) listSum

theorem polynomial_largeCount : PolynomialTime largeCountRealizer :=
  polynomial_composition (polynomial_mapWith polynomial_largeFlag) polynomial_listSum

abbrev PaddingData := MarginCheckData×ℕ

def paddedMarginAt (row : Bool) (z : PaddingData×ℕ) : ℕ :=
  let a := (marginList row z.1.1).getD z.2 0
  let used := lineSum row (lineArgument row (z.1.1,z.2))
  a-used+largeFlag (z.1.1.2,a)*largeCount (z.1.1.2,marginList (!row) z.1.1)*z.1.2

def paddedMarginAtRealizer (row : Bool) : Realizer (paddedMarginAt row) := by
  let arg : Realizer (fun z : PaddingData×ℕ => (z.1.1,z.2)) :=
    pair (composition first first) second
  let value := composition arg (marginValueRealizer row)
  let used := composition arg (lineValueRealizer row)
  let threshold : Realizer (fun z : PaddingData×ℕ => z.1.1.2) :=
    composition (composition first first) second
  let pad : Realizer (fun z : PaddingData×ℕ => z.1.2) := composition first second
  let flag := composition (pair threshold value) largeFlagRealizer
  let count := composition (pair threshold
    (composition (composition first first) (marginListRealizer (!row)))) largeCountRealizer
  let amount := composition (pair (composition (pair flag count) multiply) pad) multiply
  let remain := composition (pair value used) subtract
  let result := composition (pair remain amount) add
  exact result

theorem polynomial_paddedMarginAt (row : Bool) : PolynomialTime (paddedMarginAtRealizer row) := by
  have ha : PolynomialTime (pair (composition
      (first (A := PaddingData) (B := ℕ)) first) second) :=
    polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second
  have ht : PolynomialTime (composition (composition
      (first (A := PaddingData) (B := ℕ)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  unfold paddedMarginAtRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition ha (polynomial_marginValue row))
      (polynomial_composition ha (polynomial_lineValue row))) polynomial_subtract)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_pair ht
          (polynomial_composition ha (polynomial_marginValue row))) polynomial_largeFlag)
        (polynomial_composition (polynomial_pair ht
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            (polynomial_marginList (!row)))) polynomial_largeCount)) polynomial_multiply)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply)) polynomial_add

def paddedMargins (row : Bool) (z : PaddingData) : List ℕ :=
  (List.range (marginList row z.1).length).map (fun i => paddedMarginAt row (z,i))

def paddedMarginsRealizer (row : Bool) : Realizer (paddedMargins row) :=
  composition (pair identity (composition first (marginIndices row))) (mapWith (paddedMarginAtRealizer row))

theorem polynomial_paddedMargins (row : Bool) : PolynomialTime (paddedMarginsRealizer row) :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first (polynomial_marginIndices row)))
    (polynomial_mapWith (polynomial_paddedMarginAt row))

open scoped BigOperators

lemma largeCount_ofFn {n : ℕ} (U : ℕ) (r : Fin n → ℕ) :
    largeCount (U,List.ofFn r)=∑ i,if U≤r i then 1 else 0 := by
  simp only [largeCount,List.map_ofFn,List.sum_ofFn,Function.comp_apply,largeFlag]

lemma paddedMarginAt_eq (row : Bool) (z : PaddingData) (i : ℕ) :
    paddedMarginAt row (z,i)=
      (marginList row z.1).getD i 0-lineSum row (lineArgument row (z.1,i))+
        (if z.1.2≤(marginList row z.1).getD i 0
          then largeCount (z.1.2,marginList (!row) z.1)*z.2 else 0) := by
  unfold paddedMarginAt largeFlag
  dsimp only
  split_ifs <;> simp only [one_mul,zero_mul,add_zero]

end ContingencyTables.ProfilePrograms

end OAI
