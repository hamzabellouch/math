import OAI.Combinatorics.ContingencyTables.Transport.IntegerExchangeArithmetic
import OAI.Combinatorics.MatchingCount.Machines.TreeFastLookup
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialLists
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure

namespace OAI

/-! # A binary list program for a small-profile unit exchange -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

abbrev ExchangeInput := List ℕ×(ℕ×ℕ)

def exchangeEntry (z : ExchangeInput×ℕ) : ℕ :=
  z.1.1.getD z.2 0+(if z.2=z.1.2.1 then 1 else 0)-(if z.2=z.1.2.2 then 1 else 0)

def exchangeEntryRealizer : Realizer exchangeEntry := by
  let V : Realizer (fun z : ExchangeInput×ℕ => z.1.1) := composition first first
  let A : Realizer (fun z : ExchangeInput×ℕ => z.2) := second
  let I : Realizer (fun z : ExchangeInput×ℕ => z.1.2.1) :=
    composition (composition first second) first
  let J : Realizer (fun z : ExchangeInput×ℕ => z.1.2.2) :=
    composition (composition first second) second
  let addOne := choose (composition (pair A I) natEqual) (constant 1) (constant 0)
  let subOne := choose (composition (pair A J) natEqual) (constant 1) (constant 0)
  exact (composition (pair (composition
    (pair (composition (pair V A) (getDFast 0)) addOne) add) subOne) subtract).congr
      (fun z => by simp only [Function.comp_apply,exchangeEntry,decide_eq_true_eq])

theorem polynomial_exchangeEntry : PolynomialTime exchangeEntryRealizer := by
  have hV : PolynomialTime (composition
      (first (A := ExchangeInput) (B := ℕ)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hA : PolynomialTime (second (A := ExchangeInput) (B := ℕ)) := polynomial_second
  have hI : PolynomialTime (composition
      (composition (first (A := ExchangeInput) (B := ℕ)) second) first) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first
  have hJ : PolynomialTime (composition
      (composition (first (A := ExchangeInput) (B := ℕ)) second) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second
  have hi := polynomial_choose (polynomial_composition (polynomial_pair hA hI) polynomial_natEqual)
    (polynomial_constant 1) (polynomial_constant 0)
  have hj := polynomial_choose (polynomial_composition (polynomial_pair hA hJ) polynomial_natEqual)
    (polynomial_constant 1) (polynomial_constant 0)
  unfold exchangeEntryRealizer
  exact polynomial_congr _ (polynomial_composition
    (polynomial_pair (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair hV hA) (polynomial_getDFast 0)) hi) polynomial_add) hj)
    polynomial_subtract)

def listExchange (z : ExchangeInput) : List ℕ :=
  (List.range z.1.length).map (fun a => exchangeEntry (z,a))

def listExchangeRealizer : Realizer listExchange :=
  composition (pair identity (composition (composition first listLength) range))
    (mapWith exchangeEntryRealizer)

/-- Its loop traverses the input profile once, even if the supplied
coordinate indices are much larger than its length. -/
theorem polynomial_listExchange : PolynomialTime listExchangeRealizer := by
  have hr : PolynomialTime (composition
      (composition (first (A := List ℕ) (B := ℕ×ℕ)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
    intro z
    simp only [Polynomial.eval_X]
    exact (list_length_le_weight z.1).trans (by rw [weight_prod]; omega)
  exact polynomial_composition (polynomial_pair polynomial_identity hr)
    (polynomial_mapWith polynomial_exchangeEntry)

lemma listExchange_length (z : ExchangeInput) : (listExchange z).length=z.1.length := by
  simp only [listExchange,List.length_map,List.length_range]

/-- The binary list program implements the exact coordinate update used
by the physical graph, with no bounded-integer overflow. -/
theorem listExchange_ofFn {n : ℕ} (v : Fin n → ℕ) (i j : Fin n) :
    listExchange (List.ofFn v,(i.val,j.val))=
      List.ofFn (IntegerWeightedTransport.exchangeTarget v i j) := by
  apply List.ext_getElem
  · simp only [listExchange,List.length_map,List.length_range,List.length_ofFn]
  · intro a ha _
    have han : a<n := by
      simpa only [listExchange,List.length_map,List.length_range,List.length_ofFn] using ha
    simp only [listExchange,List.getElem_map,List.getElem_range,List.getElem_ofFn,exchangeEntry,
      List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simpa using han)]
    simp only [Option.getD_some,List.getElem_ofFn,IntegerWeightedTransport.exchangeTarget,Fin.ext_iff]

end ContingencyTables.ProfilePrograms

end OAI
