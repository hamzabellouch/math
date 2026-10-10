import OAI.Combinatorics.ContingencyTables.Machines.CanonicalInitialEncoding

namespace OAI

/-! # Computing paired-coordinate metadata from a binary profile

Consecutive coordinates are paired by the bounded list scan
(0,1),(2,3),.... This is the exact metadata of the canonical paired-label
order, rather than a catalog supplied as an external oracle.
-/

namespace ContingencyTables.PairedCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms

def indexPair (i : ℕ) : ℕ×ℕ := (2*i,2*i+1)

def twiceRealizer : Realizer (fun i : ℕ => 2*i) :=
  composition (f := fun i : ℕ => (2,i)) (g := fun z : ℕ×ℕ => z.1*z.2)
    (pair (constant 2) identity) multiply

def indexPairRealizer : Realizer indexPair :=
  pair twiceRealizer
    (composition (f := fun i : ℕ => (2*i,1)) (g := fun z : ℕ×ℕ => z.1+z.2)
      (pair twiceRealizer (constant 1)) add)

lemma polynomial_indexPair : PolynomialTime indexPairRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_identity)
      polynomial_multiply)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_identity)
        polynomial_multiply) (polynomial_constant 1)) polynomial_add)

def indicesRealizer : Realizer (fun xs : List ℕ => List.range (xs.length/2)) :=
  composition (composition (pair listLength (constant 2)) quotient) range

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_pair polynomial_listLength (polynomial_constant 2))
      polynomial_quotient) Polynomial.X
  intro xs
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (Nat.div_le_self xs.length 2).trans (list_length_le_weight xs)

def catalog (xs : List ℕ) : List (ℕ×ℕ) := (List.range (xs.length/2)).map indexPair

def catalogRealizer : Realizer catalog := composition indicesRealizer (map indexPairRealizer)

theorem polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition polynomial_indices (polynomial_map polynomial_indexPair)

def pairList {α : Type*} : List α → List (α×Bool)
  | [] => []
  | a::xs => (a,false)::(a,true)::pairList xs

lemma pairList_length {α : Type*} (xs : List α) : (pairList xs).length=2*xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [pairList,List.length_cons,ih]; omega

lemma pairList_product {α : Type*} (xs : List α) : pairList xs=xs.product [false,true] := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    change (a,false)::(a,true)::pairList xs=(a,false)::(a,true)::xs.product [false,true]
    rw [ih]

lemma pairList_get_even {α : Type*} (xs : List α) (i : ℕ) (hi : i<xs.length) :
    (pairList xs)[2*i]'(by rw [pairList_length]; omega)=(xs[i],false) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [pairList,Nat.mul_succ,List.getElem_cons_succ] using
        ih i (Nat.lt_of_succ_lt_succ hi)

lemma pairList_get_odd {α : Type*} (xs : List α) (i : ℕ) (hi : i<xs.length) :
    (pairList xs)[2*i+1]'(by rw [pairList_length]; omega)=(xs[i],true) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [pairList,Nat.mul_succ,List.getElem_cons_succ,Nat.add_assoc] using
        ih i (Nat.lt_of_succ_lt_succ hi)

noncomputable section
open CanonicalInitialEncoding InitialTransversals CompanionArithmeticProposal
open scoped Classical
variable {q : ℕ} (b : Fin q → ℕ)

def labelOrder : Fin (copyOrder b).length ≃ Copy b :=
  List.Nodup.getEquivOfForallMemList (copyOrder b) (copyOrder_nodup b) (copyOrder_mem b)

lemma coordinate_false (i : Fin (copyOrder b).length) :
    (CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,false)).val=2*i.val := by
  have hl : (pairOrder b).length=2*(copyOrder b).length := by
    change ((copyOrder b).product [false,true]).length=2*(copyOrder b).length
    rw [←pairList_product]
    exact pairList_length _
  let k : Fin (pairOrder b).length := ⟨2*i.val,by rw [hl]; omega⟩
  have hk : (CanonicalInitialEncoding.coordinateEquiv b).symm k=(labelOrder b i,false) := by
    change (pairOrder b)[k.val]=((copyOrder b)[i.val],false)
    simpa only [pairOrder,←pairList_product,k] using pairList_get_even (copyOrder b) i.val i.isLt
  have he := congrArg (fun a => (CanonicalInitialEncoding.coordinateEquiv b a).val) hk
  simpa only [Equiv.apply_symm_apply,k] using he.symm

lemma coordinate_true (i : Fin (copyOrder b).length) :
    (CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,true)).val=2*i.val+1 := by
  have hl : (pairOrder b).length=2*(copyOrder b).length := by
    change ((copyOrder b).product [false,true]).length=2*(copyOrder b).length
    rw [←pairList_product]
    exact pairList_length _
  let k : Fin (pairOrder b).length := ⟨2*i.val+1,by rw [hl]; omega⟩
  have hk : (CanonicalInitialEncoding.coordinateEquiv b).symm k=(labelOrder b i,true) := by
    change (pairOrder b)[k.val]=((copyOrder b)[i.val],true)
    simpa only [pairOrder,←pairList_product,k] using pairList_get_odd (copyOrder b) i.val i.isLt
  have he := congrArg (fun a => (CanonicalInitialEncoding.coordinateEquiv b a).val) hk
  simpa only [Equiv.apply_symm_apply,k] using he.symm

/-- Every state encoded in the canonical order has exactly the pair
catalog computed by the polynomial consecutive-coordinate scan. -/
theorem catalog_encode (S : Set (Copy b×Bool)) :
    catalog (encodeSet (CanonicalInitialEncoding.coordinateEquiv b) S)=
      List.ofFn (fun i : Fin (copyOrder b).length =>
        ((CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,false)).val,
          (CanonicalInitialEncoding.coordinateEquiv b (labelOrder b i,true)).val)) := by
  have hl : (pairOrder b).length=2*(copyOrder b).length := by
    change ((copyOrder b).product [false,true]).length=2*(copyOrder b).length
    rw [←pairList_product]
    exact pairList_length _
  simp only [catalog,encodeSet,List.length_ofFn,hl]
  rw [Nat.mul_div_cancel_left _ (by decide : 0<2)]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,indexPair,
      coordinate_false,coordinate_true]

end
end ContingencyTables.PairedCatalogProgram

end OAI
