import OAI.Combinatorics.ContingencyTables.Machines.IntegerMatrixProgram

namespace OAI

/-! # Propagating an executable point mass through an integer matrix -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

def pointEntry (z : ℕ×ℕ) : ℕ := if z.2=z.1 then 1 else 0

def pointEntryRealizer : Realizer pointEntry :=
  (choose (composition (pair second first) natEqual) (constant 1) (constant 0)).congr (by
    intro z
    simp only [Function.comp_apply,decide_eq_true_eq]
    rfl)

lemma polynomial_pointEntry : PolynomialTime pointEntryRealizer := by
  unfold pointEntryRealizer
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition
    (polynomial_pair polynomial_second polynomial_first) polynomial_natEqual)
    (polynomial_constant 1) (polynomial_constant 0)

def pointVector (z : List (List ℕ)×ℕ) : List ℕ :=
  (List.range z.1.length).map (fun j => pointEntry (z.2,j))

def pointVectorRealizer : Realizer pointVector :=
  composition (pair second (composition (composition first listLength) range))
    (mapWith pointEntryRealizer)

lemma polynomial_pointVector : PolynomialTime pointVectorRealizer := by
  unfold pointVectorRealizer
  apply polynomial_composition _ (polynomial_mapWith polynomial_pointEntry)
  apply polynomial_pair polynomial_second
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

def fromPoint (z : ℕ×(List (List ℕ)×ℕ)) : List ℕ :=
  iterate (z.1,(z.2.1,pointVector z.2))

def fromPointInputRealizer : Realizer (fun z : ℕ×(List (List ℕ)×ℕ) =>
    (z.1,(z.2.1,pointVector z.2))) :=
  pair first (pair (composition second first) (composition second pointVectorRealizer))

def fromPointRealizer : Realizer fromPoint :=
  composition fromPointInputRealizer iterateRealizer

lemma polynomial_fromPointInput : PolynomialTime fromPointInputRealizer :=
  polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_second polynomial_pointVector))

lemma work_fromPoint : WorkBound fromPointRealizer (fun z => z.1+weight z.2) := by
  have hi : WorkBound fromPointInputRealizer (fun z => z.1+weight z.2) :=
    work_of_polynomial polynomial_fromPointInput (4*X+2) (by
      intro z
      have hn := weight_nat_numeric z.1
      rw [←Prod.eta z,weight_prod]
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      omega)
  obtain ⟨p,hp⟩ := hi
  unfold fromPointRealizer
  apply work_composition ⟨p,hp⟩ work_iterate (X+p)
  intro z
  have hz := hp z
  dsimp only at hz
  simp only [Polynomial.eval_add,Polynomial.eval_X]
  change z.1+weight (z.2.1,pointVector z.2) ≤ _
  have hw : weight (z.2.1,pointVector z.2) ≤ weight (z.1,(z.2.1,pointVector z.2)) :=
    weight_snd (z.1,(z.2.1,pointVector z.2))
  omega

lemma pointVector_ofFn {n : ℕ} (B : Fin n → Fin n → ℕ) (start : Fin n) :
    pointVector (List.ofFn (fun j => List.ofFn (fun i => B i j)),start.val)=
      List.ofFn (fun i : Fin n => if i=start then 1 else 0) := by
  unfold pointVector
  rw [List.length_ofFn]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,pointEntry,Fin.ext_iff]


lemma fromPoint_ofFn {n : ℕ} (B : Fin n → Fin n → ℕ) (start : Fin n) (N : ℕ) :
    fromPoint (N,(List.ofFn (fun j => List.ofFn (fun i => B i j)),start.val))=
      List.ofFn (IntegerPropagation.numerators B start N) := by
  unfold fromPoint
  rw [pointVector_ofFn,iterate_ofFn]

end ContingencyTables.IntegerMatrixPrograms

end OAI
