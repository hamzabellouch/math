import OAI.Combinatorics.ContingencyTables.Dense.DenseMatrixProgram

namespace OAI

/-! # Binary matrix propagation of the implemented dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

abbrev MatrixWalkData := (List Bool×CountMatrixData)×List ℕ

def initialEntry (z : List ℕ×List ℕ) : ℕ :=
  if NatListEquality.listEqual z then 1 else 0

def initialEntryRealizer : Realizer initialEntry :=
  choose NatListEquality.listEqualRealizer (constant 1) (constant 0)

lemma polynomial_initialEntry : PolynomialTime initialEntryRealizer :=
  polynomial_choose NatListEquality.polynomial_listEqual
    (polynomial_constant 1) (polynomial_constant 0)

def initialVector (z : List (List ℕ)×List ℕ) : List ℕ :=
  z.1.map (fun a => initialEntry (z.2,a))

def initialVectorRealizer : Realizer initialVector :=
  composition (pair second first) (mapWith initialEntryRealizer)

lemma polynomial_initialVector : PolynomialTime initialVectorRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith polynomial_initialEntry)

def matrixWalkInput (z : MatrixWalkData) : ℕ×(List (List ℕ)×List ℕ) :=
  (z.1.1.length,(countMatrix z.1.2,initialVector (z.1.2.2,z.2)))

def matrixWalkInputRealizer : Realizer matrixWalkInput :=
  pair (composition (composition first first) listLength)
    (pair (composition (composition first second) countMatrixRealizer)
      (composition (pair (composition (composition first second) second) second)
        initialVectorRealizer))

lemma polynomial_matrixWalkInput : PolynomialTime matrixWalkInputRealizer :=
  polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_listLength)
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_countMatrix)
      (polynomial_composition (polynomial_pair (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_second)
        polynomial_second) polynomial_initialVector))

def matrixWalk (z : MatrixWalkData) : List ℕ :=
  IntegerMatrixPrograms.iterate (matrixWalkInput z)

def matrixWalkRealizer : Realizer matrixWalk :=
  composition matrixWalkInputRealizer IntegerMatrixPrograms.iterateRealizer

/-- The number of matrix steps is supplied by a unary list. All entries
and the propagated vector use binary integers. -/
theorem polynomial_matrixWalk : PolynomialTime matrixWalkRealizer := by
  obtain ⟨p,hp⟩ := polynomial_matrixWalkInput
  apply work_composition ⟨p,hp⟩ IntegerMatrixPrograms.work_iterate (Polynomial.X+p)
  intro z
  have hl : z.1.1.length ≤ weight z := (list_length_le_weight z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z))
  have hw := weight_snd (matrixWalkInput z)
  have hc := hp z
  simp only [Polynomial.eval_add,Polynomial.eval_X,matrixWalkInput] at *
  omega

lemma initialVector_actual {m n d N : ℕ}
    (e : Fin N ≃ Grid (I := Fin (m*n)) (4*d^8)) (start : Fin N) :
    initialVector (List.ofFn (fun i => gridNatCode (e i)),gridNatCode (e start))=
      List.ofFn (fun i => if i=start then 1 else 0) := by
  simp only [initialVector,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  have he : NatListEquality.listEqual (gridNatCode (e start),gridNatCode (e i))=true ↔
      i=start := by
    rw [NatListEquality.listEqual_true]
    constructor
    · intro h
      exact (e.injective (gridNatCode_injective h)).symm
    · rintro rfl
      rfl
  change (if NatListEquality.listEqual (gridNatCode (e start),gridNatCode (e i))=true
    then (1:ℕ) else 0)=(if i=start then 1 else 0)
  by_cases hi : i=start
  · simp only [ite_eq_left (he.mpr hi),ite_eq_left hi]
  · have hh : NatListEquality.listEqual (gridNatCode (e start),gridNatCode (e i))=false :=
      Bool.eq_false_iff.mpr (fun h => hi (he.mp h))
    simp [hh,hi]

private lemma numerators_reindex {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (M : B → B → ℕ)
    (start : A) (N : ℕ) (y : A) :
    IntegerPropagation.numerators (fun x y => M (e x) (e y)) start N y=
      IntegerPropagation.numerators M (e start) N (e y) := by
  induction N generalizing y with
  | zero => simp [IntegerPropagation.numerators,e.injective.eq_iff]
  | succ N ih =>
    simp only [IntegerPropagation.numerators,ih]
    exact e.sum_comp (fun x => IntegerPropagation.numerators M (e start) N x*M x (e y))

/-- The matrix is the count matrix of the actual Boolean walk, including
all rejected proposals and unused proposal codes. -/
theorem matrixWalk_actual {m n d N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (e : Fin N ≃ Grid (I := Fin (m*n)) (4*d^8))
    (xs steps : List Bool) (hxs : xs.length=8*d^5) (start : Fin N) :
    matrixWalk ((steps,(((xs,2^denseStepBits d),((marginCode R,marginCode P),d)),
      List.ofFn (fun i => gridNatCode (e i)))),gridNatCode (e start))=
      List.ofFn (fun i => IntegerPropagation.numerators
        (denseTransitionCount R P d finProdFinEquiv) (e start) steps.length (e i)) := by
  unfold matrixWalk matrixWalkInput
  rw [countMatrix_actual R P hq e xs hxs,initialVector_actual]
  rw [IntegerMatrixPrograms.iterate_ofFn]
  congr 1
  funext i
  exact numerators_reindex e _ start steps.length i

/-- A matrix-vector entry, normalized by its known dyadic denominator,
is the mass of the implemented finite-bit walk. -/
theorem matrixWalk_mass {m n d N : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (hq : m*n≤d)
    (e : Fin N ≃ Grid (I := Fin (m*n)) (4*d^8))
    (xs steps : List Bool) (hxs : xs.length=8*d^5) (start i : Fin N) :
    ((matrixWalk ((steps,(((xs,2^denseStepBits d),((marginCode R,marginCode P),d)),
      List.ofFn (fun i => gridNatCode (e i)))),gridNatCode (e start))).getD i.val 0:ℚ)/
      (2:ℚ)^(steps.length*denseStepBits d)=
      (denseBooleanWalkLaw R P d finProdFinEquiv (e start) steps.length).mass (e i) := by
  rw [matrixWalk_actual R P hq e xs steps hxs start]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt]
  exact denseWalkCount_mass R P d finProdFinEquiv (e start) (e i) steps.length

end ContingencyTables.DensePrograms

end OAI
