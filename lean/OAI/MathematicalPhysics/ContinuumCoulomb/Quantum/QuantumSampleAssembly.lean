import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumComputedAccuracy

namespace OAI

/-! Exact termwise assembly of the computed physical exchange list. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAxisSample
open Matrix
open scoped BigOperators Classical

abbrev TypedBond (m : ℕ) := Fin m × (Fin m × ℚ)

def typedBondMatrix {m : ℕ} (b : TypedBond m) : Matrix (SourceSpinBasis m) (SourceSpinBasis m) ℂ :=
  (b.2.2:ℂ) • sourceHeisenbergMatrix m b.1 b.2.1

def fieldBonds {n : ℕ} (k : ℕ) (i : Fin n) (a : Fin 2) (J : ℚ) : List (TypedBond (n*4)) :=
  List.ofFn fun e : Fin 3 => (finProdFinEquiv (i,0),
    finProdFinEquiv (i,qmaFieldEdgeRight e),fieldValue k a J e)

def crossBonds {n : ℕ} (k : ℕ) (r : ℚ) (i j : Fin n) (a b : Fin 2) (J : ℚ) :
    List (TypedBond (n*4)) :=
  List.ofFn fun e : Fin 16 =>
    let pq := (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm e
    (finProdFinEquiv (i,pq.1),finProdFinEquiv (j,pq.2),crossValue k r a b J pq.1 pq.2)

def termBonds {n : ℕ} (k : ℕ) (r : ℚ) (t : QMAXZTerm n) (J : ℚ) : List (TypedBond (n*4)) :=
  match t with
  | .scalar => []
  | .field i a => fieldBonds k i a J
  | .pair i j _ a b => crossBonds k r i j a b J ++
      fieldBonds k i a (counterA k a b J) ++ fieldBonds k j b (counterB k a b J)

def termScalar {n : ℕ} (k : ℕ) (t : QMAXZTerm n) (J : ℚ) : ℚ :=
  match t with
  | .scalar => J
  | .field _ a => -shiftValue a J
  | .pair _ _ _ a b => -offset k a b J

def penaltyBonds (n : ℕ) (r : ℚ) : List (TypedBond (n*4)) :=
  List.ofFn fun e : Fin (n*6) =>
    let ik := (finProdFinEquiv : Fin n × Fin 6 ≃ Fin (n*6)).symm e
    (finProdFinEquiv (ik.1,qmaFourEdgeLeft ik.2),
      finProdFinEquiv (ik.1,qmaFourEdgeRight ik.2),r^2)

theorem fieldBonds_matrix {n : ℕ} (k : ℕ) (i : Fin n) (a : Fin 2) (J : ℚ) :
    ((fieldBonds k i a J).map typedBondMatrix).sum =
      ∑ e : Fin 3, (fieldValue k a J e:ℂ) • sourceHeisenbergMatrix (n*4)
        (finProdFinEquiv (i,0)) (finProdFinEquiv (i,qmaFieldEdgeRight e)) := by
  simp only [fieldBonds,List.map_ofFn,List.sum_ofFn,Function.comp_apply,typedBondMatrix]

theorem crossBonds_matrix {n : ℕ} (k : ℕ) (r : ℚ) (i j : Fin n) (a b : Fin 2) (J : ℚ) :
    ((crossBonds k r i j a b J).map typedBondMatrix).sum =
      ∑ p : Fin 4, ∑ q : Fin 4, (crossValue k r a b J p q:ℂ) •
        sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,p)) (finProdFinEquiv (j,q)) := by
  simp only [crossBonds,List.map_ofFn,List.sum_ofFn,Function.comp_apply,typedBondMatrix]
  calc
    _ = ∑ pq : Fin 4 × Fin 4, (crossValue k r a b J pq.1 pq.2:ℂ) •
        sourceHeisenbergMatrix (n*4) (finProdFinEquiv (i,pq.1)) (finProdFinEquiv (j,pq.2)) :=
      Fintype.sum_equiv (finProdFinEquiv : Fin 4 × Fin 4 ≃ Fin 16).symm _ _ (by intro e; rfl)
    _ = _ := Fintype.sum_prod_type _

theorem penaltyBonds_matrix (n : ℕ) (r : ℚ) :
    ((penaltyBonds n r).map typedBondMatrix).sum =
      ∑ i : Fin n, ∑ e : Fin 6, ((r^2:ℚ):ℂ) • sourceHeisenbergMatrix (n*4)
        (finProdFinEquiv (i,qmaFourEdgeLeft e)) (finProdFinEquiv (i,qmaFourEdgeRight e)) := by
  simp only [penaltyBonds,List.map_ofFn,List.sum_ofFn,Function.comp_apply,typedBondMatrix]
  calc
    _ = ∑ ik : Fin n × Fin 6, ((r^2:ℚ):ℂ) • sourceHeisenbergMatrix (n*4)
        (finProdFinEquiv (ik.1,qmaFourEdgeLeft ik.2)) (finProdFinEquiv (ik.1,qmaFourEdgeRight ik.2)) :=
      Fintype.sum_equiv (finProdFinEquiv : Fin n × Fin 6 ≃ Fin (n*6)).symm _ _ (by intro e; rfl)
    _ = _ := Fintype.sum_prod_type _

variable {n : ℕ} {κ : Type*} [Fintype κ]

theorem sum_term_partition {M : Type*} [AddCommMonoid M]
    (t : κ → QMAXZTerm n) (f : κ → M) :
    (∑ e, f e) = (∑ e : QMAXZScalarIndex t, f e.val)+
      (∑ e : QMAXZPairIndex t, f e.val)+(∑ e : QMAXZFieldIndex t, f e.val) := by
  rw [qmaSum_subtype_ite (fun e => (t e).IsScalar),
    qmaSum_subtype_ite (fun e => (t e).IsPair),qmaSum_subtype_ite (fun e => (t e).IsField),
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases t e <;> simp [QMAXZTerm.IsScalar,QMAXZTerm.IsPair,QMAXZTerm.IsField]

theorem termScalar_sum (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    r^2*(n*6)+∑ e, termScalar k (t e) (J e) = scalarValue k r t J := by
  have hs (e : QMAXZScalarIndex t) : termScalar k (t e.val) (J e.val) = J e.val := by
    have h := e.property
    cases ht : t e.val <;> simp_all [QMAXZTerm.IsScalar,termScalar]
  have hp (e : QMAXZPairIndex t) : termScalar k (t e.val) (J e.val) =
      -offset k (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val) := by
    have aux (u : QMAXZTerm n) (hu : u.IsPair) (q : ℚ) : termScalar k u q =
        -offset k (u.asPair hu).axisLeft (u.asPair hu).axisRight q := by
      cases u <;> first | exact hu.elim | rfl
    exact aux (t e.val) e.property (J e.val)
  have hf (e : QMAXZFieldIndex t) : termScalar k (t e.val) (J e.val) =
      -shiftValue (qmaXZFieldData t e).axis (J e.val) := by
    have aux (u : QMAXZTerm n) (hu : u.IsField) (q : ℚ) : termScalar k u q =
        -shiftValue (u.asField hu).axis q := by
      cases u <;> first | exact hu.elim | rfl
    exact aux (t e.val) e.property (J e.val)
  rw [sum_term_partition t (fun e => termScalar k (t e) (J e))]
  simp only [hs,hp,hf,Finset.sum_neg_distrib,scalarValue]
  ring

def pairBondMatrix (k : ℕ) (r : ℚ) (d : QMAXZPair n) (J : ℚ) :
    Matrix (SourceSpinBasis (n*4)) (SourceSpinBasis (n*4)) ℂ :=
  (∑ p : Fin 4, ∑ q : Fin 4, (crossValue k r d.axisLeft d.axisRight J p q:ℂ) •
    sourceHeisenbergMatrix (n*4) (finProdFinEquiv (d.left,p)) (finProdFinEquiv (d.right,q)))+
  ((fieldBonds k d.left d.axisLeft (counterA k d.axisLeft d.axisRight J)).map typedBondMatrix).sum+
  ((fieldBonds k d.right d.axisRight (counterB k d.axisLeft d.axisRight J)).map typedBondMatrix).sum

theorem termBonds_pair (k : ℕ) (r : ℚ) (u : QMAXZTerm n) (hu : u.IsPair) (J : ℚ) :
    ((termBonds k r u J).map typedBondMatrix).sum = pairBondMatrix k r (u.asPair hu) J := by
  cases u with
  | scalar => exact hu.elim
  | field => exact hu.elim
  | pair i j hij a b =>
    simp only [termBonds,List.map_append,List.sum_append,crossBonds_matrix,
      pairBondMatrix,QMAXZTerm.asPair]

theorem termBonds_field (k : ℕ) (r : ℚ) (u : QMAXZTerm n) (hu : u.IsField) (J : ℚ) :
    ((termBonds k r u J).map typedBondMatrix).sum =
      ((fieldBonds k (u.asField hu).site (u.asField hu).axis J).map typedBondMatrix).sum := by
  cases u <;> first | exact hu.elim | rfl

theorem termBonds_scalar (k : ℕ) (r : ℚ) (u : QMAXZTerm n) (hu : u.IsScalar) (J : ℚ) :
    ((termBonds k r u J).map typedBondMatrix).sum = 0 := by
  cases u <;> first | exact hu.elim | rfl

theorem matrixValue_assembly (k : ℕ) (r : ℚ) (t : κ → QMAXZTerm n) (J : κ → ℚ) :
    matrixValue k r t J = ((penaltyBonds n r).map typedBondMatrix).sum+
      (∑ e, ((termBonds k r (t e) (J e)).map typedBondMatrix).sum)+
      (scalarValue k r t J:ℂ) • 1 := by
  rw [sum_term_partition t (fun e => ((termBonds k r (t e) (J e)).map typedBondMatrix).sum)]
  have hs : (∑ e : QMAXZScalarIndex t,
      ((termBonds k r (t e.val) (J e.val)).map typedBondMatrix).sum) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact termBonds_scalar k r _ e.property _
  have hp : (∑ e : QMAXZPairIndex t,
      ((termBonds k r (t e.val) (J e.val)).map typedBondMatrix).sum) =
      ∑ e : QMAXZPairIndex t, pairBondMatrix k r (qmaXZPairData t e) (J e.val) := by
    apply Finset.sum_congr rfl
    intro e _
    exact termBonds_pair k r _ e.property _
  have hf : (∑ e : QMAXZFieldIndex t,
      ((termBonds k r (t e.val) (J e.val)).map typedBondMatrix).sum) =
      ∑ e : QMAXZFieldIndex t,
        ((fieldBonds k (qmaXZFieldData t e).site (qmaXZFieldData t e).axis (J e.val)).map typedBondMatrix).sum := by
    apply Finset.sum_congr rfl
    intro e _
    exact termBonds_field k r _ e.property _
  rw [hs,hp,hf,zero_add,penaltyBonds_matrix]
  simp only [matrixValue,qmaExchangeMatrix,QMAFourExchangeIndex,Fintype.sum_sum_type,
    Fintype.sum_prod_type,qmaFourExchangeLeft,qmaFourExchangeRight,weightValue,
    pairBondMatrix,fieldBonds_matrix,Fin.sum_univ_two,ite_true,
    show (1:Fin 2) ≠ 0 by decide,ite_false,Complex.ofReal_ratCast,
    Finset.sum_add_distrib]
  abel

end ContinuumCoulomb.QuantumAxisSample

end

end OAI
