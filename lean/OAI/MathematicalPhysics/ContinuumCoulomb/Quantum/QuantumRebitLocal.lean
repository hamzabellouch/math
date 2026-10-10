import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumScalarFaithful
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumScalarReindex
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedCoefficient

namespace OAI

/-! The exact scalar core of a lifted term with one active reference qubit.
Spectator reference bits are zero in the local core and contribute identities. -/

noncomputable section
namespace ContinuumCoulomb.QuantumAlgebraicHistory
open QuantumAlgebraicScalar QuantumFixedPauli
open scoped Classical BigOperators

def referenceState (n : ℕ) (i : Fin n) (a : Fin 2) : Fin n → Fin 2 :=
  fun j => if j=i then a else 0

theorem referenceState_eq_iff (n : ℕ) (i : Fin n) (a b : Fin 2) :
    referenceState n i a=referenceState n i b ↔ a=b := by
  constructor
  · intro h
    simpa only [referenceState,ite_true] using congrFun h i
  · rintro rfl
    rfl

theorem reference_identity (n : ℕ) (i : Fin n) (a b : Fin 2) :
    identity (referenceState n i a) (referenceState n i b)=identity a b := by
  simp only [identity,referenceState_eq_iff]

theorem localY_referenceState (n : ℕ) (i : Fin n) (a b : Fin 2) :
    localY n i (referenceState n i a) (referenceState n i b)=
      QuantumFixedPauli.pauli 2 a b := by
  apply value_injective
  rw [value_localY,value_pauli]
  change sourceLocalPauli n i 1 (referenceState n i a) (referenceState n i b)=
    ContinuumCoulomb.pauli 1 a b
  unfold sourceLocalPauli sourceTensor
  rw [Finset.prod_eq_single i]
  · simp only [ite_true,referenceState,ite_true]
  · intro j _ hji
    simp only [hji,ite_false,referenceState,Matrix.one_apply,ite_true]
  · simp

theorem lift_extend {ι : Type} [Fintype ι] [DecidableEq ι] (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (u v : QMASupportBasis S) :
    lift S A (qmaSupportExtend S u) (qmaSupportExtend S v)=A u v := by
  have hu : (fun j : {j // j∈S} => qmaSupportExtend S u j.val)=u := by
    funext j
    exact dite_eq_left j.property
  have hv : (fun j : {j // j∈S} => qmaSupportExtend S v j.val)=v := by
    funext j
    exact dite_eq_left j.property
  have he : (fun j : {j // j∉S} => qmaSupportExtend S u j.val)=
      (fun j : {j // j∉S} => qmaSupportExtend S v j.val) := by
    funext j
    have hu0 : qmaSupportExtend S u j.val=0 := dite_eq_right j.property
    have hv0 : qmaSupportExtend S v j.val=0 := dite_eq_right j.property
    exact hu0.trans hv0.symm
  simp only [lift,hu,hv,identity,ite_eq_left he]
  apply value_injective
  simp only [value_mul,value_rat,Rat.cast_one,mul_one]

def oneReference (a b : Fin 2) (z : Scalar) : Scalar :=
  add (mul (identity a b) (QuantumAlgebraicScalar.realPart z))
    (mul (neg imaginary) (mul (QuantumFixedPauli.pauli 2 a b) (imagPart z)))

theorem rebit_entry_of_references {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (A : Matrix (ι → Fin 2) (ι → Fin 2) Scalar)
    (s t : Fin n ⊕ ι → Fin 2) (a b : Fin 2)
    (hs : s ∘ Sum.inl=referenceState n i a)
    (ht : t ∘ Sum.inl=referenceState n i b) :
    rebit n i A s t=oneReference a b (A (s ∘ Sum.inr) (t ∘ Sum.inr)) := by
  simp only [rebit,hs,ht,reference_identity,localY_referenceState,oneReference]

theorem rebit_lift_entry {ι : Type} [Fintype ι] [DecidableEq ι]
    (n : ℕ) (i : Fin n) (S : Finset ι)
    (A : Matrix (QMASupportBasis S) (QMASupportBasis S) Scalar)
    (a b : Fin 2) (u v : QMASupportBasis S) :
    rebit n i (lift S A)
      (Sum.elim (referenceState n i a) (qmaSupportExtend S u))
      (Sum.elim (referenceState n i b) (qmaSupportExtend S v))=
      oneReference a b (A u v) := by
  change add (mul (identity (referenceState n i a) (referenceState n i b))
      (QuantumAlgebraicScalar.realPart (lift S A (qmaSupportExtend S u) (qmaSupportExtend S v))))
    (mul (neg imaginary) (mul (localY n i (referenceState n i a) (referenceState n i b))
      (imagPart (lift S A (qmaSupportExtend S u) (qmaSupportExtend S v)))))=_
  rw [lift_extend,reference_identity,localY_referenceState]
  rfl

end ContinuumCoulomb.QuantumAlgebraicHistory

end

end OAI
