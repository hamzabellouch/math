import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumXZTerms
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFourTensorFullFamily

namespace OAI

/-! The actual word family splits into the three kinds of physical simulator terms. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

structure QMAXZPair (n : ℕ) where
  left : Fin n
  right : Fin n
  distinct : left ≠ right
  axisLeft : Fin 2
  axisRight : Fin 2

structure QMAXZField (n : ℕ) where
  site : Fin n
  axis : Fin 2

def QMAXZTerm.IsPair {n : ℕ} : QMAXZTerm n → Prop
  | .pair .. => True
  | _ => False

def QMAXZTerm.IsField {n : ℕ} : QMAXZTerm n → Prop
  | .field .. => True
  | _ => False

def QMAXZTerm.IsScalar {n : ℕ} : QMAXZTerm n → Prop
  | .scalar => True
  | _ => False

def QMAXZTerm.asPair {n : ℕ} (t : QMAXZTerm n) (h : t.IsPair) : QMAXZPair n := by
  cases t with
  | scalar => exact h.elim
  | field => exact h.elim
  | pair i j hij a b => exact ⟨i,j,hij,a,b⟩

def QMAXZTerm.asField {n : ℕ} (t : QMAXZTerm n) (h : t.IsField) : QMAXZField n := by
  cases t with
  | scalar => exact h.elim
  | field i a => exact ⟨i,a⟩
  | pair => exact h.elim

theorem QMAXZTerm.pair_matrix {n : ℕ} (t : QMAXZTerm n) (h : t.IsPair) :
    t.matrix = qmaPairMatrix (t.asPair h).left (t.asPair h).right
      (qmaFourAxis (t.asPair h).axisLeft) (qmaFourAxis (t.asPair h).axisRight) := by
  cases t <;> first | exact h.elim | rfl

theorem QMAXZTerm.field_matrix {n : ℕ} (t : QMAXZTerm n) (h : t.IsField) :
    t.matrix = qmaSiteMatrix (t.asField h).site (qmaFourAxis (t.asField h).axis) := by
  cases t <;> first | exact h.elim | rfl

theorem QMAXZTerm.scalar_matrix {n : ℕ} (t : QMAXZTerm n) (h : t.IsScalar) : t.matrix = 1 := by
  cases t <;> first | exact h.elim | rfl

theorem qmaXZLabel_ne_zero (a : Fin 2) : qmaXZLabel a ≠ 0 := by
  fin_cases a <;> decide

theorem QMAXZTerm.pair_support {n : ℕ} (t : QMAXZTerm n) (h : t.IsPair) :
    qmaPauliSupport t.word = {(t.asPair h).left,(t.asPair h).right} := by
  cases t with
  | scalar => exact h.elim
  | field => exact h.elim
  | pair i j hij a b =>
    change qmaPauliSupport (QMAXZTerm.pair i j hij a b).word = {i,j}
    apply Finset.ext
    intro k
    unfold qmaPauliSupport
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton,QMAXZTerm.word]
    by_cases hi : k = i
    · subst k
      simp only [ite_true,true_or,iff_true]
      exact qmaXZLabel_ne_zero a
    · by_cases hj : k = j
      · subst k
        simp only [hi,ite_false,ite_true,or_true,iff_true]
        exact qmaXZLabel_ne_zero b
      · simp only [hi,hj,ite_false,ne_eq,not_true_eq_false,or_self]

variable {n : ℕ} {κ : Type*} [Fintype κ]

abbrev QMAXZPairIndex (t : κ → QMAXZTerm n) := {e // (t e).IsPair}
abbrev QMAXZFieldIndex (t : κ → QMAXZTerm n) := {e // (t e).IsField}
abbrev QMAXZScalarIndex (t : κ → QMAXZTerm n) := {e // (t e).IsScalar}

def qmaXZPairData (t : κ → QMAXZTerm n) (e : QMAXZPairIndex t) : QMAXZPair n :=
  (t e.val).asPair e.property

def qmaXZFieldData (t : κ → QMAXZTerm n) (e : QMAXZFieldIndex t) : QMAXZField n :=
  (t e.val).asField e.property

omit [Fintype κ] in
theorem qmaXZPairData_distinct (t : κ → QMAXZTerm n)
    (hprivate : ∀ e f, (qmaPauliSupport (t e).word).card = 2 →
      qmaPauliSupport (t e).word = qmaPauliSupport (t f).word → e = f)
    (e f : QMAXZPairIndex t) (hef : e ≠ f) :
    ({(qmaXZPairData t e).left,(qmaXZPairData t e).right} : Finset (Fin n)) ≠
      {(qmaXZPairData t f).left,(qmaXZPairData t f).right} := by
  intro heq
  apply hef
  apply Subtype.ext
  apply hprivate e.val f.val
  · rw [(t e.val).pair_support e.property]
    exact Finset.card_pair ((qmaXZPairData t e).distinct)
  · rw [(t e.val).pair_support e.property,(t f.val).pair_support f.property]
    exact heq

theorem qmaSum_subtype_ite {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : α → M) :
    (∑ e : {x // p x}, f e.val) = ∑ e, if p e then f e else 0 := by
  have h := Fintype.sum_subtype_add_sum_subtype p (fun e => if p e then f e else 0)
  have hp : (∑ e : {x // p x}, if p e.val then f e.val else 0) = ∑ e : {x // p x}, f e.val := by
    apply Finset.sum_congr rfl
    intro e _
    exact ite_eq_left e.property
  have hn : (∑ e : {x // ¬p x}, if p e.val then f e.val else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact ite_eq_right e.property
  simpa only [hp,hn,add_zero] using h

theorem qmaXZFamily_split (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    (∑ e, (J e:ℂ) • (t e).matrix) =
      (∑ e : QMAXZPairIndex t, (J e.val:ℂ) • qmaPairMatrix
        (qmaXZPairData t e).left (qmaXZPairData t e).right
        (qmaFourAxis (qmaXZPairData t e).axisLeft) (qmaFourAxis (qmaXZPairData t e).axisRight))+
      (∑ e : QMAXZFieldIndex t, (J e.val:ℂ) • qmaSiteMatrix
        (qmaXZFieldData t e).site (qmaFourAxis (qmaXZFieldData t e).axis))+
      ((∑ e : QMAXZScalarIndex t, J e.val:ℝ):ℂ) • 1 := by
  have hp : (∑ e : QMAXZPairIndex t, (J e.val:ℂ) • (t e.val).matrix) =
      ∑ e : QMAXZPairIndex t, (J e.val:ℂ) • qmaPairMatrix
        (qmaXZPairData t e).left (qmaXZPairData t e).right
        (qmaFourAxis (qmaXZPairData t e).axisLeft) (qmaFourAxis (qmaXZPairData t e).axisRight) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [(t e.val).pair_matrix e.property]
    rfl
  have hf : (∑ e : QMAXZFieldIndex t, (J e.val:ℂ) • (t e.val).matrix) =
      ∑ e : QMAXZFieldIndex t, (J e.val:ℂ) • qmaSiteMatrix
        (qmaXZFieldData t e).site (qmaFourAxis (qmaXZFieldData t e).axis) := by
    apply Finset.sum_congr rfl
    intro e _
    rw [(t e.val).field_matrix e.property]
    rfl
  have hs : (∑ e : QMAXZScalarIndex t, (J e.val:ℂ) • (t e.val).matrix) =
      ((∑ e : QMAXZScalarIndex t, J e.val:ℝ):ℂ) • 1 := by
    rw [Complex.ofReal_sum,Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro e _
    rw [(t e.val).scalar_matrix e.property]
  rw [← hp,← hf,← hs]
  rw [qmaSum_subtype_ite (fun e => (t e).IsPair) (fun e => (J e:ℂ) • (t e).matrix),
    qmaSum_subtype_ite (fun e => (t e).IsField) (fun e => (J e:ℂ) • (t e).matrix),
    qmaSum_subtype_ite (fun e => (t e).IsScalar) (fun e => (J e:ℂ) • (t e).matrix)]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  cases t e <;> simp [QMAXZTerm.IsPair,QMAXZTerm.IsField,QMAXZTerm.IsScalar]

def qmaXZFamilyConstant (t : κ → QMAXZTerm n) (J : κ → ℝ) : ℝ :=
  (∑ e : QMAXZScalarIndex t, J e.val)-
    ∑ e : QMAXZPairIndex t, qmaFourEnergyOffset
      (qmaXZPairData t e).axisLeft (qmaXZPairData t e).axisRight (J e.val)

theorem qmaXZFamily_target (t : κ → QMAXZTerm n) (J : κ → ℝ) :
    qmaFourTensorFullTarget
      (fun e => (qmaXZPairData t e).left) (fun e => (qmaXZPairData t e).right)
      (fun e => (qmaXZPairData t e).axisLeft) (fun e => (qmaXZPairData t e).axisRight)
      (fun e => J e.val)
      (fun e => (qmaXZFieldData t e).site) (fun e => (qmaXZFieldData t e).axis)
      (fun e => J e.val) (qmaXZFamilyConstant t J) = ∑ e, (J e:ℂ) • (t e).matrix := by
  rw [qmaXZFamily_split t J]
  simp only [qmaFourTensorFullTarget,qmaFourTensorFamilyTarget,qmaXZFamilyConstant,Complex.ofReal_sub]
  module

end ContinuumCoulomb

end

end OAI
