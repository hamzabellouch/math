import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialBranchFamilies
import OAI.Combinatorics.ThinTrees.Arithmetic.UnaryArithmetic
import OAI.Combinatorics.ThinTrees.Continuation.Interior

namespace OAI

/-! Finite families. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_dite {α β : Type*} {ea : α → Word} {eb : β → Word}
    {P : α → Prop} [DecidablePred P]
    {f : {a // P a} → β} {g : {a // ¬P a} → β}
    (test : Realizes ea boolCode (fun a => decide (P a)))
    (r : Realizes (fun a : {a // P a} => ea a.val) eb f)
    (s : Realizes (fun a : {a // ¬P a} => ea a.val) eb g)
    [PolyTime test] [PolyTime r] [PolyTime s] : PolyTime (test.dite r s) := by
  refine ⟨?_⟩
  exact (RunsPoly.dite_families
    (RunsPoly.of_poly test id (isPoly_self (fun a => (ea a).length)))
    (RunsPoly.of_poly r id (isPoly_self (fun a : {a // P a} => (ea a.val).length)))
    (RunsPoly.of_poly s id (isPoly_self (fun a : {a // ¬P a} => (ea a.val).length)))).cost

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
variable {I J : α → Type*} {n m : α → ℕ}

def indexedCode (ea : α → Word) (e : (a : α) → I a ≃ Fin (n a)) (p : Σ a,I a) : Word :=
  prodCode ea natCode (p.1,(e p.1 p.2).val)

def indexedFirst (e : (a : α) → I a ≃ Fin (n a)) :
    Realizes (indexedCode ea e) ea (fun p => p.1) :=
  (first ea natCode).reindex (indexedCode ea e) (fun p => (p.1,(e p.1 p.2).val))
    (fun _ => rfl)
def indexedIndex (e : (a : α) → I a ≃ Fin (n a)) :
    Realizes (indexedCode ea e) natCode (fun p => (e p.1 p.2).val) :=
  (second ea natCode).reindex (indexedCode ea e) (fun p => (p.1,(e p.1 p.2).val))
    (fun _ => rfl)
instance poly_indexedFirst (e : (a : α) → I a ≃ Fin (n a)) :
    PolyTime (indexedFirst (ea:=ea) e) := by unfold indexedFirst;apply poly_reindex
instance poly_indexedIndex (e : (a : α) → I a ≃ Fin (n a)) :
    PolyTime (indexedIndex (ea:=ea) e) := by unfold indexedIndex;apply poly_reindex

def Realizes.tabulateIndexed {e : (a : α) → I a ≃ Fin (n a)} {f : (Σ a,I a) → β}
    (r : Realizes (indexedCode ea e) eb f) (rn : Realizes ea natCode n) :
    Realizes ea (listCode eb) (fun a => List.ofFn (fun i => f ⟨a,(e a).symm i⟩)) :=
  (r.reindex (finFamilyCode ea n) (fun p => ⟨p.1,(e p.1).symm p.2⟩)
    (fun p => by simp only [indexedCode,finFamilyCode,Equiv.apply_symm_apply])).tabulateFin rn
instance poly_tabulateIndexed {e : (a : α) → I a ≃ Fin (n a)} {f : (Σ a,I a) → β}
    (r : Realizes (indexedCode ea e) eb f) (rn : Realizes ea natCode n)
    [PolyTime r] [PolyTime rn] : PolyTime (r.tabulateIndexed rn) := by
  unfold Realizes.tabulateIndexed
  refine @poly_tabulateFin _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_reindex
  · infer_instance

def sumEquiv (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (a : α) : I a ⊕ J a ≃ Fin (n a+m a) :=
  ((e a).sumCongr (e' a)).trans finSumFinEquiv

def sumLeft (_e : (a : α) → I a ≃ Fin (n a)) (_e' : (a : α) → J a ≃ Fin (m a))
    (p : {p : Σ a,I a ⊕ J a // p.2.isLeft=true}) : Σ a,I a :=
  ⟨p.val.1,p.val.2.getLeft p.property⟩
def sumRight (_e : (a : α) → I a ≃ Fin (n a)) (_e' : (a : α) → J a ≃ Fin (m a))
    (p : {p : Σ a,I a ⊕ J a // ¬p.2.isLeft=true}) : Σ a,J a :=
  ⟨p.val.1,p.val.2.getRight (by have hp := p.property; cases h : p.val.2 <;> simp_all)⟩

lemma sumLeft_code (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (p : {p : Σ a,I a ⊕ J a // p.2.isLeft=true}) :
    indexedCode ea (sumEquiv e e') p.val=indexedCode ea e (sumLeft e e' p) := by
  rcases p with ⟨⟨a,i|j⟩,h⟩
  · rfl
  · simp at h

lemma sumRight_index (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (p : {p : Σ a,I a ⊕ J a // ¬p.2.isLeft=true}) :
    (sumEquiv e e' p.val.1 p.val.2).val-n p.val.1=
      (e' (sumRight e e' p).1 (sumRight e e' p).2).val := by
  rcases p with ⟨⟨a,i|j⟩,h⟩
  · simp at h
  · change n a+(e' a j).val-n a=(e' a j).val
    omega

def indexedSumTest (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (rn : Realizes ea natCode n) :
    Realizes (indexedCode ea (sumEquiv e e')) boolCode
      (fun p => decide (p.2.isLeft=true)) :=
  ((indexedIndex (sumEquiv e e')).nlt ((indexedFirst (sumEquiv e e')).then rn)).congr (by
    rintro ⟨a,i|j⟩
    · change decide ((e a i).val<n a)=decide (true=true)
      simp [(e a i).isLt]
    · change decide (n a+(e' a j).val<n a)=decide (false=true)
      simp)
instance poly_indexedSumTest (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rn : Realizes ea natCode n) [PolyTime rn] :
    PolyTime (indexedSumTest e e' rn) := by unfold indexedSumTest;infer_instance

def indexedSumRight (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (rn : Realizes ea natCode n) :
    Realizes (fun p : {p : Σ a,I a ⊕ J a // ¬p.2.isLeft=true} =>
      indexedCode ea (sumEquiv e e') p.val) (indexedCode ea e') (sumRight e e') :=
  let view := (identity (indexedCode ea (sumEquiv e e'))).reindex
    (fun p : {p : Σ a,I a ⊕ J a // ¬p.2.isLeft=true} => indexedCode ea (sumEquiv e e') p.val)
    Subtype.val (fun _ => rfl)
  let a := view.then (indexedFirst (sumEquiv e e'))
  let i := view.then (indexedIndex (sumEquiv e e'))
  (a.both (i.nsub (a.then rn))).changeOutput (indexedCode ea e') (sumRight e e') (by
    intro p
    change prodCode ea natCode (p.val.1,(sumEquiv e e' p.val.1 p.val.2).val-n p.val.1) =
      prodCode ea natCode ((sumRight e e' p).1,(e' (sumRight e e' p).1 (sumRight e e' p).2).val)
    rw [sumRight_index]
    rfl)
instance poly_indexedSumRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rn : Realizes ea natCode n) [PolyTime rn] :
    PolyTime (indexedSumRight e e' rn) := by unfold indexedSumRight;infer_instance

def Realizes.sumCases {e : (a : α) → I a ≃ Fin (n a)}
    {e' : (a : α) → J a ≃ Fin (m a)} {f : (Σ a,I a) → β} {g : (Σ a,J a) → β}
    (r : Realizes (indexedCode ea e) eb f) (s : Realizes (indexedCode ea e') eb g)
    (rn : Realizes ea natCode n) :
    Realizes (indexedCode ea (sumEquiv e e')) eb
      (fun p => p.2.elim (fun i => f ⟨p.1,i⟩) (fun j => g ⟨p.1,j⟩)) :=
  ((indexedSumTest e e' rn).dite
    (r.reindex (fun p : {p : Σ a,I a ⊕ J a // p.2.isLeft=true} =>
      indexedCode ea (sumEquiv e e') p.val) (sumLeft e e') (sumLeft_code e e'))
    ((indexedSumRight e e' rn).then s)).congr (by
      rintro ⟨a,i|j⟩ <;> simp [sumLeft,sumRight])
instance poly_sumCases {e : (a : α) → I a ≃ Fin (n a)}
    {e' : (a : α) → J a ≃ Fin (m a)} {f : (Σ a,I a) → β} {g : (Σ a,J a) → β}
    (r : Realizes (indexedCode ea e) eb f) (s : Realizes (indexedCode ea e') eb g)
    (rn : Realizes ea natCode n) [PolyTime r] [PolyTime s] [PolyTime rn] :
    PolyTime (r.sumCases s rn) := by unfold Realizes.sumCases;infer_instance

def prodEquiv (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (a : α) : I a × J a ≃ Fin (n a*m a) :=
  ((e a).prodCongr (e' a)).trans finProdFinEquiv

def splitProduct (e : (a : α) → I a ≃ Fin (n a)) (e' : (a : α) → J a ≃ Fin (m a))
    (rm : Realizes ea natCode m) :
    Realizes (indexedCode ea (prodEquiv e e'))
      (indexedCode (indexedCode ea e) (fun p : Σ a,I a => e' p.1))
      (fun p => ⟨⟨p.1,p.2.1⟩,p.2.2⟩) :=
  let a := indexedFirst (ea:=ea) (prodEquiv e e')
  let i := indexedIndex (ea:=ea) (prodEquiv e e')
  (((a.both (i.ndiv (a.then rm))).both (i.nmod (a.then rm)))).changeOutput
    (indexedCode (indexedCode ea e) (fun p : Σ a,I a => e' p.1))
    (fun p => ⟨⟨p.1,p.2.1⟩,p.2.2⟩) (by
      rintro ⟨a,i,j⟩
      have hj := (e' a j).isLt
      have hm : 0 < m a := by omega
      change prodCode (prodCode ea natCode) natCode
        ((a,((e' a j).val+m a*(e a i).val)/m a),
          ((e' a j).val+m a*(e a i).val)%m a)=
        prodCode (prodCode ea natCode) natCode ((a,(e a i).val),(e' a j).val)
      simp [Nat.add_mul_div_left _ _ hm,Nat.add_mod,Nat.div_eq_of_lt hj,Nat.mod_eq_of_lt hj])
instance poly_splitProduct (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (splitProduct e e' rm) := by unfold splitProduct;infer_instance

def Realizes.prodCases {e : (a : α) → I a ≃ Fin (n a)}
    {e' : (a : α) → J a ≃ Fin (m a)} {f : (Σ p : (Σ a,I a),J p.1) → β}
    (r : Realizes (indexedCode (indexedCode ea e) (fun p : Σ a,I a => e' p.1)) eb f)
    (rm : Realizes ea natCode m) :
    Realizes (indexedCode ea (prodEquiv e e')) eb (fun p => f ⟨⟨p.1,p.2.1⟩,p.2.2⟩) :=
  (splitProduct e e' rm).then r
instance poly_prodCases {e : (a : α) → I a ≃ Fin (n a)}
    {e' : (a : α) → J a ≃ Fin (m a)} {f : (Σ p : (Σ a,I a),J p.1) → β}
    (r : Realizes (indexedCode (indexedCode ea e) (fun p : Σ a,I a => e' p.1)) eb f)
    (rm : Realizes ea natCode m) [PolyTime r] [PolyTime rm] :
    PolyTime (r.prodCases rm) := by unfold Realizes.prodCases;infer_instance

def indexedProductLeft (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) :
    Realizes (indexedCode ea (prodEquiv e e')) (indexedCode ea e)
      (fun p => ⟨p.1,p.2.1⟩) :=
  (splitProduct e e' rm).then (indexedFirst (fun p : Σ a,I a => e' p.1))
instance poly_indexedProductLeft (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (indexedProductLeft e e' rm) := by unfold indexedProductLeft;infer_instance

def indexedProductRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) :
    Realizes (indexedCode ea (prodEquiv e e')) (indexedCode ea e')
      (fun p => ⟨p.1,p.2.2⟩) :=
  let s := splitProduct e e' rm
  let a := s.then (indexedFirst (fun p : Σ a,I a => e' p.1)) |>.then (indexedFirst e)
  let i := s.then (indexedIndex (fun p : Σ a,I a => e' p.1))
  (a.both i).changeOutput (indexedCode ea e') (fun p => ⟨p.1,p.2.2⟩) (fun _ => rfl)
instance poly_indexedProductRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (indexedProductRight e e' rm) := by unfold indexedProductRight;apply poly_changeOutput

def Realizes.not {P : α → Prop} [DecidablePred P]
    (r : Realizes ea boolCode (fun a => decide (P a))) :
    Realizes ea boolCode (fun a => decide (¬ P a)) :=
  (r.ite (constant ea boolCode false) (constant ea boolCode true)).congr (by intro a;simp)
instance poly_not {P : α → Prop} [DecidablePred P]
    (r : Realizes ea boolCode (fun a => decide (P a))) [PolyTime r] : PolyTime r.not := by
  unfold Realizes.not;infer_instance

def Realizes.and {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) :
    Realizes ea boolCode (fun a => decide (P a ∧ Q a)) :=
  (r.ite s (constant ea boolCode false)).congr (by intro a;simp)
instance poly_and {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) [PolyTime r] [PolyTime s] : PolyTime (r.and s) := by
  unfold Realizes.and;infer_instance

def Realizes.finEq {n : α → ℕ} {f g : (a : α) → Fin (n a)}
    (r : Realizes ea natCode (fun a => (f a).val))
    (s : Realizes ea natCode (fun a => (g a).val)) :
    Realizes ea boolCode (fun a => decide (f a=g a)) :=
  (r.neq s).congr (by intro a;simp only [Fin.ext_iff])
instance poly_finEq {n : α → ℕ} {f g : (a : α) → Fin (n a)}
    (r : Realizes ea natCode (fun a => (f a).val))
    (s : Realizes ea natCode (fun a => (g a).val)) [PolyTime r] [PolyTime s] :
    PolyTime (r.finEq s) := by unfold Realizes.finEq;infer_instance
end CurrentKS.Realization
end

end OAI
