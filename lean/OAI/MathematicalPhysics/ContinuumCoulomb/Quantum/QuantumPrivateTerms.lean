import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawCompiler

namespace OAI

/-! Explicit private mediator terms; no support-selection oracle is needed. -/

noncomputable section
namespace ContinuumCoulomb.QuantumPrivate
open Matrix
open scoped BigOperators Classical

variable {n m : ℕ}

def left (t : QMAXZTerm n) : QMAXZTerm n :=
  match t with
  | .scalar => .scalar
  | .field i a => .field i a
  | .pair i _ _ a _ => .field i a

def right (t : QMAXZTerm n) : QMAXZTerm n :=
  match t with
  | .pair _ j _ _ b => .field j b
  | _ => .scalar

theorem factor (t : QMAXZTerm n) :
    qmaPauliWord (left t).word*qmaPauliWord (right t).word = t.matrix := by
  rw [QMAXZTerm.word_matrix,QMAXZTerm.word_matrix]
  cases t with
  | scalar => simp [left,right,QMAXZTerm.matrix]
  | field i a => simp [left,right,QMAXZTerm.matrix]
  | pair i j hij a b =>
    exact (qmaPairMatrix_eq_mul i j hij (qmaFourAxis a) (qmaFourAxis b)).symm

theorem disjoint (t : QMAXZTerm n) :
    Disjoint (qmaPauliSupport (left t).word) (qmaPauliSupport (right t).word) := by
  cases t with
  | scalar => simp [left,right,QMAXZTerm.word,qmaPauliSupport]
  | field i a => simp [left,right,QMAXZTerm.word,qmaPauliSupport]
  | pair i j hij a b =>
    change Disjoint (qmaPauliSupport (qmaSinglePauliWord i (qmaXZLabel a)))
      (qmaPauliSupport (qmaSinglePauliWord j (qmaXZLabel b)))
    exact (Finset.disjoint_singleton.mpr hij).mono
      (qmaSinglePauliWord_support _ _) (qmaSinglePauliWord_support _ _)

def old (i : Fin n) : Fin (n+m) := finSumFinEquiv (Sum.inl i)
def fresh (e : Fin m) : Fin (n+m) := finSumFinEquiv (Sum.inr e)

theorem old_ne_fresh (i : Fin n) (e : Fin m) : old i ≠ fresh e := by
  intro h
  have h' := finSumFinEquiv.injective h
  cases h'

def term (e : Fin m) (t : QMAXZTerm n) (k : Fin 4) : QMAXZTerm (n+m) :=
  if k = 0 then .scalar else if k = 1 then .field (fresh e) 1 else if k = 2 then
    match t with
    | .scalar => .field (fresh e) 0
    | .field i a => .pair (old i) (fresh e) (old_ne_fresh i e) a 0
    | .pair i _ _ a _ => .pair (old i) (fresh e) (old_ne_fresh i e) a 0
  else
    match t with
    | .pair _ j _ _ b => .pair (old j) (fresh e) (old_ne_fresh j e) b 0
    | _ => .field (fresh e) 0

theorem term_word (e : Fin m) (t : QMAXZTerm n) (k : Fin 4) (i : Fin n ⊕ Fin m) :
    (term e t k).word (finSumFinEquiv i) =
      qmaXZSubdivisionWord (left t).word (right t).word e k i := by
  have hl (i : Fin n) (j : Fin m) : Fin.castAdd m i ≠ Fin.natAdd n j := old_ne_fresh i j
  have hr (j : Fin m) (i : Fin n) : Fin.natAdd n j ≠ Fin.castAdd m i := (hl i j).symm
  fin_cases k <;> cases t <;> cases i <;>
    simp [term,left,right,old,fresh,QMAXZTerm.word,qmaXZSubdivisionWord,qmaSinglePauliWord,
      qmaXZLabel,hl,hr]

def weight (R J : ℚ) (k : Fin 4) : ℚ := ![R^2/2+1+(J/2)^2,-R^2/2,R,-R*J/2] k

theorem weight_cast (R J : ℚ) (k : Fin 4) :
    (weight R J k:ℝ) = qmaXZSubdivisionWeight (R:ℝ) (J:ℝ) k := by
  fin_cases k <;> simp [weight,qmaXZSubdivisionWeight]

def budget {κ : Type*} [Fintype κ] (J : κ → ℚ) : ℚ := 4*(1+∑ e, (1+|J e|)^2)
def scale {κ : Type*} [Fintype κ] (N : ℕ) (J : κ → ℚ) : ℚ := 8*(budget J)^4*N

theorem budget_cast {κ : Type*} [Fintype κ] (J : κ → ℚ) :
    (budget J:ℝ) = qmaThirdBudget 0 (fun e => (J e:ℝ)) := by
  simp [budget,qmaThirdBudget,qmaThirdWeight]

theorem scale_cast {κ : Type*} [Fintype κ] (N : ℕ) (J : κ → ℚ) :
    (scale N J:ℝ) = 8*(qmaThirdBudget 0 (fun e => (J e:ℝ)))^4*N := by
  simp only [scale,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,budget_cast]

end ContinuumCoulomb.QuantumPrivate

end

end OAI
