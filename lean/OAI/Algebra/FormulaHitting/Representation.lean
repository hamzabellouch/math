import OAI.Algebra.FormulaHitting.Formula
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace OAI

namespace NCHitting

open Matrix

def automatonValue {F I : Type*} {n : ℕ} [Semiring F] [Fintype I]
    (B : Fin n → Matrix I I F) (u v : I → F) : Word n → F
  | [] => u ⬝ᵥ v
  | i :: w => automatonValue B (u ᵥ* B i) v w

theorem automatonValue_add {F I : Type*} {n : ℕ} [Semiring F] [Fintype I]
    (B : Fin n → Matrix I I F) (u u' v : I → F) (w : Word n) :
    automatonValue B (u + u') v w =
      automatonValue B u v w + automatonValue B u' v w := by
  induction w generalizing u u' with
  | nil => simp [automatonValue, add_dotProduct]
  | cons i w ih => simp [automatonValue, add_vecMul, ih]

theorem automatonValue_smul {F I : Type*} {n : ℕ} [CommSemiring F] [Fintype I]
    (B : Fin n → Matrix I I F) (a : F) (u v : I → F) (w : Word n) :
    automatonValue B (a • u) v w = a * automatonValue B u v w := by
  induction w generalizing u with
  | nil => simp [automatonValue, smul_dotProduct]
  | cons i w ih => simp [automatonValue, smul_vecMul, ih]

theorem automatonValue_zero {F I : Type*} {n : ℕ} [Semiring F] [Fintype I]
    (B : Fin n → Matrix I I F) (v : I → F) (w : Word n) :
    automatonValue B 0 v w = 0 := by
  induction w with
  | nil => simp [automatonValue]
  | cons i w ih => simp [automatonValue, ih]

def wordMatrix {F I : Type*} {n : ℕ} [Semiring F] [Fintype I] [DecidableEq I]
    (B : Fin n → Matrix I I F) (w : Word n) : Matrix I I F :=
  (w.map B).prod

theorem automatonValue_eq_matrix {F I : Type*} {n : ℕ}
    [Semiring F] [Fintype I] [DecidableEq I]
    (B : Fin n → Matrix I I F) (u v : I → F) (w : Word n) :
    automatonValue B u v w = u ⬝ᵥ (wordMatrix B w *ᵥ v) := by
  induction w generalizing u with
  | nil => simp [automatonValue, wordMatrix]
  | cons i w ih =>
    simp only [automatonValue, ih, wordMatrix, List.map_cons, List.prod_cons]
    rw [← dotProduct_mulVec, mulVec_mulVec]

theorem automatonValue_sumBlocks {F I J : Type*} {n : ℕ}
    [Semiring F] [Fintype I] [Fintype J]
    (A : Fin n → Matrix I I F) (B : Fin n → Matrix J J F)
    (u v : I → F) (u' v' : J → F) (w : Word n) :
    automatonValue (fun i => fromBlocks (A i) 0 0 (B i))
        (Sum.elim u u') (Sum.elim v v') w =
      automatonValue A u v w + automatonValue B u' v' w := by
  induction w generalizing u u' with
  | nil => simp [automatonValue, sumElim_dotProduct_sumElim]
  | cons i w ih =>
    simpa [automatonValue, vecMul_fromBlocks, Function.comp_def] using
      ih (u ᵥ* A i) (u' ᵥ* B i)

def productTransition {F I J : Type*} {n : ℕ}
    [Semiring F] [Fintype J]
    (A : Fin n → Matrix I I F) (B : Fin n → Matrix J J F)
    (v : I → F) (u' : J → F) (i : Fin n) : Matrix (I ⊕ J) (I ⊕ J) F :=
  fromBlocks (A i) (vecMulVec v (u' ᵥ* B i)) 0 (B i)

theorem automatonValue_productBlocks_general {F I J : Type*} {n : ℕ}
    [CommSemiring F] [Fintype I] [Fintype J]
    (A : Fin n → Matrix I I F) (B : Fin n → Matrix J J F)
    (u v : I → F) (u' b v' : J → F) (w : Word n) :
    automatonValue (productTransition A B v u') (Sum.elim u b)
        (Sum.elim ((u' ⬝ᵥ v') • v) v') w =
      convolution (automatonValue A u v) (automatonValue B u' v') w +
        automatonValue B b v' w := by
  induction w generalizing u b with
  | nil =>
    simp [automatonValue, convolution, sumElim_dotProduct_sumElim,
      dotProduct_smul, mul_comm]
  | cons i w ih =>
    rw [automatonValue]
    simp only [productTransition, vecMul_fromBlocks, Function.comp_def,
      Sum.elim_inl, Sum.elim_inr, vecMul_zero, add_zero, vecMul_vecMulVec]
    rw [ih, automatonValue_add, automatonValue_smul]
    simp only [convolution, automatonValue]
    ac_rfl

theorem automatonValue_productBlocks {F I J : Type*} {n : ℕ}
    [CommSemiring F] [Fintype I] [Fintype J]
    (A : Fin n → Matrix I I F) (B : Fin n → Matrix J J F)
    (u v : I → F) (u' v' : J → F) (w : Word n) :
    automatonValue (productTransition A B v u') (Sum.elim u 0)
        (Sum.elim ((u' ⬝ᵥ v') • v) v') w =
      convolution (automatonValue A u v) (automatonValue B u' v') w := by
  rw [automatonValue_productBlocks_general, automatonValue_zero, add_zero]

structure AcyclicRepresentation (F : Type*) (n : ℕ) [CommSemiring F] where
  State : Type
  [fintype : Fintype State]
  [decidableEq : DecidableEq State]
  u : State → F
  v : State → F
  B : Fin n → Matrix State State F
  rank : State → ℕ
  rank_lt : ∀ a, rank a < Fintype.card State
  upper : ∀ i a b, rank b ≤ rank a → B i a b = 0

attribute [instance] AcyclicRepresentation.fintype AcyclicRepresentation.decidableEq

namespace AcyclicRepresentation

variable {F : Type*} {n : ℕ} [CommSemiring F]

def value (R : AcyclicRepresentation F n) : WordSeries F n :=
  automatonValue R.B R.u R.v

theorem wordMatrix_entry_zero (R : AcyclicRepresentation F n)
    (w : Word n) (a b : R.State) (h : R.rank b < R.rank a + w.length) :
    wordMatrix R.B w a b = 0 := by
  induction w generalizing a with
  | nil =>
    have hne : a ≠ b := by intro he; subst b; simp at h
    simp [wordMatrix, hne]
  | cons i w ih =>
    simp only [wordMatrix, List.map_cons, List.prod_cons, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    by_cases hc : R.rank c ≤ R.rank a
    · rw [R.upper i a c hc, zero_mul]
    · have hbc : R.rank b < R.rank c + w.length := by
        simp only [List.length_cons] at h
        omega
      rw [show (List.map R.B w).prod c b = 0 from ih c hbc, mul_zero]

theorem wordMatrix_eq_zero (R : AcyclicRepresentation F n)
    (w : Word n) (h : Fintype.card R.State ≤ w.length) : wordMatrix R.B w = 0 := by
  ext a b
  apply R.wordMatrix_entry_zero w a b
  have hb := R.rank_lt b
  omega

theorem value_eq_matrix (R : AcyclicRepresentation F n) (w : Word n) :
    R.value w = R.u ⬝ᵥ (wordMatrix R.B w *ᵥ R.v) :=
  automatonValue_eq_matrix R.B R.u R.v w

def sumRank (R S : AcyclicRepresentation F n) : R.State ⊕ S.State → ℕ :=
  Sum.elim R.rank (fun a => Fintype.card R.State + S.rank a)

theorem sumRank_lt (R S : AcyclicRepresentation F n) (a : R.State ⊕ S.State) :
    sumRank R S a < Fintype.card (R.State ⊕ S.State) := by
  cases a with
  | inl a =>
    have h := R.rank_lt a
    simp only [sumRank, Sum.elim_inl, Fintype.card_sum]
    omega
  | inr a =>
    have h := S.rank_lt a
    simp only [sumRank, Sum.elim_inr, Fintype.card_sum]
    omega

theorem block_upper (R S : AcyclicRepresentation F n)
    (C : Fin n → Matrix R.State S.State F) (i : Fin n)
    (a b : R.State ⊕ S.State) (h : sumRank R S b ≤ sumRank R S a) :
    fromBlocks (R.B i) (C i) 0 (S.B i) a b = 0 := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact R.upper i a b h
    | inr b =>
      have ha := R.rank_lt a
      simp only [sumRank, Sum.elim_inl, Sum.elim_inr] at h
      omega
  | inr a =>
    cases b with
    | inl b => rfl
    | inr b =>
      apply S.upper i a b
      simp only [sumRank, Sum.elim_inr] at h
      omega

def add (R S : AcyclicRepresentation F n) : AcyclicRepresentation F n where
  State := R.State ⊕ S.State
  fintype := inferInstance
  decidableEq := inferInstance
  u := Sum.elim R.u S.u
  v := Sum.elim R.v S.v
  B i := fromBlocks (R.B i) 0 0 (S.B i)
  rank := sumRank R S
  rank_lt := sumRank_lt R S
  upper := block_upper R S (fun _ => 0)

theorem add_value (R S : AcyclicRepresentation F n) (w : Word n) :
    (R.add S).value w = R.value w + S.value w :=
  automatonValue_sumBlocks R.B S.B R.u R.v S.u S.v w

def mul (R S : AcyclicRepresentation F n) : AcyclicRepresentation F n where
  State := R.State ⊕ S.State
  fintype := inferInstance
  decidableEq := inferInstance
  u := Sum.elim R.u 0
  v := Sum.elim ((S.u ⬝ᵥ S.v) • R.v) S.v
  B := productTransition R.B S.B R.v S.u
  rank := sumRank R S
  rank_lt := sumRank_lt R S
  upper := block_upper R S (fun i => vecMulVec R.v (S.u ᵥ* S.B i))

theorem mul_value (R S : AcyclicRepresentation F n) (w : Word n) :
    (R.mul S).value w = convolution R.value S.value w :=
  automatonValue_productBlocks R.B S.B R.u R.v S.u S.v w

def scalar (a : F) : AcyclicRepresentation F n where
  State := Unit
  fintype := inferInstance
  decidableEq := inferInstance
  u _ := a
  v _ := 1
  B _ := 0
  rank _ := 0
  rank_lt _ := by simp
  upper _ _ _ _ := rfl

theorem scalar_value (a : F) (w : Word n) :
    (scalar (n := n) a).value w = if w = [] then a else 0 := by
  cases w with
  | nil =>
    change (∑ _ : Unit, a * 1) = a
    simp
  | cons i w =>
    change automatonValue (fun _ : Fin n => (0 : Matrix Unit Unit F))
      ((fun _ : Unit => a) ᵥ* 0) (fun _ => 1) w = 0
    rw [vecMul_zero, automatonValue_zero]

def ofVariable (i : Fin n) : AcyclicRepresentation F n where
  State := Fin 2
  fintype := inferInstance
  decidableEq := inferInstance
  u a := if a = 0 then 1 else 0
  v a := if a = 1 then 1 else 0
  B j a b := if a = 0 ∧ b = 1 ∧ j = i then 1 else 0
  rank a := a.val
  rank_lt a := by simp
  upper j a b h := by
    by_cases hab : a = 0 ∧ b = 1 ∧ j = i
    · rcases hab with ⟨rfl, rfl, _⟩
      simp at h
    · simp [hab]

theorem variable_value (i : Fin n) (w : Word n) :
    (ofVariable (F := F) i).value w = if w = [i] then 1 else 0 := by
  change automatonValue
    (fun j (a b : Fin 2) => if a = 0 ∧ b = 1 ∧ j = i then (1 : F) else 0)
    (fun a : Fin 2 => if a = 0 then 1 else 0)
    (fun a : Fin 2 => if a = 1 then 1 else 0) w = _
  cases w with
  | nil => simp [automatonValue, dotProduct]
  | cons j w =>
    cases w with
    | nil =>
      simp [automatonValue, vecMul, dotProduct, Fin.sum_univ_two]
    | cons k w =>
      have hz : ((ofVariable (F := F) i).u ᵥ* (ofVariable i).B j) ᵥ*
          (ofVariable i).B k = 0 := by
        change ((fun a : Fin 2 => if a = 0 then (1 : F) else 0) ᵥ*
          (fun a b : Fin 2 => if a = 0 ∧ b = 1 ∧ j = i then 1 else 0)) ᵥ*
          (fun a b : Fin 2 => if a = 0 ∧ b = 1 ∧ k = i then 1 else 0) = 0
        ext a
        change _ = (0 : F)
        fin_cases a <;>
          simp [vecMul, dotProduct, Fin.sum_univ_two]
      rw [ite_eq_right (show (j :: k :: w : Word n) ≠ [i] by simp)]
      change automatonValue (ofVariable (F := F) i).B
        (((ofVariable i).u ᵥ* (ofVariable i).B j) ᵥ* (ofVariable i).B k)
        (ofVariable i).v w = 0
      rw [hz, automatonValue_zero]

@[simp] theorem scalar_card (a : F) : Fintype.card (scalar (n := n) a).State = 1 := rfl

@[simp] theorem variable_card (i : Fin n) :
    Fintype.card (ofVariable (F := F) i).State = 2 := rfl

@[simp] theorem add_card (R S : AcyclicRepresentation F n) :
    Fintype.card (R.add S).State = Fintype.card R.State + Fintype.card S.State :=
  Fintype.card_sum

@[simp] theorem mul_card (R S : AcyclicRepresentation F n) :
    Fintype.card (R.mul S).State = Fintype.card R.State + Fintype.card S.State :=
  Fintype.card_sum

end AcyclicRepresentation

noncomputable def Formula.representation {F : Type*} {n : ℕ} [CommSemiring F] :
    Formula F n → AcyclicRepresentation F n
  | .scalar a => .scalar a
  | .var i => .ofVariable i
  | .add f g => f.representation.add g.representation
  | .mul f g => f.representation.mul g.representation

theorem Formula.representation_card_le {F : Type*} {n : ℕ} [CommSemiring F]
    (f : Formula F n) : Fintype.card f.representation.State ≤ 2 * f.size := by
  induction f with
  | scalar a => change 1 ≤ 2 * 1; decide
  | var i => change 2 ≤ 2 * 1; decide
  | add f g ihf ihg =>
    change Fintype.card (f.representation.State ⊕ g.representation.State) ≤
      2 * (f.size + g.size + 1)
    rw [Fintype.card_sum]
    omega
  | mul f g ihf ihg =>
    change Fintype.card (f.representation.State ⊕ g.representation.State) ≤
      2 * (f.size + g.size + 1)
    rw [Fintype.card_sum]
    omega

theorem Formula.representation_card_pos {F : Type*} {n : ℕ} [CommSemiring F]
    (f : Formula F n) : 0 < Fintype.card f.representation.State := by
  induction f with
  | scalar a => change 0 < 1; decide
  | var i => change 0 < 2; decide
  | add f g ihf ihg =>
    change 0 < Fintype.card (f.representation.State ⊕ g.representation.State)
    rw [Fintype.card_sum]
    omega
  | mul f g ihf ihg =>
    change 0 < Fintype.card (f.representation.State ⊕ g.representation.State)
    rw [Fintype.card_sum]
    omega

theorem Formula.representation_correct {F : Type*} {n : ℕ} [CommSemiring F]
    (f : Formula F n) (w : Word n) : f.representation.value w = f.coeff w := by
  induction f generalizing w with
  | scalar a => exact AcyclicRepresentation.scalar_value a w
  | var i => exact AcyclicRepresentation.variable_value i w
  | add f g ihf ihg =>
    simp only [Formula.representation, AcyclicRepresentation.add_value,
      Formula.coeff, ihf, ihg]
  | mul f g ihf ihg =>
    simp only [Formula.representation, AcyclicRepresentation.mul_value, Formula.coeff]
    congr 1 <;> funext w <;> first | exact ihf w | exact ihg w

theorem Formula.coeff_zero_of_representation_dimension_le
    {F : Type*} {n : ℕ} [CommSemiring F] (f : Formula F n) (w : Word n)
    (h : Fintype.card f.representation.State ≤ w.length) : f.coeff w = 0 := by
  rw [← f.representation_correct w, f.representation.value_eq_matrix,
    f.representation.wordMatrix_eq_zero w h]
  simp

end NCHitting

end OAI
