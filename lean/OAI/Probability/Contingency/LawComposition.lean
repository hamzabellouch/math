import Mathlib
import OAI.Probability.Contingency.DyadicLaws

namespace OAI

/-! Law Composition. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
namespace Contingency.Law
noncomputable section
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

theorem pure_bind (x : α) (f : α → Law β) : (pure x).bind f=f x := by
  classical
  apply Law.ext; funext y
  simp [bind,pure]

theorem bind_assoc (p : Law α) (f : α → Law β) (g : β → Law γ) :
    (p.bind f).bind g=p.bind (fun x => (f x).bind g) := by
  apply Law.ext; funext y
  simp only [bind,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  exact Finset.sum_comm

theorem map_bind (p : Law α) (f : α → β) (g : β → Law γ) :
    (p.map f).bind g=p.bind (fun x => g (f x)) := by
  simp only [map,bind_assoc,pure_bind]

theorem map_map (p : Law α) (f : α → β) (g : β → γ) :
    (p.map f).map g=p.map (fun x => g (f x)) := by
  change (p.map f).bind _=_
  rw [map_bind]
  rfl

end
end Contingency.Law

 

 

open scoped BigOperators
open Filter

namespace Contingency

 
def Tables {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :=
  {X : Fin m → Fin n → ℕ //
    (∀ i, ∑ j, X i j = r i) ∧ (∀ j, ∑ i, X i j = c j)}

instance tablesFinite {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Finite (Tables r c) := by
  let f : Tables r c → (i : Fin m) → Fin n → Fin (r i + 1) :=
    fun X i j => ⟨X.val i j, by
      have := Finset.single_le_sum (fun (j : Fin n) _ => Nat.zero_le (X.val i j))
        (Finset.mem_univ j)
      rw [X.property.1 i] at this
      omega⟩
  apply Finite.of_injective f
  intro X Y h
  apply Subtype.ext
  funext i j
  exact congrArg Fin.val (congrFun (congrFun h i) j)

 

def encodeNat (x : ℕ) : List Bool :=
  List.replicate x.bits.length true ++ false :: x.bits

def encodeList (xs : List ℕ) : List Bool := xs.flatMap encodeNat

def inputBits {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) : List Bool :=
  encodeList ([m, n, k] ++ List.ofFn r ++ List.ofFn c)

def outputBits {m n : ℕ} {r : Fin m → ℕ} {c : Fin n → ℕ}
    (X : Tables r c) : List Bool :=
  encodeList ((List.ofFn fun i => List.ofFn (X.val i)).flatten)

namespace BitModel

inductive Move | left | stay | right
  deriving DecidableEq

 

structure Tape where
  left : List (Option Bool)
  head : Option Bool
  right : List (Option Bool)
  deriving DecidableEq

def Tape.blank : Tape := ⟨[], none, []⟩

def Tape.ofInput (xs : List Bool) : Tape :=
  match xs with
  | [] => .blank
  | x :: xs => ⟨[], some x, xs.map some⟩

def Tape.move (d : Move) (a : Option Bool) (t : Tape) : Tape :=
  match d with
  | .stay => ⟨t.left, a, t.right⟩
  | .left => match t.left with
    | [] => ⟨[], none, a :: t.right⟩
    | x :: xs => ⟨xs, x, a :: t.right⟩
  | .right => match t.right with
    | [] => ⟨a :: t.left, none, []⟩
    | x :: xs => ⟨a :: t.left, x, xs⟩

 

structure Instruction (states tapes : ℕ) where
  next : Option (Fin states)
  write : Fin tapes → Option Bool
  move : Fin tapes → Move
  emit : Option Bool

 

structure Machine where
  states : ℕ
  tapes : ℕ
  start : Fin states
  inputTape : Fin tapes
  transition : Fin states → Bool → (Fin tapes → Option Bool) → Instruction states tapes

structure Config (M : Machine) where
  state : Option (Fin M.states)
  tape : Fin M.tapes → Tape
  outputRev : List Bool

def Machine.initial (M : Machine) (xs : List Bool) : Config M :=
  ⟨some M.start, fun i => if i = M.inputTape then .ofInput xs else .blank, []⟩

def Machine.step (M : Machine) (coin : Bool) (c : Config M) : Config M :=
  match c.state with
  | none => c
  | some s =>
    let a := M.transition s coin (fun i => (c.tape i).head)
    ⟨a.next, fun i => (c.tape i).move (a.move i) (a.write i),
      match a.emit with | none => c.outputRev | some b => b :: c.outputRev⟩

def Machine.run (M : Machine) (xs : List Bool) {t : ℕ} (coins : Fin t → Bool) : Config M :=
  (List.ofFn coins).foldl (fun c b => M.step b c) (M.initial xs)

 

noncomputable def Machine.mass (M : Machine) (xs out : List Bool) (t : ℕ) : ℝ :=
  ((Finset.univ.filter fun coins : Fin t → Bool =>
    (M.run xs coins).state = none ∧ (M.run xs coins).outputRev.reverse = out).card : ℝ) /
    2 ^ t

 
noncomputable def Machine.tail (M : Machine) (xs : List Bool) (t : ℕ) : ℝ :=
  ((Finset.univ.filter fun coins : Fin t → Bool =>
    (M.run xs coins).state ≠ none).card : ℝ) / 2 ^ t

end BitModel

 

def inputSize (m n N : ℕ) : ℕ := m + n + Nat.log2 (N + 1) + 1

noncomputable def variationBy {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (M : BitModel.Machine) (k t : ℕ) : ℝ := by
  letI := Fintype.ofFinite (Tables r c)
  exact (∑ X : Tables r c,
    |M.mass (inputBits r c k) (outputBits X) t - 1 / Fintype.card (Tables r c)|) / 2

 

def BoundedMain : Prop :=
  ∃ (M : BitModel.Machine) (A q : ℕ),
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i) = (∑ j, c j) → ∀ k : ℕ, 1 ≤ k →
      ∃ t : ℕ, t ≤ A * (inputSize m n (∑ i, r i) + k) ^ q ∧
        (∀ coins : Fin t → Bool,
          (M.run (inputBits r c k) coins).state = none ∧
          ∃ X : Tables r c,
            (M.run (inputBits r c k) coins).outputRev.reverse = outputBits X) ∧
        variationBy r c M k t ≤ (2 : ℝ) ^ (-(k : ℤ))

 

def ExactMain : Prop :=
  ∃ (M : BitModel.Machine) (A q : ℕ),
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i) = (∑ j, c j) →
      (∀ (t : ℕ) (coins : Fin t → Bool),
        (M.run (inputBits r c 0) coins).state = none → ∃ X : Tables r c,
          (M.run (inputBits r c 0) coins).outputRev.reverse = outputBits X) ∧
      Tendsto (M.tail (inputBits r c 0)) atTop (nhds 0) ∧
      (∀ X : Tables r c, Tendsto (M.mass (inputBits r c 0) (outputBits X))
        atTop (nhds (1 / (Nat.card (Tables r c) : ℝ)))) ∧
      Summable (M.tail (inputBits r c 0)) ∧
      (∑' t, M.tail (inputBits r c 0) t) ≤
        (A * (inputSize m n (∑ i, r i)) ^ q : ℕ)

 

def MainTheorem : Prop := BoundedMain ∧ ExactMain

end Contingency

 

 

open scoped BigOperators

namespace Contingency

 

theorem tables_nonempty {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i) = ∑ j, c j) : Nonempty (Tables r c) := by
  classical
  let e : (Σ i, Fin (r i)) ≃ (Σ j, Fin (c j)) :=
    Fintype.equivOfCardEq (by simpa [Fintype.card_sigma] using hrc)
  let X (i : Fin m) (j : Fin n) : ℕ := ∑ z : (Σ i, Fin (r i)),
    (if z.1=i then 1 else 0)*(if (e z).1=j then 1 else 0)
  refine ⟨⟨X,?_,?_⟩⟩
  · intro i
    change (∑ j, ∑ z : (Σ i, Fin (r i)),
      (if z.1=i then 1 else 0)*(if (e z).1=j then 1 else 0)) = r i
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    have hz (z : Σ i, Fin (r i)) : (∑ j, if (e z).1=j then (1:ℕ) else 0)=1 := by simp
    simp only [hz,mul_one]
    rw [Fintype.sum_sigma]
    change (∑ a, ∑ _t : Fin (r a), if a=i then (1:ℕ) else 0)=r i
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_ite,mul_one,mul_zero]
    simp
  · intro j
    change (∑ i, ∑ z : (Σ i, Fin (r i)),
      (if z.1=i then 1 else 0)*(if (e z).1=j then 1 else 0)) = c j
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    have hz (z : Σ i, Fin (r i)) : (∑ i, if z.1=i then (1:ℕ) else 0)=1 := by simp
    simp only [hz,one_mul]
    calc
      _ = ∑ z : (Σ j, Fin (c j)), if z.1=j then (1:ℕ) else 0 :=
        e.sum_comp (fun z : (Σ j, Fin (c j)) => if z.1=j then (1:ℕ) else 0)
      _ = _ := by
        rw [Fintype.sum_sigma]
        change (∑ a, ∑ _t : Fin (c a), if a=j then (1:ℕ) else 0)=c j
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_ite,mul_one,mul_zero]
        simp

end Contingency

 

 

open scoped BigOperators
namespace Contingency
noncomputable section

lemma sum_dite_subtype {α M : Type*} [Fintype α] [AddCommMonoid M]
    (p : α → Prop) [DecidablePred p] (f : {x // p x} → M) :
    (∑ x, if h : p x then f ⟨x,h⟩ else 0)=∑ x,f x := by
  symm
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
  · intro i hi
    split_ifs with h
    · exact (hi ⟨⟨i,h⟩,rfl⟩).elim
    · rfl
  · intro i; simp [i.property]

variable {m n a b : ℕ} {r : Fin m → ℕ} {c : Fin n → ℕ}

theorem table_cell_le_row (X : Tables r c) (i : Fin m) (j : Fin n) : X.val i j≤r i := by
  rw [← X.property.1 i]
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (X.val i j)) (Finset.mem_univ j)

theorem table_cell_le_col (X : Tables r c) (i : Fin m) (j : Fin n) : X.val i j≤c j := by
  rw [← X.property.2 j]
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (X.val i j)) (Finset.mem_univ i)

variable (p : Fin m → Prop) (q : Fin n → Prop) [DecidablePred p] [DecidablePred q]
    (er : Fin a ≃ {i // p i}) (ec : Fin b ≃ {j // q j})
    (hr : ∀ i,¬p i → r i=0) (hc : ∀ j,¬q j → c j=0)

def restrictTable (X : Tables r c) :
    Tables (fun i => r (er i).val) (fun j => c (ec j).val) := by
  refine ⟨fun i j => X.val (er i).val (ec j).val,?_,?_⟩
  · intro i
    rw [ec.sum_comp (fun j => X.val (er i).val j.val)]
    calc
      _ = ∑ j,X.val (er i).val j := by
        apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
        · intro j hj
          have hn : ¬q j := fun h => hj ⟨⟨j,h⟩,rfl⟩
          have h := table_cell_le_col X (er i).val j
          rw [hc j hn] at h
          omega
        · intro j; rfl
      _ = _ := X.property.1 _
  · intro j
    rw [er.sum_comp (fun i => X.val i.val (ec j).val)]
    calc
      _ = ∑ i,X.val i (ec j).val := by
        apply Fintype.sum_of_injective Subtype.val Subtype.val_injective
        · intro i hi
          have hn : ¬p i := fun h => hi ⟨⟨i,h⟩,rfl⟩
          have h := table_cell_le_row X i (ec j).val
          rw [hr i hn] at h
          omega
        · intro i; rfl
      _ = _ := X.property.2 _

def expandTable (X : Tables (fun i => r (er i).val) (fun j => c (ec j).val)) : Tables r c := by
  refine ⟨fun i j => if hi : p i then if hj : q j then X.val (er.symm ⟨i,hi⟩) (ec.symm ⟨j,hj⟩) else 0 else 0,?_,?_⟩
  · intro i
    by_cases hi : p i
    · simp only [dite_eq_left hi]
      rw [sum_dite_subtype q (fun j => X.val (er.symm ⟨i,hi⟩) (ec.symm j))]
      rw [← ec.sum_comp (fun j => X.val (er.symm ⟨i,hi⟩) (ec.symm j))]
      simp only [Equiv.symm_apply_apply]
      simp only [X.property.1,Equiv.apply_symm_apply]
    · simp [hi,hr i hi]
  · intro j
    by_cases hj : q j
    · simp only [dite_eq_left hj]
      rw [sum_dite_subtype p (fun i => X.val (er.symm i) (ec.symm ⟨j,hj⟩))]
      rw [← er.sum_comp (fun i => X.val (er.symm i) (ec.symm ⟨j,hj⟩))]
      simp only [Equiv.symm_apply_apply]
      simp only [X.property.2,Equiv.apply_symm_apply]
    · simp [hj,hc j hj]

 

def restrictTableEquiv : Tables r c ≃ Tables (fun i => r (er i).val) (fun j => c (ec j).val) where
  toFun := restrictTable p q er ec hr hc
  invFun := expandTable p q er ec hr hc
  left_inv X := by
    apply Subtype.ext; funext i j
    by_cases hi : p i
    · by_cases hj : q j
      · simp [expandTable,restrictTable,hi,hj]
      · have hz : X.val i j=0 := by have h := table_cell_le_col X i j; rw [hc j hj] at h; omega
        simp [expandTable,hi,hj,hz]
    · have hz : X.val i j=0 := by have h := table_cell_le_row X i j; rw [hr i hi] at h; omega
      simp [expandTable,hi,hz]
  right_inv X := by
    apply Subtype.ext; funext i j
    simp [restrictTable,expandTable,(er i).property,(ec j).property]

end
end Contingency

 

 

open scoped BigOperators
namespace Contingency
noncomputable section

def maximizers {a : ℕ} (R : Fin (a+1) → ℕ) : Finset (Fin (a+1)) :=
  Finset.univ.filter (fun i => ∀ j,R j≤R i)

theorem maximizers_nonempty {a : ℕ} (R : Fin (a+1) → ℕ) : (maximizers R).Nonempty := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ R Finset.univ_nonempty
  exact ⟨i,by simpa [maximizers] using hi⟩

 
def maximumIndex {a : ℕ} (R : Fin (a+1) → ℕ) : Fin (a+1) := (maximizers R).min' (maximizers_nonempty R)

theorem maximumIndex_max {a : ℕ} (R : Fin (a+1) → ℕ) (i : Fin (a+1)) : R i≤R (maximumIndex R) := by
  have hh := Finset.min'_mem (maximizers R) (maximizers_nonempty R)
  exact (Finset.mem_filter.mp hh).2 i

theorem maximumIndex_first {a : ℕ} (R : Fin (a+1) → ℕ) (i : Fin (a+1))
    (hi : ∀ j,R j≤R i) : maximumIndex R ≤ i := Finset.min'_le _ i (by simp [maximizers,hi])

def marginOrder {a : ℕ} (R : Fin (a+1) → ℕ) : Fin (a+1) ≃ Fin (a+1) :=
  Equiv.swap (maximumIndex R) (Fin.last a)

theorem marginOrder_max {a : ℕ} (R : Fin (a+1) → ℕ) (i : Fin (a+1)) :
    R (marginOrder R i)≤R (marginOrder R (Fin.last a)) := by
  rw [marginOrder,Equiv.swap_apply_right]
  exact maximumIndex_max _ _

variable {m n a b : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (er : Fin a ≃ Fin m) (ec : Fin b ≃ Fin n)

def permuteTable (X : Tables r c) : Tables (fun i => r (er i)) (fun j => c (ec j)) :=
  ⟨fun i j => X.val (er i) (ec j),fun row => (ec.sum_comp _).trans (X.property.1 (er row)),
    fun column => (er.sum_comp _).trans (X.property.2 (ec column))⟩

def permuteTableEquiv : Tables r c ≃ Tables (fun i => r (er i)) (fun j => c (ec j)) where
  toFun := permuteTable r c er ec
  invFun X := ⟨fun i j => X.val (er.symm i) (ec.symm j),by
    constructor
    · intro i
      rw [ec.symm.sum_comp (fun j => X.val (er.symm i) j),X.property.1]
      simp
    · intro j
      rw [er.symm.sum_comp (fun i => X.val i (ec.symm j)),X.property.2]
      simp⟩
  left_inv X := by apply Subtype.ext; funext i j; simp [permuteTable]
  right_inv X := by apply Subtype.ext; funext i j; simp [permuteTable]

namespace Law
variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]

theorem uniform_map_equiv (e : α ≃ β) : (uniform α).map e=uniform β := by
  classical
  apply Law.ext; funext y
  have he (x : α) : e x=y ↔ x=e.symm y := e.eq_symm_apply.symm
  simp only [map,bind,pure,mul_ite,mul_one,mul_zero,he]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,uniform,Fintype.card_congr e]

end Law
end
end Contingency

 

 

open scoped BigOperators
namespace Contingency.Dense
noncomputable section
variable {a c : ℕ}

 

def complete (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (x : Fin a → Fin c → ℝ) :
    Fin (a+1) → Fin (c+1) → ℝ :=
  Fin.lastCases
    (Fin.lastCases (R (Fin.last a)-(∑ j : Fin c,P j.castSucc)+(∑ i,∑ j,x i j))
      (fun j => P j.castSucc-∑ i,x i j))
    (fun i => Fin.lastCases (R i.castSucc-∑ j,x i j) (fun j => x i j))

@[simp] theorem complete_free (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (x : Fin a → Fin c → ℝ) (i : Fin a) (j : Fin c) :
    complete R P x i.castSucc j.castSucc=x i j := by simp [complete]

@[simp] theorem complete_right (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (x : Fin a → Fin c → ℝ) (i : Fin a) :
    complete R P x i.castSucc (Fin.last c)=R i.castSucc-∑ j,x i j := by simp [complete]

@[simp] theorem complete_bottom (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (x : Fin a → Fin c → ℝ) (j : Fin c) :
    complete R P x (Fin.last a) j.castSucc=P j.castSucc-∑ i,x i j := by simp [complete]

@[simp] theorem complete_corner (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (x : Fin a → Fin c → ℝ) :
    complete R P x (Fin.last a) (Fin.last c)=
      R (Fin.last a)-(∑ j : Fin c,P j.castSucc)+(∑ i,∑ j,x i j) := by simp [complete]

@[simp] theorem complete_row (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (x : Fin a → Fin c → ℝ) (i : Fin (a+1)) : ∑ j,complete R P x i j=R i := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.sum_univ_castSucc]
    simp only [complete_bottom,complete_corner,Finset.sum_sub_distrib]
    rw [Finset.sum_comm (f:=fun i j => x i j)]
    ring
  · rw [Fin.sum_univ_castSucc]
    simp only [complete_free,complete_right]
    ring

@[simp] theorem complete_col (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (x : Fin a → Fin c → ℝ) (h : (∑ i,R i)=∑ j,P j) (j : Fin (c+1)) :
    ∑ i,complete R P x i j=P j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Fin.sum_univ_castSucc]
    simp only [complete_right,complete_corner,Finset.sum_sub_distrib]
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc] at h
    linarith
  · rw [Fin.sum_univ_castSucc]
    simp only [complete_free,complete_bottom]
    ring

 
theorem complete_represents (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (X : Fin (a+1) → Fin (c+1) → ℝ)
    (hR : ∀ i,∑ j,X i j=R i) (hP : ∀ j,∑ i,X i j=P j) :
    complete R P (fun i j => X i.castSucc j.castSucc)=X := by
  funext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · have hr := hR (Fin.last a)
      rw [Fin.sum_univ_castSucc] at hr
      have hp (j : Fin c) := hP j.castSucc
      simp only [Fin.sum_univ_castSucc] at hp
      have he : (∑ j : Fin c,X (Fin.last a) j.castSucc)=
          (∑ j : Fin c,P j.castSucc)-(∑ i : Fin a,∑ j : Fin c,X i.castSucc j.castSucc) := by
        rw [Finset.sum_comm (f:=fun (i : Fin a) (j : Fin c) => X i.castSucc j.castSucc),← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro j _; linarith [hp j]
      rw [he] at hr
      rw [complete_corner]
      linarith
    · rw [complete_bottom]
      have hp := hP j.castSucc
      rw [Fin.sum_univ_castSucc] at hp
      linarith
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [complete_right]
      have hr := hR i.castSucc
      rw [Fin.sum_univ_castSucc] at hr
      linarith
    · exact complete_free R P _ i j

def scale (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (i : Fin (a+1)) (j : Fin (c+1)) : ℝ :=
  min (R i) (P j)

def scaled (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (u : Fin a×Fin c → ℝ) :=
  complete R P (fun i j => w i j*u (i,j))

def normalized (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (u : Fin a×Fin c → ℝ) (i : Fin (a+1)) (j : Fin (c+1)) : ℝ :=
  scaled R P w u i j/scale R P i j

def polytope (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) : Set (Fin a×Fin c → ℝ) :=
  {u | ∀ i j, 0 ≤ normalized R P w u i j}

 
theorem width_bounds (s B : ℕ) (hB : 0<B) (h : 2*B ≤ s) :
    (s:ℝ)/(2*B) ≤ ((s/B:ℕ):ℝ) ∧ ((s/B:ℕ):ℝ) ≤ (s:ℝ)/B := by
  have hq : 1 ≤ s/B := Nat.div_pos (by omega) hB
  have hu := Nat.div_mul_le_self s B
  have hl := Nat.lt_mul_div_succ s hB
  have hb : (0:ℝ)<B := by exact_mod_cast hB
  constructor
  · apply (div_le_iff₀ (by positivity : (0:ℝ)<2*B)).mpr
    have hi : s ≤ (s/B)*(2*B) := by nlinarith only [hq,hl]
    exact_mod_cast hi
  · apply (le_div_iff₀ hb).mpr
    exact_mod_cast hu

 
theorem entry_le_scale (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (X : Fin (a+1) → Fin (c+1) → ℝ) (hX : ∀ i j,0 ≤ X i j)
    (hR : ∀ i,∑ j,X i j=R i) (hP : ∀ j,∑ i,X i j=P j) (i j) : X i j ≤  scale R P i j := by
  apply le_min
  · simpa only [hR] using Finset.single_le_sum (fun j _ => hX i j) (Finset.mem_univ j)
  · simpa only [hP] using Finset.single_le_sum (fun i _ => hX i j) (Finset.mem_univ i)

 
theorem polytope_bounded (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (w : Fin a → Fin c → ℝ) (B : ℝ) (hB : 0<B)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j) (heq : (∑ i,R i)=∑ j,P j)
    (hw : ∀ i j,scale R P i.castSucc j.castSucc/(2*B) ≤ w i j)
    (u : Fin a×Fin c → ℝ) (hu : u∈polytope R P w) :
    ∀ s,0 ≤ u s ∧ u s ≤ 2*B := by
  have hs (i j) : 0<scale R P i j := lt_min (hR i) (hP j)
  have hpos (i j) : 0<w i j := (div_pos (hs i.castSucc j.castSucc) (by positivity)).trans_le (hw i j)
  have hX (i j) : 0 ≤  scaled R P w u i j := by
    have h := hu i j
    change 0 ≤ scaled R P w u i j/scale R P i j at h
    simpa only [zero_mul] using (le_div_iff₀ (hs i j)).mp h
  rintro ⟨i,j⟩
  have he : scaled R P w u i.castSucc j.castSucc=w i j*u (i,j) := complete_free R P _ i j
  have h0 := hX i.castSucc j.castSucc
  rw [he] at h0
  have hl := entry_le_scale R P (scaled R P w u) hX
    (fun i => complete_row R P _ i) (fun j => complete_col R P _ heq j) i.castSucc j.castSucc
  rw [he] at hl
  constructor
  · exact nonneg_of_mul_nonneg_right h0 (hpos i j)
  · have hw' : scale R P i.castSucc j.castSucc ≤ w i j*(2*B) :=
      (div_le_iff₀ (by positivity)).mp (hw i j)
    exact (mul_le_mul_iff_right₀ (hpos i j)).mp (hl.trans hw')

end
end Contingency.Dense

 

 

open scoped BigOperators
namespace Contingency.Dense
noncomputable section
variable {a c : ℕ}

 

theorem real_completion {I J : Type*} [Fintype I] [Fintype J]
    (R : I → ℝ) (P : J → ℝ) (hR : ∀ i,0 ≤ R i) (hP : ∀ j,0 ≤ P j)
    (heq : (∑ i,R i)=∑ j,P j) :
    ∃ X : I → J → ℝ, (∀ i j,0 ≤ X i j) ∧ (∀ i,∑ j,X i j=R i) ∧ (∀ j,∑ i,X i j=P j) := by
  classical
  by_cases h0 : (∑ i,R i)=0
  · have hR0 (i) : R i=0 := by
      have := Finset.single_le_sum (fun i _ => hR i) (Finset.mem_univ i)
      rw [h0] at this; linarith [hR i]
    have hP0 (j) : P j=0 := by
      have := Finset.single_le_sum (fun j _ => hP j) (Finset.mem_univ j)
      rw [← heq,h0] at this; linarith [hP j]
    refine ⟨fun _ _ => 0,fun _ _ => le_rfl,?_,?_⟩
    · intro i; simp [hR0]
    · intro j; simp [hP0]
  · have hS : 0<(∑ i,R i) := lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hR i)) (Ne.symm h0)
    refine ⟨fun i j => R i*P j/(∑ i,R i),?_,?_,?_⟩
    · intro i j; exact div_nonneg (mul_nonneg (hR i) (hP j)) hS.le
    · intro i
      rw [← Finset.sum_div,← Finset.mul_sum,← heq]
      field_simp
    · intro j
      rw [← Finset.sum_div,← Finset.sum_mul]
      field_simp

 

theorem interior_table (d : ℝ) (hd : 0<d)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j) (heq : (∑ i,R i)=∑ j,P j)
    (ha : (a+1:ℕ) ≤ d) (hc : (c+1:ℕ) ≤ d) :
    ∃ X : Fin (a+1) → Fin (c+1) → ℝ,
      (∀ i j,scale R P i j/(2*d) ≤ X i j) ∧
      (∀ i,∑ j,X i j=R i) ∧ (∀ j,∑ i,X i j=P j) := by
  let B := fun i j => scale R P i j/(2*d)
  have hBn (i j) : 0 ≤ B i j := div_nonneg (le_min (hR i).le (hP j).le) (by positivity)
  have hrow (i) : (∑ j,B i j) ≤ R i/2 := by
    calc
      _  ≤  ∑ j : Fin (c+1), R i/(2*d) := by
        apply Finset.sum_le_sum; intro j _
        exact div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
      _ = (c+1:ℕ)*(R i/(2*d)) := by simp
      _  ≤  d*(R i/(2*d)) := mul_le_mul_of_nonneg_right hc (div_nonneg (hR i).le (by positivity))
      _ = R i/2 := by field_simp
  have hcol (j) : (∑ i,B i j) ≤ P j/2 := by
    calc
      _  ≤  ∑ i : Fin (a+1), P j/(2*d) := by
        apply Finset.sum_le_sum; intro i _
        exact div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = (a+1:ℕ)*(P j/(2*d)) := by simp
      _  ≤  d*(P j/(2*d)) := mul_le_mul_of_nonneg_right ha (div_nonneg (hP j).le (by positivity))
      _ = P j/2 := by field_simp
  let R' := fun i => R i-∑ j,B i j
  let P' := fun j => P j-∑ i,B i j
  have hR' (i) : 0 ≤ R' i := by dsimp [R']; linarith [hrow i,hR i]
  have hP' (j) : 0 ≤ P' j := by dsimp [P']; linarith [hcol j,hP j]
  have heq' : (∑ i,R' i)=∑ j,P' j := by
    simp only [R',P',Finset.sum_sub_distrib,heq]
    rw [Finset.sum_comm]
  obtain ⟨Y,hY,hYR,hYP⟩ := real_completion R' P' hR' hP' heq'
  refine ⟨fun i j => B i j+Y i j,?_,?_,?_⟩
  · intro i j; exact le_add_of_nonneg_right (hY i j)
  · intro i; rw [Finset.sum_add_distrib,hYR]; dsimp [R']; ring
  · intro j; rw [Finset.sum_add_distrib,hYP]; dsimp [P']; ring

 
theorem interior_point (d : ℝ) (hd : 0<d)
    (R : Fin (a+1) → ℝ) (P : Fin (c+1) → ℝ) (w : Fin a → Fin c → ℝ)
    (hR : ∀ i,0<R i) (hP : ∀ j,0<P j) (heq : (∑ i,R i)=∑ j,P j)
    (ha : (a+1:ℕ) ≤ d) (hc : (c+1:ℕ) ≤ d) (hw : ∀ i j,0<w i j) :
    ∃ u : Fin a×Fin c → ℝ, ∀ i j, 1/(2*d) ≤ normalized R P w u i j := by
  obtain ⟨X,hX,hXR,hXP⟩ := interior_table d hd R P hR hP heq ha hc
  let u := fun s : Fin a×Fin c => X s.1.castSucc s.2.castSucc/w s.1 s.2
  have he : scaled R P w u=X := by
    unfold scaled
    have hx : (fun i j => w i j*u (i,j))=fun i j => X i.castSucc j.castSucc := by
      funext i j
      dsimp [u]
      field_simp [(hw i j).ne']
    rw [hx]
    exact complete_represents R P X hXR hXP
  refine ⟨u,fun i j => ?_⟩
  unfold normalized
  rw [he]
  have hs : 0<scale R P i j := lt_min (hR i) (hP j)
  apply (le_div_iff₀ hs).mpr
  calc
    _ = scale R P i j/(2*d) := by ring
    _ ≤ _ := hX i j

end
end Contingency.Dense

end

end OAI
