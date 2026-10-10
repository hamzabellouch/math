import Mathlib
import OAI.Probability.Contingency.DenseDyadic

namespace OAI

/-! Completions. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators

namespace Contingency.PaddedGraph
variable {m n : ℕ}

def rowPadding (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (i : Fin m) : ℤ :=
  ∑ j, if IsLarge U r c (i,j) then (L:ℤ) else 0

def colPadding (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (j : Fin n) : ℤ :=
  ∑ i, if IsLarge U r c (i,j) then (L:ℤ) else 0

 

def Completion (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (X : State m n) :=
  { A : Cell m n → ℤ // (∀ w, 0 ≤ A w) ∧
    (∀ w, IsSmall U r c w → A w = 0) ∧
    (∀ i, rowSum A i = r i - rowSum X.x i + rowPadding U L r c i) ∧
    (∀ j, colSum A j = c j - colSum X.q j + colPadding U L r c j) }

instance completionFinite (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (X : State m n) :
    Finite (Completion U L r c X) := by
  let f : Completion U L r c X → (w : Cell m n) →
      Fin ((r w.1 - rowSum X.x w.1 + rowPadding U L r c w.1).toNat + 1) :=
    fun A w => ⟨(A.val w).toNat, by
      have h := coordinate_le_rowSum A.val A.property.1 w
      rw [A.property.2.2.1 w.1] at h
      have hh := Int.toNat_le_toNat h
      omega⟩
  apply Finite.of_injective f
  intro A B he
  apply Subtype.ext
  funext w
  have h := congrArg (fun g => (g w).val) he
  dsimp [f] at h
  have hA := A.property.1 w
  have hB := B.property.1 w
  omega

def completionRepair (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hd : DefectAt U r c s t X)
    (A : Completion U L r c X) : Completion U L r c (repair U r c s t X) := by
  let B := fun w => A.val w + if IsLarge U r c (receiver s t) then unit (receiver s t) w else 0
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro w
    have h := A.property.1 w
    dsimp [B,unit]
    split_ifs <;> omega
  · intro w hw
    dsimp [B]
    rw [A.property.2.1 w hw]
    by_cases hv : IsLarge U r c (receiver s t)
    · have he : w ≠ receiver s t := by intro he; exact hw (he ▸ hv)
      simp [hv,unit,he]
    · simp [hv]
  · intro i
    rw [repair_rowSum U r c s t X i]
    by_cases hv : IsLarge U r c (receiver s t)
    · have hb : B = fun w => A.val w - 0 + unit (receiver s t) w := by
        funext w; simp [B,hv]
      rw [hb,rowSum_sub_add,rowSum_unit,A.property.2.2.1 i]
      simp only [hv,true_and]
      have hz : rowSum (fun _ : Cell m n => (0:ℤ)) i = 0 := by simp [rowSum]
      rw [hz]
      dsimp [receiver]
      omega
    · have hb : B = A.val := by funext w; simp [B,hv]
      rw [hb,A.property.2.2.1 i]
      simp [hv]
  · intro j
    rw [repair_colSum U r c s t X hd j]
    by_cases hv : IsLarge U r c (receiver s t)
    · have hb : B = fun w => A.val w - 0 + unit (receiver s t) w := by
        funext w; simp [B,hv]
      rw [hb,colSum_sub_add,colSum_unit,A.property.2.2.2 j]
      simp only [hv,true_and]
      have hz : colSum (fun _ : Cell m n => (0:ℤ)) j = 0 := by simp [colSum]
      rw [hz]
      dsimp [receiver]
      omega
    · have hb : B = A.val := by funext w; simp [B,hv]
      rw [hb,A.property.2.2.2 j]
      simp [hv]

theorem completionRepair_injective (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hd : DefectAt U r c s t X) :
    Function.Injective (completionRepair U L r c s t X hd) := by
  intro A B he
  apply Subtype.ext
  funext w
  have h := congrArg (fun A : Completion U L r c (repair U r c s t X) => A.val w) he
  dsimp [completionRepair] at h
  linarith

 
noncomputable def weight (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (X : State m n) : ℕ := by
  classical
  exact if Feasible U r c X then Nat.card (Completion U L r c X) else 0

theorem weight_repair_le (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (X : State m n) (hd : DefectAt U r c s t X) :
    weight U L r c X ≤ weight U L r c (repair U r c s t X) := by
  classical
  by_cases hx : Feasible U r c X
  · rw [weight,ite_eq_left hx,weight,ite_eq_left (repair_feasible U r c s t X hx hd)]
    exact Nat.card_le_card_of_injective _ (completionRepair_injective U L r c s t X hd)
  · simp [weight,hx]

 

theorem joint_repair_injective (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) :
    Function.Injective (fun Z : Σ X : {X : State m n // DefectAt U r c s t X},
      Completion U L r c X.val =>
      (⟨repair U r c s t Z.1.val,
        completionRepair U L r c s t Z.1.val Z.1.property Z.2⟩ :
         Σ Y : State m n, Completion U L r c Y)) := by
  rintro ⟨⟨X,hX⟩,A⟩ ⟨⟨Y,hY⟩,B⟩ he
  have hs := congrArg Sigma.fst he
  have hxy := repair_injective U r c s t X Y hX hY hs
  subst Y
  have ha : completionRepair U L r c s t X hX A = completionRepair U L r c s t X hY B := by
    exact (Sigma.mk.inj he).2.eq
  have hab := completionRepair_injective U L r c s t X hX ha
  subst B
  rfl

end Contingency.PaddedGraph

 

 

open scoped BigOperators

namespace Contingency.PaddedGraph
variable {m n : ℕ}

instance feasibleFinite (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Finite {X : State m n // Feasible U r c X} := by
  let f : {X : State m n // Feasible U r c X} → Cell m n → Fin (U+1) × Fin (U+1) :=
    fun X w => (⟨(X.val.x w).toNat, by have h := X.property.1 w; omega⟩,
      ⟨(X.val.q w).toNat, by have h := X.property.1 w; omega⟩)
  apply Finite.of_injective f
  intro X Y he
  apply Subtype.ext
  have hx : X.val.x=Y.val.x := by
    funext w
    have h := congrArg (fun g => (g w).1.val) he
    dsimp [f] at h
    have hX := (X.property.1 w).1
    have hY := (Y.property.1 w).1
    omega
  have hq : X.val.q=Y.val.q := by
    funext w
    have h := congrArg (fun g => (g w).2.val) he
    dsimp [f] at h
    have hX := (X.property.1 w).2.2.1
    have hY := (Y.property.1 w).2.2.1
    omega
  cases X with | mk X hX =>
    cases Y with | mk Y hY =>
      cases X; cases Y
      simp_all

def Prefix (s : Cell m n) (σ : Cell m n → ℤ) (X : State m n) : Prop :=
  ∀ w, Before w s → X.x w = σ w ∧ X.q w = σ w

def ChildStates (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) :=
  {X : {X : State m n // Feasible U r c X} //
    Transversal X.val ∧ Prefix s σ X.val ∧ X.val.x s = l}

def DefectStates (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) :=
  {X : {X : State m n // Feasible U r c X} //
    DefectAt U r c s t X.val ∧ Prefix s σ X.val ∧ X.val.x s = l-1}

instance (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) : Finite (ChildStates U r c s σ l) :=
  by unfold ChildStates; infer_instance
instance (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) : Finite (DefectStates U r c s t σ l) :=
  by unfold DefectStates; infer_instance

noncomputable def conditionalRepair (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) (hst : Before s t)
    (X : DefectStates U r c s t σ l) :
    ChildStates U r c s σ (if t.1=s.1 then l else l-1) := by
  refine ⟨⟨repair U r c s t X.val.val,
    repair_feasible U r c s t X.val.val X.val.property X.property.1⟩,
    repair_transversal U r c s t X.val.val,?_,
    repair_special U r c s t X.val.val X.property.1 l X.property.2.2⟩
  intro w hw
  have h := repair_prefix U r c s t X.val.val X.property.1 hst w hw
  have h' := X.property.2.1 w hw
  exact ⟨h.1.trans h'.1,h.2.trans h'.2⟩

def childFiber (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) :=
  Σ X : ChildStates U r c s σ l, Completion U L r c X.val.val

def defectFiber (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) :=
  Σ X : DefectStates U r c s t σ l, Completion U L r c X.val.val

instance (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) : Finite (childFiber U L r c s σ l) :=
  inferInstanceAs (Finite (Sigma _))
instance (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) : Finite (defectFiber U L r c s t σ l) :=
  inferInstanceAs (Finite (Sigma _))

noncomputable def conditionalCompletionRepair (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) (hst : Before s t)
    (Z : defectFiber U L r c s t σ l) : childFiber U L r c s σ (if t.1=s.1 then l else l-1) :=
  ⟨conditionalRepair U r c s t σ l hst Z.1,
    completionRepair U L r c s t Z.1.val.val Z.1.property.1 Z.2⟩

theorem conditionalCompletionRepair_injective (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) (hst : Before s t) :
    Function.Injective (conditionalCompletionRepair U L r c s t σ l hst) := by
  rintro ⟨⟨⟨X,hfX⟩,hX⟩,A⟩ ⟨⟨⟨Y,hfY⟩,hY⟩,B⟩ he
  have hxy : repair U r c s t X = repair U r c s t Y :=
    congrArg (fun Z => Z.1.val.val) he
  have hxy' := repair_injective U r c s t X Y hX.1 hY.1 hxy
  subst Y
  have ha : completionRepair U L r c s t X hX.1 A = completionRepair U L r c s t X hY.1 B :=
    (Sigma.mk.inj he).2.eq
  have hab := completionRepair_injective U L r c s t X hX.1 ha
  subst B
  rfl

noncomputable def childMass (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) : ℕ :=
  Nat.card (childFiber U L r c s σ l)

noncomputable def defectMass (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) : ℕ :=
  Nat.card (defectFiber U L r c s t σ l)

 

theorem conditional_repair_bound (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) (hst : Before s t) :
    defectMass U L r c s t σ l ≤
      if t.1=s.1 then childMass U L r c s σ l else childMass U L r c s σ (l-1) := by
  have h := Nat.card_le_card_of_injective _
    (conditionalCompletionRepair_injective U L r c s t σ l hst)
  change defectMass U L r c s t σ l ≤ childMass U L r c s σ (if t.1=s.1 then l else l-1) at h
  split_ifs at * <;> exact h

theorem conditional_repair_max (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (s t : Cell m n) (σ : Cell m n → ℤ) (l : ℤ) (hst : Before s t) :
    defectMass U L r c s t σ l ≤ max (childMass U L r c s σ (l-1)) (childMass U L r c s σ l) := by
  have h := conditional_repair_bound U L r c s t σ l hst
  split_ifs at h
  · exact h.trans (le_max_right _ _)
  · exact h.trans (le_max_left _ _)

end Contingency.PaddedGraph

 

 

open scoped BigOperators

namespace Contingency

 

theorem softPenalty_zero_iff {m n : ℕ}
    (r rb : Fin m → ℤ) (c cb : Fin n → ℤ) (B : Cell m n → ℤ)
    (small : Finset (Cell m n)) (p : Coordinate m n → ℤ) :
    softPenalty r rb c cb B small p = 0 ↔
      (∀ i : Fin m, (∑ j : Fin n, p (true,(i,j))) = rb i) ∧
      (∀ j : Fin n, (∑ i : Fin m, (B (i,j) - p (false,(i,j)))) = cb j) ∧
      (∀ i : Fin m, (∑ j : Fin n, if (i,j) ∈ small then p (true,(i,j)) else 0) ≤ r i) ∧
      (∀ j : Fin n, (∑ i : Fin m, if (i,j) ∈ small then B (i,j)-p (false,(i,j)) else 0) ≤ c j) := by
  classical
  rw [softPenalty_expansion]
  simp only [Nat.add_eq_zero_iff,Finset.sum_eq_zero_iff,Finset.mem_univ,true_implies,
    Int.natAbs_eq_zero,sub_eq_zero,Int.toNat_eq_zero,sub_nonpos]
  tauto

namespace PaddedGraph
variable {m n : ℕ}

def smallSet (U : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) : Finset (Cell m n) :=
  Finset.univ.filter (IsSmall U r c)

def capacity (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (w : Cell m n) : ℤ :=
  if IsLarge U r c w then C else U

def paddedRow (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (i : Fin m) : ℤ :=
  r i + rowPadding U L r c i

def paddedCol (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) (j : Fin n) : ℤ :=
  c j + colPadding U L r c j

 

def fullCoordinates (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (A : Cell m n → ℤ) : Coordinate m n → ℤ :=
  fun w => if w.1 then X.x w.2 + A w.2 else capacity U C r c w.2 - (X.q w.2 + A w.2)

theorem fullCoordinates_x (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (A : Cell m n → ℤ) (w : Cell m n) :
    fullCoordinates U C r c X A (true,w) = X.x w + A w := rfl

theorem fullCoordinates_q (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (A : Cell m n → ℤ) (w : Cell m n) :
    capacity U C r c w - fullCoordinates U C r c X A (false,w) = X.q w + A w := by
  simp [fullCoordinates]

theorem completion_cell_le (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (hf : Feasible U r c X) (A : Completion U L r c X)
    (w : Cell m n) : A.val w ≤ paddedRow U L r c w.1 := by
  have h := coordinate_le_rowSum A.val A.property.1 w
  rw [A.property.2.2.1 w.1] at h
  have hrow : 0 ≤ rowSum X.x w.1 := by
    apply Finset.sum_nonneg; intro j hj; exact (hf.1 (w.1,j)).1
  dsimp [paddedRow]
  omega

theorem fullCoordinates_inBox (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (hf : Feasible U r c X) (A : Completion U L r c X)
    (hC : ∀ i, paddedRow U L r c i ≤ C) :
    InBox (fun w => capacity U C r c w.2) (fullCoordinates U C r c X A.val) := by
  rintro ⟨b,w⟩
  have hX := hf.1 w
  by_cases hw : IsLarge U r c w
  · have hx0 := hf.2.1 w hw
    have hA := A.property.1 w
    have hAc := (completion_cell_le U L r c X hf A w).trans (hC w.1)
    cases b <;> simp [fullCoordinates,capacity,hw,hx0] <;> omega
  · have hA := A.property.2.1 w hw
    cases b <;> simp [fullCoordinates,capacity,hw,hA] <;> omega

theorem fullCoordinates_penalty_zero (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (hf : Feasible U r c X) (A : Completion U L r c X) :
    softPenalty (fun i => r i) (paddedRow U L r c) (fun j => c j) (paddedCol U L r c)
      (capacity U C r c) (smallSet U r c) (fullCoordinates U C r c X A.val) = 0 := by
  rw [softPenalty_zero_iff]
  have hsx (w : Cell m n) :
      (if w ∈ smallSet U r c then fullCoordinates U C r c X A.val (true,w) else 0) = X.x w := by
    by_cases hw : IsSmall U r c w
    · simp [smallSet,hw,fullCoordinates,A.property.2.1 w hw]
    · have hx := hf.2.1 w (Classical.not_not.mp hw)
      simp [smallSet,hw,hx]
  have hsq (w : Cell m n) :
      (if w ∈ smallSet U r c then capacity U C r c w -
          fullCoordinates U C r c X A.val (false,w) else 0) = X.q w := by
    rw [fullCoordinates_q]
    by_cases hw : IsSmall U r c w
    · simp [smallSet,hw,A.property.2.1 w hw]
    · have hx := hf.2.1 w (Classical.not_not.mp hw)
      simp [smallSet,hw,hx]
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    simp only [fullCoordinates_x,Finset.sum_add_distrib]
    change rowSum X.x i + rowSum A.val i = _
    rw [A.property.2.2.1 i]
    dsimp [paddedRow]
    ring
  · intro j
    simp only [fullCoordinates_q,Finset.sum_add_distrib]
    change colSum X.q j + colSum A.val j = _
    rw [A.property.2.2.2 j]
    dsimp [paddedCol]
    ring
  · intro i; simp only [hsx]; exact (hf.2.2.1 i).1
  · intro j; simp only [hsq]; exact (hf.2.2.2 j).1

theorem sum_rowSum (x : Cell m n → ℤ) : (∑ i, rowSum x i) = ∑ w, x w := by
  simp [rowSum,Fintype.sum_prod_type]

theorem sum_colSum (x : Cell m n → ℤ) : (∑ j, colSum x j) = ∑ w, x w := by
  rw [← sum_rowSum]
  exact Finset.sum_comm

theorem padding_totals (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    (∑ i, rowPadding U L r c i) = ∑ j, colPadding U L r c j := by
  exact Finset.sum_comm

theorem completion_small_totals (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i) = ∑ j, c j) (X : State m n) (A : Completion U L r c X) :
    (∑ w, X.x w) = ∑ w, X.q w := by
  have hrow := congrArg (fun f : Fin m → ℤ => ∑ i, f i) (funext A.property.2.2.1)
  have hcol := congrArg (fun f : Fin n → ℤ => ∑ j, f j) (funext A.property.2.2.2)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,sum_rowSum,sum_colSum] at hrow hcol
  have he : (∑ i, (r i:ℤ)) = ∑ j, (c j:ℤ) := by exact_mod_cast hrc
  have hpad := padding_totals U L r c
  omega

theorem fullCoordinates_total (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i) = ∑ j, c j) (X : State m n) (A : Completion U L r c X) :
    (∑ w, fullCoordinates U C r c X A.val w) = ∑ w, capacity U C r c w := by
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,fullCoordinates,ite_true,Bool.false_eq_true,ite_false]
  simp only [← Finset.sum_add_distrib]
  have he := completion_small_totals U L r c hrc X A
  simp only [Fintype.sum_prod_type] at he
  have hs : (∑ i, ∑ j, (X.x (i,j)+A.val (i,j) +
      (capacity U C r c (i,j)-(X.q (i,j)+A.val (i,j))))) =
      (∑ i, ∑ j, capacity U C r c (i,j)) +
      (∑ i, ∑ j, X.x (i,j)) - (∑ i, ∑ j, X.q (i,j)) := by
    simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i hi
    apply Finset.sum_congr rfl; intro j hj
    ring
  rw [hs,he]
  ring

 

theorem completion_softWeight_one (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i) = ∑ j, c j) (X : State m n) (hf : Feasible U r c X)
    (A : Completion U L r c X) (hC : ∀ i, paddedRow U L r c i ≤ C) :
    softWeight 0 (fun i => r i) (paddedRow U L r c) (fun j => c j) (paddedCol U L r c)
      (capacity U C r c) (smallSet U r c) (fullCoordinates U C r c X A.val) = 1 := by
  rw [softWeight_zero,ite_eq_left]
  exact ⟨fullCoordinates_inBox U L C r c X hf A hC,
    fullCoordinates_total U L C r c hrc X A,
    fullCoordinates_penalty_zero U L C r c X hf A⟩

 
def LargeChoices (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :=
  {A : Cell m n → ℤ // ∀ w, 0 ≤ A w ∧ A w ≤ C ∧ (IsSmall U r c w → A w=0)}

instance (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) : Finite (LargeChoices U C r c) := by
  let f : LargeChoices U C r c → Cell m n → Fin (C+1) :=
    fun A w => ⟨(A.val w).toNat,by have h := A.property w; omega⟩
  apply Finite.of_injective f
  intro A B h
  apply Subtype.ext; funext w
  have he := congrArg (fun z => (z w).val) h
  have hA := (A.property w).1
  have hB := (B.property w).1
  dsimp [f] at he
  omega

noncomputable instance (U C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Fintype (LargeChoices U C r c) := Fintype.ofFinite _

def CompletionEquations (U L : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (A : Cell m n → ℤ) : Prop :=
  (∀ i, rowSum A i = r i-rowSum X.x i+rowPadding U L r c i) ∧
  (∀ j, colSum A j = c j-colSum X.q j+colPadding U L r c j)

def choiceCompletion (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (A : LargeChoices U C r c)
    (he : CompletionEquations U L r c X A.val) : Completion U L r c X :=
  ⟨A.val,fun w => (A.property w).1,fun w => (A.property w).2.2,he⟩

def completionChoice (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (hf : Feasible U r c X)
    (hC : ∀ i, paddedRow U L r c i ≤ C) (A : Completion U L r c X) :
    LargeChoices U C r c :=
  ⟨A.val,fun w => ⟨A.property.1 w,(completion_cell_le U L r c X hf A w).trans (hC w.1),
    A.property.2.1 w⟩⟩

def completionChoiceEquiv (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (X : State m n) (hf : Feasible U r c X) (hC : ∀ i, paddedRow U L r c i ≤ C) :
    Completion U L r c X ≃ {A : LargeChoices U C r c // CompletionEquations U L r c X A.val} where
  toFun A := ⟨completionChoice U L C r c X hf hC A,A.property.2.2⟩
  invFun A := choiceCompletion U L C r c X A.val A.property
  left_inv _ := rfl
  right_inv _ := rfl

theorem choice_softWeight (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i) = ∑ j, c j) (X : State m n) (hf : Feasible U r c X)
    (A : LargeChoices U C r c) (hC : ∀ i, paddedRow U L r c i ≤ C) :
    softWeight 0 (fun i => r i) (paddedRow U L r c) (fun j => c j) (paddedCol U L r c)
      (capacity U C r c) (smallSet U r c) (fullCoordinates U C r c X A.val) =
    (by classical exact if CompletionEquations U L r c X A.val then (1:ℝ) else 0) := by
  classical
  by_cases he : CompletionEquations U L r c X A.val
  · exact (completion_softWeight_one U L C r c hrc X hf
      (choiceCompletion U L C r c X A he) hC).trans (ite_eq_left he).symm
  · rw [ite_eq_right he,softWeight_zero,ite_eq_right]
    rintro ⟨_,_,hp⟩
    apply he
    rw [softPenalty_zero_iff] at hp
    constructor
    · intro i
      have h := hp.1 i
      simp only [fullCoordinates_x,Finset.sum_add_distrib] at h
      change rowSum X.x i + rowSum A.val i = r i + rowPadding U L r c i at h
      omega
    · intro j
      have h := hp.2.1 j
      simp only [fullCoordinates_q,Finset.sum_add_distrib] at h
      change colSum X.q j + colSum A.val j = c j + colPadding U L r c j at h
      omega

 

theorem sum_choice_softWeight (U L C : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ)
    (hrc : (∑ i, r i) = ∑ j, c j) (X : State m n) (hf : Feasible U r c X)
    (hC : ∀ i, paddedRow U L r c i ≤ C) :
    (∑ A : LargeChoices U C r c,
      softWeight 0 (fun i => r i) (paddedRow U L r c) (fun j => c j) (paddedCol U L r c)
        (capacity U C r c) (smallSet U r c) (fullCoordinates U C r c X A.val)) =
      (Nat.card (Completion U L r c X) : ℝ) := by
  classical
  simp_rw [choice_softWeight U L C r c hrc X hf _ hC]
  rw [Nat.card_congr (completionChoiceEquiv U L C r c X hf hC)]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  simp

end PaddedGraph
end Contingency

end

end OAI
