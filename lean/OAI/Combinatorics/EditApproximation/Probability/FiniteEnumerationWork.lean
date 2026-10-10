import OAI.Combinatorics.EditApproximation.Numerics.VectorOptimizerWork
import OAI.Combinatorics.EditApproximation.Geometry.WideActions
import OAI.Combinatorics.EditApproximation.Geometry.BandDimension
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal finite enumeration with counters. Each callback is evaluated
once and its returned work is charged; list cells and copied output cells
are charged separately. -/

namespace EditApproximation



theorem arithmeticMapWithWork_value {α β : Type*} (f : α → β × ℕ) (values : List α) :
    (arithmeticMapWithWork f values).1 = values.map (fun a => (f a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih => simp only [arithmeticMapWithWork, ih, List.map_cons]

theorem arithmeticMapWithWork_cost {α β : Type*} (f : α → β × ℕ) (values : List α)
    (C : ℕ) (hC : ∀ a ∈ values, (f a).2 ≤ C) :
    (arithmeticMapWithWork f values).2 ≤ values.length * (C + 3) := by
  induction values with
  | nil => simp only [arithmeticMapWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons a rest ih =>
    have ha := hC a List.mem_cons_self
    have htail := ih (fun b hb => hC b (List.mem_cons_of_mem a hb))
    simp only [arithmeticMapWithWork, List.length_cons]
    nlinarith only [ha, htail]



theorem arithmeticFlatMapWithWork_value {α β : Type*} (f : α → List β × ℕ) (values : List α) :
    (arithmeticFlatMapWithWork f values).1 = values.flatMap (fun a => (f a).1) := by
  induction values with
  | nil => rfl
  | cons a rest ih => simp only [arithmeticFlatMapWithWork, ih, List.flatMap_cons]

theorem arithmeticFlatMapWithWork_cost {α β : Type*} (f : α → List β × ℕ) (values : List α)
    (C L : ℕ) (hC : ∀ a ∈ values, (f a).2 ≤ C) (hL : ∀ a ∈ values, (f a).1.length ≤ L) :
    (arithmeticFlatMapWithWork f values).2 ≤ values.length * (C + L + 3) := by
  induction values with
  | nil => simp only [arithmeticFlatMapWithWork, List.length_nil, Nat.zero_mul, le_refl]
  | cons a rest ih =>
    have ha := hC a List.mem_cons_self
    have hla := hL a List.mem_cons_self
    have htail := ih (fun b hb => hC b (List.mem_cons_of_mem a hb))
      (fun b hb => hL b (List.mem_cons_of_mem a hb))
    simp only [arithmeticFlatMapWithWork, List.length_cons]
    nlinarith only [ha, hla, htail]

/-- Each complete assignment is stored in an array, so later coordinate
access is constant time. The recursive tail is constructed once. -/


theorem materializedAssignmentsWithWork_value {α : Type*} (M : ℕ) (choices : Fin M → List α) :
    ((materializedAssignmentsWithWork M choices).1.map Vector.get) = finiteAssignments M choices := by
  have hget {m : ℕ} (f : Fin m → α) : (Vector.ofFn f).get = f := funext (vector_get_ofFn f)
  induction M with
  | zero => simp only [materializedAssignmentsWithWork, finiteAssignments, List.map_cons,
      List.map_nil, hget]
  | succ M ih =>
    simp only [materializedAssignmentsWithWork, arithmeticFlatMapWithWork_value,
      arithmeticMapWithWork_value, List.map_flatMap, List.map_map, Function.comp_def, hget]
    unfold finiteAssignments
    apply List.flatMap_congr
    intro head _
    rw [← ih (fun i => choices i.succ), List.map_map]
    rfl

theorem materializedAssignmentsWithWork_cost {α : Type*} (M K : ℕ)
    (choices : Fin M → List α) (hchoices : ∀ i, (choices i).length ≤ K) :
    (materializedAssignmentsWithWork M choices).2 ≤
      (M + 1) * (6 * M + 10) * (K + 1) ^ (M + 1) := by
  induction M with
  | zero =>
    simp only [materializedAssignmentsWithWork, Nat.zero_add, Nat.mul_zero, pow_one, Nat.one_mul]
    omega
  | succ M ih =>
    let previous := materializedAssignmentsWithWork M (fun i => choices i.succ)
    have hprevious := ih (fun i => choices i.succ) (fun i => hchoices i.succ)
    have hlength : previous.1.length ≤ K ^ M := by
      have heq := congrArg List.length
        (materializedAssignmentsWithWork_value M (fun i => choices i.succ))
      simp only [List.length_map] at heq
      exact heq.trans_le (finiteAssignments_length_le M K _ (fun i => hchoices i.succ))
    have hmap (head : α) :
        (arithmeticMapWithWork (fun tail : Vector α M =>
          (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous.1).2 ≤
            previous.1.length * (3 * (M + 1) + 3) :=
      arithmeticMapWithWork_cost _ _ _ (fun _ _ => le_rfl)
    have hmaplength (head : α) :
        (arithmeticMapWithWork (fun tail : Vector α M =>
          (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous.1).1.length ≤
            previous.1.length := by
      rw [arithmeticMapWithWork_value, List.length_map]
    have hflat := arithmeticFlatMapWithWork_cost (fun head =>
      arithmeticMapWithWork (fun tail : Vector α M =>
        (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous.1) (choices 0)
      (previous.1.length * (3 * (M + 1) + 3)) previous.1.length
      (fun head _ => hmap head) (fun head _ => hmaplength head)
    have hchoice := hchoices 0
    have hL : previous.1.length ≤ (K + 1) ^ M :=
      hlength.trans (Nat.pow_le_pow_left (by omega) M)
    have hscale : K * (K + 1) ^ M ≤ (K + 1) ^ (M + 1) := by
      rw [pow_succ]
      nlinarith
    have hZ : K + 1 ≤ (K + 1) ^ (M + 1) := Nat.le_pow (by omega)
    have hexp : (K + 1) ^ (M + 1) ≤ (K + 1) ^ (M + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hexpanded :
        (arithmeticFlatMapWithWork (fun head =>
          arithmeticMapWithWork (fun tail : Vector α M =>
            (Vector.ofFn (Fin.cons head tail.get), 3 * (M + 1))) previous.1) (choices 0)).2 ≤
          (3 * M + 11) * (K + 1) ^ (M + 1) := by
      apply hflat.trans
      calc
        _ ≤ K * ((K + 1) ^ M * (3 * (M + 1) + 3) + (K + 1) ^ M + 3) :=
          Nat.mul_le_mul hchoice (by nlinarith only [hL])
        _ = (3 * M + 7) * (K * (K + 1) ^ M) + 3 * K := by ring
        _ ≤ (3 * M + 7) * (K + 1) ^ (M + 1) + 3 * K :=
          Nat.add_le_add_right (Nat.mul_le_mul_left _ hscale) _
        _ ≤ _ := by nlinarith only [hZ]
    change previous.2 + _ + 1 ≤ _
    have hcoefficient :
        (M + 1) * (6 * M + 10) + (3 * M + 11) + 1 ≤ (M + 2) * (6 * (M + 1) + 10) := by
      nlinarith
    have hone : 1 ≤ (K + 1) ^ (M + 1) := Nat.one_le_pow _ _ (by omega)
    calc
      _ ≤ ((M + 1) * (6 * M + 10) + (3 * M + 11) + 1) * (K + 1) ^ (M + 1) := by
        dsimp only [previous] at *
        nlinarith only [hprevious, hexpanded, hone]
      _ ≤ (M + 2) * (6 * (M + 1) + 10) * (K + 1) ^ (M + 2) :=
        Nat.mul_le_mul hcoefficient hexp
      _ = _ := by rfl

def materializedWideActionsWithWork {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) : List (Vector (TargetInterval ny) M) × ℕ :=
  materializedAssignmentsWithWork M (wideChildStateList parent r b P)

theorem materializedWideActionsWithWork_value {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) :
    ((materializedWideActionsWithWork M parent r b P).1.map Vector.get) =
      wideActionList M parent r b P :=
  materializedAssignmentsWithWork_value M _

/-- Cartesian-product construction after the endpoint lists are present.
Each returned action supports direct indexed reads from its stored array. -/
theorem materializedWideActionsWithWork_cost {nx ny : ℕ} (M : ℕ) (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (hP : 0 < P) :
    (materializedWideActionsWithWork M parent r b P).2 ≤
      (M + 1) * (6 * M + 10) * ((40 * P + 2) ^ 2 + 1) ^ (M + 1) :=
  materializedAssignmentsWithWork_cost M ((40 * P + 2) ^ 2) _
    (wideChildStateList_length_le parent r hP)

end EditApproximation

end OAI
