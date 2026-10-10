import OAI.Combinatorics.EditApproximation.Binary.BinaryOptimizerWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The final Boolean maximization retains the actual action label. This
is the sampled atom of the optimizer, rather than its averaged vector. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem dotWithWork_value {d : ℕ} (left right : Vector BinaryFraction d) :
    (dotWithWork left right).1.value = ∑ i, (left.get i).value * (right.get i).value := by
  rw [← representation_value, dotWithWork_representation, UnreducedRational.dot_value]
  simp only [vector_map_get, representation_value]

theorem gradientWithWork_value {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) (i : Fin d) :
    ((gradientWithWork G linear point).1.get i).value =
      rationalSmoothedGradient G (fun j => (linear.get j).value) (fun j => (point.get j).value) i := by
  have h := congrArg (fun v : Vector UnreducedRational d => (v.get i).value)
    (gradientWithWork_representation G linear point)
  simp only [vector_map_get, representation_value, UnreducedRational.gradient_value] at h
  simpa only [vector_map_get, representation_value] using h



theorem selectionWithWork_value {α : Type*} {d : ℕ}
    (vertices : List (α × Vector BinaryFraction d)) (linear : Vector BinaryFraction d) (G j : ℕ) :
    (selectionWithWork vertices linear G j).1 =
      (materializedSelectionWithWork
        (vertices.map fun v => (v.1, v.2.map value)) (linear.map value) G j).1 := by
  rw [materializedSelectionWithWork_value, argmax_map_commutes]
  simp only [selectionWithWork, scoredArgmaxWithWork_value, Option.map_map, Function.comp_def]
  apply congrArg (fun score => (vertices.argmax score).map Prod.fst)
  funext vertex
  rw [dotWithWork_value]
  have hget (v : Vector BinaryFraction d) : (v.map value).get = fun i => (v.get i).value := by
    funext i
    exact vector_map_get value v i
  simp only [gradientWithWork_value, finiteOptimizerWithWork_value,
    List.map_map, vector_map_get, Function.comp_def, hget]

theorem scoredArgmaxWithWork_map_cost {α β : Type*} (mapping : α → β)
    (score : β → BinaryFraction × ℕ) (values : List α) :
    (scoredArgmaxWithWork (fun a => score (mapping a)) values).2 =
      (scoredArgmaxWithWork score (values.map mapping)).2 := by
  have h : (scoredArgmaxWithWork score (values.map mapping)).1 =
      (scoredArgmaxWithWork (fun a => score (mapping a)) values).1.map
        (fun result => (mapping result.1, result.2)) ∧
      (scoredArgmaxWithWork (fun a => score (mapping a)) values).2 =
        (scoredArgmaxWithWork score (values.map mapping)).2 := by
    induction values with
    | nil => exact ⟨rfl, rfl⟩
    | cons head tail ih =>
      simp only [List.map_cons, scoredArgmaxWithWork, ih.1, ← ih.2]
      cases htail : (scoredArgmaxWithWork (fun a => score (mapping a)) tail).1 with
      | none => exact ⟨rfl, rfl⟩
      | some best =>
        simp only [Option.map_some]
        split_ifs <;> simp
  exact h.2

def selectionBitBudget (d vertices G K B Bv L V : ℕ) : ℕ :=
  let P := optimizerPointWordBudget K B Bv
  let W := optimizerGradientWordBudget G K B Bv L
  optimizerBitBudget d vertices G K B Bv L V + d * (gradientCellBitBudget G P L + 6) +
    maximizerBitBudget d vertices (max P W) (2 * G ^ 60 + 1 + V + 1)

theorem selectionWithWork_cost {α : Type*} {d : ℕ}
    (vertices : List (α × Vector BinaryFraction d)) (linear : Vector BinaryFraction d)
    (G K B Bv L V : ℕ) (hvertices : vertices ≠ [])
    (hinput : ∀ v ∈ vertices, ∀ i : Fin d,
      (v.2.get i).width ≤ (v.2.get i).representation.storageBits ∧
      (0 ≤ (v.2.get i).value ∧ (v.2.get i).value ≤ 1) ∧
      Nat.size (v.2.get i).representation.den ≤ B)
    (hvw : ∀ v ∈ vertices, ∀ i, (v.2.get i).width ≤ Bv)
    (hlw : ∀ i, (linear.get i).width ≤ L)
    (hlv : ∀ i, |(linear.get i).value| ≤ V) :
    (selectionWithWork vertices linear G K).2 ≤ selectionBitBudget d vertices.length G K B Bv L V := by
  let points := vertices.map Prod.snd
  let point := (finiteOptimizerWithWork points linear G K).1
  let grad := (gradientWithWork G linear point).1
  let P := optimizerPointWordBudget K B Bv
  let W := optimizerGradientWordBudget G K B Bv L
  have hpnonempty : points ≠ [] := by
    intro h
    exact hvertices (List.map_eq_nil_iff.mp h)
  have hpinput (v : Vector BinaryFraction d) (hv : v ∈ points) (i : Fin d) :
      (v.get i).width ≤ (v.get i).representation.storageBits ∧
      (0 ≤ (v.get i).value ∧ (v.get i).value ≤ 1) ∧ Nat.size (v.get i).representation.den ≤ B := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact hinput a ha i
  have hpw (v : Vector BinaryFraction d) (hv : v ∈ points) (i : Fin d) : (v.get i).width ≤ Bv := by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
    exact hvw a ha i
  have hpoint (i : Fin d) : (point.get i).width ≤ P := by
    have h := finiteOptimizerWithWork_coordinate_width points linear G K B hpnonempty hpinput i
    change (point.get i).width ≤ _ at h
    dsimp only [P, optimizerPointWordBudget]
    omega
  have hpositive (i : Fin d) : 0 ≤ (point.get i).value := by
    have hn : (points.map fun v i => (v.get i).value) ≠ [] := by
      intro h
      exact hpnonempty (List.map_eq_nil_iff.mp h)
    have h := finiteRationalOptimizer_coordinate_bounds univ
      (points.map fun v i => (v.get i).value) (fun i => (linear.get i).value) G K hn i (by
        intro v hv
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        exact (hpinput w hw i).2.1)
    rw [← congrFun (finiteOptimizerWithWork_value points linear G K) i] at h
    exact h.1
  have hgw (i : Fin d) : (grad.get i).width ≤ W :=
    gradientWithWork_width G linear point P L hpositive hpoint hlw i
  have hgv (i : Fin d) : |(grad.get i).value| ≤ (2 * G ^ 60 + 1 + V + 1 : ℕ) :=
    (gradientWithWork_abs G V linear point hpositive hlv i).trans
      (by exact_mod_cast Nat.le_add_right (2 * G ^ 60 + 1 + V) 1)
  have hvP (v : Vector BinaryFraction d) (hv : v ∈ points) (i : Fin d) : (v.get i).width ≤ P := by
    have h := hpw v hv i
    dsimp only [P, optimizerPointWordBudget]
    omega
  have hvabs (v : Vector BinaryFraction d) (hv : v ∈ points) (i : Fin d) :
      |(v.get i).value| ≤ (2 * G ^ 60 + 1 + V + 1 : ℕ) := by
    rw [abs_of_nonneg (hpinput v hv i).2.1.1]
    exact (hpinput v hv i).2.1.2.trans (by exact_mod_cast
      (show 1 ≤ 2 * G ^ 60 + 1 + V + 1 by omega))
  have hiterate := finiteOptimizerWithWork_cost points linear G K B Bv L V hpnonempty hpinput hpw hlw hlv
  have hgradient := gradientWithWork_cost G linear point P L hpositive hpoint hlw
  have hselected := maximizerWithWork_cost grad points (max P W) (2 * G ^ 60 + 1 + V + 1)
    (fun i => (hgw i).trans (Nat.le_max_right _ _)) hgv
    (fun v hv i => (hvP v hv i).trans (Nat.le_max_left _ _)) hvabs
  rw [maximizerWithWork, ← scoredArgmaxWithWork_map_cost Prod.snd (dotWithWork grad) vertices] at hselected
  simp only [points, List.length_map] at hiterate hselected
  change (finiteOptimizerWithWork points linear G K).2 ≤ _ at hiterate
  change (finiteOptimizerWithWork points linear G K).2 + (gradientWithWork G linear point).2 +
    (scoredArgmaxWithWork (fun vertex => dotWithWork grad vertex.2) vertices).2 + 1 ≤ _
  change _ ≤ optimizerBitBudget d vertices.length G K B Bv L V +
    d * (gradientCellBitBudget G P L + 6) +
      maximizerBitBudget d vertices.length (max P W) (2 * G ^ 60 + 1 + V + 1)
  omega

end BinaryFraction
end EditApproximation

end OAI
