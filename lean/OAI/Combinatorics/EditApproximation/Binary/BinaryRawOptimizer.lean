import OAI.Combinatorics.EditApproximation.Binary.BinaryRawNumerics
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Complete materialized entropy optimizer on Boolean fraction storage.
Every arithmetic operation invokes the counted Boolean implementation. -/

namespace EditApproximation
namespace BinaryFraction

open Finset



theorem gradientWithWork_representation {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) :
    (gradientWithWork G linear point).1.map representation =
      UnreducedRational.gradient G (linear.map representation) (point.map representation) := by
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_map]
  change ((gradientWithWork G linear point).1.get ⟨i, hi⟩).representation =
    (UnreducedRational.gradient G (linear.map representation) (point.map representation)).get ⟨i, hi⟩
  rw [gradientWithWork, vectorMapWithWork_value]
  simpa only [UnreducedRational.gradient, vector_get_ofFn] using
    gradientCellWithWork_representation G linear point ⟨i, hi⟩



theorem scoredArgmaxWithWork_value {α : Type*} (score : α → BinaryFraction × ℕ) (values : List α) :
    (scoredArgmaxWithWork score values).1 =
      (values.argmax (fun a => (score a).1.value)).map (fun a => (a, (score a).1)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmaxWithWork, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).1.value) with
    | none => rfl
    | some best => simp only [Option.map_some, ltWithWork_value]; split_ifs <;> rfl



theorem maximizerWithWork_representation {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) :
    (maximizerWithWork gradient vertices).1.map representation =
      UnreducedRational.maximizer (gradient.map representation) (vertices.map fun v => v.map representation) := by
  have hscore (v : Vector BinaryFraction d) :
      (dotWithWork gradient v).1.value =
        (UnreducedRational.dot (gradient.map representation) (v.map representation)).value := by
    rw [← dotWithWork_representation, representation_value]
  have hmap := argmax_map_commutes (fun v : Vector BinaryFraction d => v.map representation)
    (fun v => (UnreducedRational.dot (gradient.map representation) v).value) vertices
  simp only [maximizerWithWork, scoredArgmaxWithWork_value, hscore, Option.map_map,
    Function.comp_def, UnreducedRational.maximizer, UnreducedRational.scoredArgmax_spec]
  rw [hmap]
  cases h : vertices.argmax (fun v =>
      (UnreducedRational.dot (gradient.map representation) (v.map representation)).value) with
  | none =>
    apply Vector.ext
    intro i hi
    simp [zero_representation]
  | some v => rfl



theorem optimizerUpdateWithWork_representation {d : ℕ} (j : ℕ)
    (previous selected : Vector BinaryFraction d) (i : Fin d) :
    ((optimizerUpdateWithWork j previous selected).1.get i).representation =
      ((UnreducedRational.one.sub (UnreducedRational.optimizerStep j)).mul
        (previous.get i).representation).add
      ((UnreducedRational.optimizerStep j).mul (selected.get i).representation) := by
  simp only [optimizerUpdateWithWork, vectorMapWithWork_value,
    canonicalAddWithWork_representation, canonicalMulWithWork_representation,
    subWithWork_representation, divWithWork_representation, nat_representation,
    one_representation, UnreducedRational.optimizerStep]



theorem finiteOptimizerWithWork_representation {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G K : ℕ) :
    (finiteOptimizerWithWork vertices linear G K).1.map representation =
      UnreducedRational.finiteOptimizer (vertices.map fun v => v.map representation)
        (linear.map representation) G K := by
  induction K with
  | zero =>
    cases vertices with
    | nil =>
      apply Vector.ext
      intro i hi
      simp [finiteOptimizerWithWork, UnreducedRational.finiteOptimizer, zero_representation]
    | cons v vs => rfl
  | succ K ih =>
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    change (((optimizerUpdateWithWork K (finiteOptimizerWithWork vertices linear G K).1
      (maximizerWithWork (gradientWithWork G linear
        (finiteOptimizerWithWork vertices linear G K).1).1 vertices).1).1.get ⟨i, hi⟩).representation) = _
    rw [optimizerUpdateWithWork_representation]
    have hg := gradientWithWork_representation G linear (finiteOptimizerWithWork vertices linear G K).1
    rw [ih] at hg
    have hm := maximizerWithWork_representation
      (gradientWithWork G linear (finiteOptimizerWithWork vertices linear G K).1).1 vertices
    rw [hg] at hm
    have hp := congrArg (fun v : Vector UnreducedRational d => v.get ⟨i, hi⟩) ih
    have hs := congrArg (fun v : Vector UnreducedRational d => v.get ⟨i, hi⟩) hm
    simpa only [UnreducedRational.finiteOptimizer, vector_map_get, Vector.getElem_ofFn] using
      congrArg₂ UnreducedRational.add
        (congrArg (UnreducedRational.mul (UnreducedRational.one.sub (UnreducedRational.optimizerStep K))) hp)
        (congrArg (UnreducedRational.mul (UnreducedRational.optimizerStep K)) hs)

theorem finiteOptimizerWithWork_value {d : ℕ} (vertices : List (Vector BinaryFraction d))
    (linear : Vector BinaryFraction d) (G K : ℕ) :
    (fun i => ((finiteOptimizerWithWork vertices linear G K).1.get i).value) =
      finiteRationalOptimizer univ (vertices.map fun v i => (v.get i).value)
        (fun i => (linear.get i).value) G K := by
  have h := finiteOptimizerWithWork_representation vertices linear G K
  have hvalue := UnreducedRational.finiteOptimizer_value
    (vertices.map fun v => v.map representation) (linear.map representation) G K
  rw [← h] at hvalue
  simpa only [vector_map_get, representation_value, List.map_map, Function.comp_def] using hvalue

end BinaryFraction
end EditApproximation

end OAI
