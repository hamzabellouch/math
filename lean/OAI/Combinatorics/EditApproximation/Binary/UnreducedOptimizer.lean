import OAI.Combinatorics.EditApproximation.Binary.UnreducedNumerics
import OAI.Combinatorics.EditApproximation.Numerics.VectorOptimizerWork
import OAI.Combinatorics.EditApproximation.Numerics.OptimizerBits

namespace OAI

/-! A fraction-only implementation of the actual finite optimizer. None of
its arithmetic or score comparisons requires reduced rational numbers. -/

namespace EditApproximation

open Finset
namespace UnreducedRational

def scoredArgmax {α : Type*} (score : α → UnreducedRational) : List α → Option (α × UnreducedRational)
  | [] => none
  | a :: rest =>
    let current := score a
    match scoredArgmax score rest with
    | none => some (a, current)
    | some best => if current.lt best.2 then some best else some (a, current)

theorem scoredArgmax_spec {α : Type*} (score : α → UnreducedRational) (values : List α) :
    scoredArgmax score values =
      (values.argmax (fun a => (score a).value)).map (fun a => (a, score a)) := by
  induction values with
  | nil => rfl
  | cons a rest ih =>
    simp only [scoredArgmax, ih, List.argmax_cons]
    cases h : rest.argmax (fun a => (score a).value) with
    | none => rfl
    | some best => simp only [Option.map_some, lt_eq_true]; split_ifs <;> rfl

def dotList {d : ℕ} (left right : Vector UnreducedRational d) : List (Fin d) → UnreducedRational
  | [] => zero
  | i :: rest => ((left.get i).mul (right.get i)).add (dotList left right rest)

def dot {d : ℕ} (left right : Vector UnreducedRational d) : UnreducedRational :=
  dotList left right (List.finRange d)

theorem dotList_value {d : ℕ} (left right : Vector UnreducedRational d) (indices : List (Fin d)) :
    (dotList left right indices).value =
      (indices.map fun i => (left.get i).value * (right.get i).value).sum := by
  induction indices with
  | nil => simp [dotList]
  | cons i rest ih => simp [dotList, ih]

theorem dot_value {d : ℕ} (left right : Vector UnreducedRational d) :
    (dot left right).value = ∑ i, (left.get i).value * (right.get i).value := by
  simp only [dot, dotList_value]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

def gradientCell {d : ℕ} (G : ℕ) (linear point : Vector UnreducedRational d) (i : Fin d) : UnreducedRational :=
  ((logarithm ((point.get i).add ((nat G).pow 50).inv) (G ^ 60)).neg.sub one).add (linear.get i)

def gradient {d : ℕ} (G : ℕ) (linear point : Vector UnreducedRational d) : Vector UnreducedRational d :=
  Vector.ofFn (gradientCell G linear point)

theorem gradient_value {d : ℕ} (G : ℕ) (linear point : Vector UnreducedRational d) (i : Fin d) :
    ((gradient G linear point).get i).value =
      rationalSmoothedGradient G (fun i => (linear.get i).value) (fun i => (point.get i).value) i := by
  simp [gradient, gradientCell, rationalSmoothedGradient, one_div]

def maximizer {d : ℕ} (gradient : Vector UnreducedRational d)
    (vertices : List (Vector UnreducedRational d)) : Vector UnreducedRational d :=
  ((scoredArgmax (dot gradient) vertices).map Prod.fst).getD (Vector.replicate d zero)

theorem maximizer_value {d : ℕ} (gradient : Vector UnreducedRational d)
    (vertices : List (Vector UnreducedRational d)) :
    (fun i => ((maximizer gradient vertices).get i).value) =
      rationalLinearizationMaximizer univ
        (vertices.map fun vertex i => (vertex.get i).value) (fun i => (gradient.get i).value) := by
  have hmap := argmax_map_commutes (fun vertex : Vector UnreducedRational d => fun i => (vertex.get i).value)
    (fun vertex => ∑ i, (gradient.get i).value * vertex i) vertices
  simp only [maximizer, scoredArgmax_spec, dot_value, Option.map_map, Function.comp_def]
  unfold rationalLinearizationMaximizer
  rw [hmap]
  cases h : vertices.argmax (fun vertex => ∑ i, (gradient.get i).value * (vertex.get i).value) with
  | none => funext i; simp [value_zero]
  | some vertex => rfl

def finiteOptimizer {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G : ℕ) : ℕ → Vector UnreducedRational d
  | 0 => vertices.headD (Vector.replicate d zero)
  | j + 1 =>
    let previous := finiteOptimizer vertices linear G j
    let selected := maximizer (gradient G linear previous) vertices
    Vector.ofFn fun i => ((one.sub (optimizerStep j)).mul (previous.get i)).add
      ((optimizerStep j).mul (selected.get i))

theorem finiteOptimizer_value {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G K : ℕ) :
    (fun i => ((finiteOptimizer vertices linear G K).get i).value) =
      finiteRationalOptimizer univ (vertices.map fun vertex i => (vertex.get i).value)
        (fun i => (linear.get i).value) G K := by
  induction K with
  | zero =>
    cases vertices with
    | nil => funext i; simp [finiteOptimizer, finiteRationalOptimizer]
    | cons vertex rest => rfl
  | succ K ih =>
    funext i
    simp only [finiteOptimizer, vector_get_ofFn, value_add, value_mul, value_sub, value_one,
      optimizerStep_value, finiteRationalOptimizer]
    rw [congrFun ih i]
    have hm := maximizer_value (gradient G linear (finiteOptimizer vertices linear G K)) vertices
    have hg : (fun i => ((gradient G linear (finiteOptimizer vertices linear G K)).get i).value) =
        rationalSmoothedGradient G (fun i => (linear.get i).value)
          (finiteRationalOptimizer univ (vertices.map fun vertex i => (vertex.get i).value)
            (fun i => (linear.get i).value) G K) := by
      funext i
      rw [gradient_value]
      rw [ih]
    rw [hg] at hm
    rw [congrFun hm i]

theorem maximizer_mem {d : ℕ} (gradient : Vector UnreducedRational d)
    (vertices : List (Vector UnreducedRational d)) (hvertices : vertices ≠ []) :
    maximizer gradient vertices ∈ vertices := by
  unfold maximizer
  rw [scoredArgmax_spec]
  cases h : vertices.argmax (fun vertex => (dot gradient vertex).value) with
  | none => exact False.elim (hvertices (List.argmax_eq_none.mp h))
  | some vertex =>
    simp only [Option.map_some, Option.getD_some]
    exact List.argmax_mem (by rw [h]; simp)

theorem finiteOptimizer_eq_iterate {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G K : ℕ) (i : Fin d) :
    (finiteOptimizer vertices linear G K).get i =
      optimizerIterate (vertices.headD (Vector.replicate d zero)).get
        (fun j => (maximizer (gradient G linear (finiteOptimizer vertices linear G j)) vertices).get) K i := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [finiteOptimizer, vector_get_ofFn, optimizerIterate, ih]

theorem finiteOptimizer_den_bits {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G K B : ℕ) (i : Fin d)
    (hvertices : vertices ≠ [])
    (hinput : ∀ vertex ∈ vertices, Nat.size (vertex.get i).den ≤ B) :
    Nat.size ((finiteOptimizer vertices linear G K).get i).den ≤
      B + K * (2 * Nat.size (K + 1) + B) := by
  rw [finiteOptimizer_eq_iterate]
  apply optimizerIterate_den_bits
  · apply hinput
    cases vertices with
    | nil => exact False.elim (hvertices rfl)
    | cons vertex rest => exact List.mem_cons_self
  · intro j _
    exact hinput _ (maximizer_mem _ vertices hvertices)

theorem finiteOptimizer_storageBits {d : ℕ} (vertices : List (Vector UnreducedRational d))
    (linear : Vector UnreducedRational d) (G K B : ℕ) (i : Fin d)
    (hvertices : vertices ≠ [])
    (hinput : ∀ vertex ∈ vertices,
      (0 ≤ (vertex.get i).value ∧ (vertex.get i).value ≤ 1) ∧ Nat.size (vertex.get i).den ≤ B) :
    ((finiteOptimizer vertices linear G K).get i).storageBits ≤
      2 * (B + K * (2 * Nat.size (K + 1) + B)) + 2 := by
  have hlist : (vertices.map fun vertex j => (vertex.get j).value) ≠ [] := by
    intro h
    exact hvertices (List.map_eq_nil_iff.mp h)
  have hpoint := finiteRationalOptimizer_coordinate_bounds univ
    (vertices.map fun vertex j => (vertex.get j).value) (fun j => (linear.get j).value)
    G K hlist i (by
      intro vertex hv
      obtain ⟨stored, hs, rfl⟩ := List.mem_map.mp hv
      exact (hinput stored hs).1)
  rw [← congrFun (finiteOptimizer_value vertices linear G K) i] at hpoint
  have h := storageBits_le ((finiteOptimizer vertices linear G K).get i) 1
    (B + K * (2 * Nat.size (K + 1) + B)) (by
      rw [abs_of_nonneg hpoint.1]
      exact hpoint.2) (finiteOptimizer_den_bits vertices linear G K B i hvertices
        (fun vertex hv => (hinput vertex hv).2))
  simp only [Nat.size_one] at h
  omega

end UnreducedRational
end EditApproximation

end OAI
