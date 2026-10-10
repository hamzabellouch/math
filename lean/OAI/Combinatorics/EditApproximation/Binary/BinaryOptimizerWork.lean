import OAI.Combinatorics.EditApproximation.Binary.BinaryUpdateWork

namespace OAI

/-! Total bit operations of the executed Boolean-fraction optimizer.
The bound includes logarithm sums, gradient materialization, scored vertex
search and every coordinate update, with no unit-cost rational primitive. -/

namespace EditApproximation
namespace BinaryFraction

open Finset

theorem maximizerWithWork_mem {d : ℕ} (gradient : Vector BinaryFraction d)
    (vertices : List (Vector BinaryFraction d)) (hvertices : vertices ≠ []) :
    (maximizerWithWork gradient vertices).1 ∈ vertices := by
  unfold maximizerWithWork
  dsimp only
  rw [scoredArgmaxWithWork_value]
  cases h : vertices.argmax (fun vertex => (dotWithWork gradient vertex).1.value) with
  | none => exact False.elim (hvertices (List.argmax_eq_none.mp h))
  | some vertex =>
    simp only [Option.map_some, Option.getD_some]
    exact List.argmax_mem (by rw [h]; simp)

theorem gradientStorageBudget_mono (G : ℕ) {A B C D : ℕ}
    (hpoint : A ≤ B) (hlinear : C ≤ D) :
    UnreducedRational.gradientStorageBudget G A C ≤
      UnreducedRational.gradientStorageBudget G B D := by
  have hs := UnreducedRational.logarithmStorageBudget_mono
    (show 2 * A + 2 * (5 + 50 * (Nat.size G + 2)) + 2 ≤
      2 * B + 2 * (5 + 50 * (Nat.size G + 2)) + 2 by omega) (G ^ 60)
  unfold UnreducedRational.gradientStorageBudget
  omega

theorem gradientWithWork_width {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d)
    (P L : ℕ) (hp : ∀ i, 0 ≤ (point.get i).value)
    (hpw : ∀ i, (point.get i).width ≤ P) (hlw : ∀ i, (linear.get i).width ≤ L) (i : Fin d) :
    ((gradientWithWork G linear point).1.get i).width ≤
      UnreducedRational.gradientStorageBudget G (2 * P + 1) (2 * L + 1) := by
  simp only [gradientWithWork, vectorMapWithWork_value]
  apply (gradientCellWithWork_width G linear point i (hp i)).trans
  apply gradientStorageBudget_mono
  · exact (representation_storageBits_le _).trans (by have h := hpw i; omega)
  · exact (representation_storageBits_le _).trans (by have h := hlw i; omega)

theorem gradientWithWork_abs {d : ℕ} (G V : ℕ) (linear point : Vector BinaryFraction d)
    (hp : ∀ i, 0 ≤ (point.get i).value)
    (hlv : ∀ i, |(linear.get i).value| ≤ V) (i : Fin d) :
    |((gradientWithWork G linear point).1.get i).value| ≤ (2 * G ^ 60 + 1 + V : ℕ) := by
  have hv := congrArg (fun v : Vector UnreducedRational d => (v.get i).value)
    (gradientWithWork_representation G linear point)
  simp only [vector_map_get, representation_value, UnreducedRational.gradient_value] at hv
  rw [hv]
  have hpos : 0 ≤ (point.get i).value + 1 / (G : ℚ) ^ 50 :=
    add_nonneg (hp i) (div_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg _) _))
  have hlog := rationalLogApproximation_abs_bound _ (G ^ 60) hpos
  unfold rationalSmoothedGradient
  calc
    _ ≤ |-rationalLogApproximation ((point.get i).value + 1 / (G : ℚ) ^ 50) (G ^ 60) - 1| +
      |(linear.get i).value| := abs_add_le _ _
    _ ≤ |rationalLogApproximation ((point.get i).value + 1 / (G : ℚ) ^ 50) (G ^ 60)| + 1 +
      |(linear.get i).value| := by
        have h := abs_add_le (-rationalLogApproximation
          ((point.get i).value + 1 / (G : ℚ) ^ 50) (G ^ 60)) (-1)
        exact add_le_add (by simpa only [sub_eq_add_neg, abs_neg, abs_one] using h) le_rfl
    _ ≤ 2 * (G ^ 60 : ℕ) + 1 + (V : ℚ) := add_le_add (add_le_add hlog le_rfl) (hlv i)
    _ = _ := by push_cast; rfl

def optimizerPointWordBudget (K B Bv : ℕ) : ℕ :=
  Bv + 2 * (B + K * (2 * Nat.size (K + 1) + B)) + 2

def optimizerGradientWordBudget (G K B Bv L : ℕ) : ℕ :=
  UnreducedRational.gradientStorageBudget G (2 * optimizerPointWordBudget K B Bv + 1) (2 * L + 1)

def optimizerRoundBitBudget (d v G K B Bv L V : ℕ) : ℕ :=
  let P := optimizerPointWordBudget K B Bv
  let W := optimizerGradientWordBudget G K B Bv L
  d * (gradientCellBitBudget G P L + 6) +
    maximizerBitBudget d v (max P W) (2 * G ^ 60 + 1 + V + 1) +
    optimizerUpdateBitBudget d K P + 3

def optimizerBitBudget (d v G K B Bv L V : ℕ) : ℕ :=
  d + 1 + K * optimizerRoundBitBudget d v G K B Bv L V

theorem finiteOptimizerWithWork_cost {d : ℕ}
    (vertices : List (Vector BinaryFraction d)) (linear : Vector BinaryFraction d)
    (G K B Bv L V : ℕ) (hvertices : vertices ≠ [])
    (hinput : ∀ v ∈ vertices, ∀ i : Fin d,
      (v.get i).width ≤ (v.get i).representation.storageBits ∧
      (0 ≤ (v.get i).value ∧ (v.get i).value ≤ 1) ∧
      Nat.size (v.get i).representation.den ≤ B)
    (hvw : ∀ v ∈ vertices, ∀ i, (v.get i).width ≤ Bv)
    (hlw : ∀ i, (linear.get i).width ≤ L)
    (hlv : ∀ i, |(linear.get i).value| ≤ V) :
    (finiteOptimizerWithWork vertices linear G K).2 ≤
      optimizerBitBudget d vertices.length G K B Bv L V := by
  let P := optimizerPointWordBudget K B Bv
  let W := optimizerGradientWordBudget G K B Bv L
  have hpoint (j : ℕ) (hj : j ≤ K) (i : Fin d) :
      ((finiteOptimizerWithWork vertices linear G j).1.get i).width ≤ P := by
    have hw := finiteOptimizerWithWork_coordinate_width vertices linear G j B hvertices hinput i
    have hsize := Nat.size_le_size (show j + 1 ≤ K + 1 by omega)
    have hm := Nat.mul_le_mul hj
      (show 2 * Nat.size (j + 1) + B ≤ 2 * Nat.size (K + 1) + B by omega)
    dsimp only [P, optimizerPointWordBudget]
    omega
  have hpositive (j : ℕ) (i : Fin d) :
      0 ≤ ((finiteOptimizerWithWork vertices linear G j).1.get i).value := by
    have hn : (vertices.map fun v i => (v.get i).value) ≠ [] := by
      intro h
      exact hvertices (List.map_eq_nil_iff.mp h)
    have h := finiteRationalOptimizer_coordinate_bounds univ
      (vertices.map fun v i => (v.get i).value) (fun i => (linear.get i).value) G j hn i (by
        intro v hv
        obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
        exact (hinput w hw i).2.1)
    rw [← congrFun (finiteOptimizerWithWork_value vertices linear G j) i] at h
    exact h.1
  have hvert (v : Vector BinaryFraction d) (hv : v ∈ vertices) (i : Fin d) : (v.get i).width ≤ P := by
    have h := hvw v hv i
    dsimp only [P, optimizerPointWordBudget]
    omega
  have hvertexAbs (v : Vector BinaryFraction d) (hv : v ∈ vertices) (i : Fin d) :
      |(v.get i).value| ≤ (2 * G ^ 60 + 1 + V + 1 : ℕ) := by
    rw [abs_of_nonneg (hinput v hv i).2.1.1]
    exact (hinput v hv i).2.1.2.trans (by exact_mod_cast (show 1 ≤ 2 * G ^ 60 + 1 + V + 1 by omega))
  have hcost : ∀ j ≤ K, (finiteOptimizerWithWork vertices linear G j).2 ≤
      d + 1 + j * optimizerRoundBitBudget d vertices.length G K B Bv L V := by
    intro j
    induction j with
    | zero => intro _; simp only [finiteOptimizerWithWork, Nat.zero_mul, Nat.add_zero, le_refl]
    | succ j ih =>
      intro hj
      have hj' : j ≤ K := by omega
      have hcprev := ih hj'
      let previous := (finiteOptimizerWithWork vertices linear G j).1
      let grad := (gradientWithWork G linear previous).1
      let selected := (maximizerWithWork grad vertices).1
      have hcgrad := gradientWithWork_cost G linear previous P L
        (hpositive j) (hpoint j hj') hlw
      have hwgrad (i : Fin d) : (grad.get i).width ≤ W :=
        gradientWithWork_width G linear previous P L (hpositive j) (hpoint j hj') hlw i
      have hvgrad (i : Fin d) : |(grad.get i).value| ≤ (2 * G ^ 60 + 1 + V + 1 : ℕ) :=
        (gradientWithWork_abs G V linear previous (hpositive j) hlv i).trans (by exact_mod_cast Nat.le_add_right _ 1)
      have hcmax := maximizerWithWork_cost grad vertices (max P W) (2 * G ^ 60 + 1 + V + 1)
        (fun i => (hwgrad i).trans (Nat.le_max_right _ _)) hvgrad
        (fun v hv i => (hvert v hv i).trans (Nat.le_max_left _ _)) hvertexAbs
      have hcupdate := optimizerUpdateWithWork_cost j K P hj' previous selected
        (hpoint j hj') (fun i => hvert selected (maximizerWithWork_mem grad vertices hvertices) i)
      change (finiteOptimizerWithWork vertices linear G j).2 + (gradientWithWork G linear previous).2 +
        (maximizerWithWork grad vertices).2 + (optimizerUpdateWithWork j previous selected).2 + 3 ≤ _
      change _ ≤ d + 1 + (j + 1) *
        (d * (gradientCellBitBudget G P L + 6) +
          maximizerBitBudget d vertices.length (max P W) (2 * G ^ 60 + 1 + V + 1) +
          optimizerUpdateBitBudget d K P + 3)
      change (finiteOptimizerWithWork vertices linear G j).2 ≤ d + 1 + j *
        (d * (gradientCellBitBudget G P L + 6) +
          maximizerBitBudget d vertices.length (max P W) (2 * G ^ 60 + 1 + V + 1) +
          optimizerUpdateBitBudget d K P + 3) at hcprev
      rw [Nat.add_mul, Nat.one_mul]
      omega
  exact hcost K le_rfl

end BinaryFraction
end EditApproximation

end OAI
