import OAI.Combinatorics.EditApproximation.Binary.BinaryRawOptimizer
import OAI.Combinatorics.EditApproximation.Binary.UnreducedStorage

namespace OAI

/-! Actual Boolean word lengths in the materialized numerical implementation.
These bounds use the stored unreduced values, without a gcd reduction. -/

namespace EditApproximation
namespace BinaryFraction

theorem gradientCellWithWork_width {d : ℕ} (G : ℕ)
    (linear point : Vector BinaryFraction d) (i : Fin d) (hpoint : 0 ≤ (point.get i).value) :
    (gradientCellWithWork G linear point i).1.width ≤
      UnreducedRational.gradientStorageBudget G (point.get i).representation.storageBits
        (linear.get i).representation.storageBits := by
  have hraw := UnreducedRational.gradientCell_storageBits G (linear.map representation)
    (point.map representation) i (by simpa only [vector_map_get, representation_value] using hpoint)
  simp only [vector_map_get] at hraw
  have hwidth := gradientCellWithWork_width_le_storageBits G linear point i
  rw [gradientCellWithWork_representation] at hwidth
  exact hwidth.trans hraw

theorem logarithmWithWork_width (r : BinaryFraction) (K : ℕ) (hr : 0 ≤ r.value) :
    (r.logarithmWithWork K).1.width ≤
      UnreducedRational.logarithmStorageBudget r.representation.storageBits K := by
  have hwidth := logarithmWithWork_width_le_storageBits r K
  rw [logarithmWithWork_representation] at hwidth
  exact hwidth.trans (UnreducedRational.logarithm_storageBits_poly _ _ hr)

theorem dotListWithWork_width {d : ℕ} (left right : Vector BinaryFraction d)
    (indices : List (Fin d)) (BL BR VL VR : ℕ)
    (hlbits : ∀ i ∈ indices, Nat.size (left.get i).representation.den ≤ BL)
    (hrbits : ∀ i ∈ indices, Nat.size (right.get i).representation.den ≤ BR)
    (hlvalue : ∀ i ∈ indices, |(left.get i).value| ≤ VL)
    (hrvalue : ∀ i ∈ indices, |(right.get i).value| ≤ VR) :
    (dotListWithWork left right indices).1.width ≤ Nat.size (indices.length * VL * VR) +
      2 * (1 + indices.length * (BL + BR)) + 1 := by
  have hwidth := dotListWithWork_width_le_storageBits left right indices
  rw [dotListWithWork_representation] at hwidth
  apply hwidth.trans
  apply UnreducedRational.dotList_storageBits _ _ _ BL BR VL VR
  · simpa only [vector_map_get] using hlbits
  · simpa only [vector_map_get] using hrbits
  · simpa only [vector_map_get, representation_value] using hlvalue
  · simpa only [vector_map_get, representation_value] using hrvalue

theorem finiteOptimizerWithWork_coordinate_normalized {d : ℕ}
    (vertices : List (Vector BinaryFraction d)) (linear : Vector BinaryFraction d) (G K : ℕ)
    (hvertices : vertices ≠ [])
    (hinput : ∀ v ∈ vertices, ∀ i : Fin d, (v.get i).width ≤ (v.get i).representation.storageBits)
    (i : Fin d) :
    ((finiteOptimizerWithWork vertices linear G K).1.get i).width ≤
      ((finiteOptimizerWithWork vertices linear G K).1.get i).representation.storageBits := by
  cases K with
  | zero =>
    cases vertices with
    | nil => exact False.elim (hvertices rfl)
    | cons v vs => exact hinput v List.mem_cons_self i
  | succ K =>
    simp only [finiteOptimizerWithWork, optimizerUpdateWithWork, vectorMapWithWork_value]
    exact canonicalAddWithWork_self_width _ _

theorem finiteOptimizerWithWork_coordinate_width {d : ℕ}
    (vertices : List (Vector BinaryFraction d)) (linear : Vector BinaryFraction d) (G K B : ℕ)
    (hvertices : vertices ≠ [])
    (hinput : ∀ v ∈ vertices, ∀ i : Fin d,
      (v.get i).width ≤ (v.get i).representation.storageBits ∧
      (0 ≤ (v.get i).value ∧ (v.get i).value ≤ 1) ∧ Nat.size (v.get i).representation.den ≤ B)
    (i : Fin d) :
    ((finiteOptimizerWithWork vertices linear G K).1.get i).width ≤
      2 * (B + K * (2 * Nat.size (K + 1) + B)) + 2 := by
  have hn : (vertices.map fun v => v.map representation) ≠ [] := by
    intro h
    exact hvertices (List.map_eq_nil_iff.mp h)
  have hr := UnreducedRational.finiteOptimizer_storageBits
    (vertices.map fun v => v.map representation) (linear.map representation) G K B i hn (by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      simpa only [vector_map_get, representation_value] using (hinput w hw i).2)
  have hrep := congrArg (fun v : Vector UnreducedRational d => v.get i)
    (finiteOptimizerWithWork_representation vertices linear G K)
  simp only [vector_map_get] at hrep
  rw [← hrep] at hr
  exact (finiteOptimizerWithWork_coordinate_normalized vertices linear G K hvertices
    (fun v hv i => (hinput v hv i).1) i).trans hr

end BinaryFraction
end EditApproximation

end OAI
