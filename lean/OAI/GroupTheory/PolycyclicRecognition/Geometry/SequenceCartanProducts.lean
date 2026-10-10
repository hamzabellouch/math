import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWordLogarithms
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Products of the Cartan factors of two probe paths -/

noncomputable section
namespace PolycyclicRecognition

open Module LieModule Filter
open scoped Manifold Topology

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  {ED D : Type*} [NormedAddCommGroup ED] [NormedSpace ℝ ED]
  [FiniteDimensional ℝ ED] [TopologicalSpace D] [ChartedSpace ED D] [Group D]
  [LieGroup (𝓘(ℝ, ED)) ⊤ D] [T2Space D]
  (eD : H ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, ED)) D)
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D) (hbijD : Function.Bijective ExpD)

/-- A common subexponential box contains the products of every allowed
pair of Cartan factors, including the final right-cell increment. -/
theorem exists_sequence_cartan_product_bound
    (hExpD : IsGroupExponential ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
    (scale R₁ R₂ : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR₁0 : ∀ n, 0 ≤ R₁ n) (hR₂0 : ∀ n, 0 ≤ R₂ n)
    (hR₁ : HasSubexponentialUpperBoundSeq scale R₁)
    (hR₂ : HasSubexponentialUpperBoundSeq scale R₂) :
    ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ n (d e : D),
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD d)‖ ≤ R₁ n →
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD e)‖ ≤ R₂ n →
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD (d * e))‖ ≤ R n := by
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℝ H H
  obtain ⟨K, hK, hbracket⟩ := exists_basis_structureConstant_bound (finBasis ℝ H)
  let A : ℝ := (c : ℝ) * 2 ^ c * (1 + (finrank ℝ H : ℝ) ^ 2 * K) ^ c
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let R := fun n => A * (1 + (R₁ n + R₂ n)) ^ c * (1 + (2 : ℝ)) ^ c
  have hsum : HasSubexponentialUpperBoundSeq scale (fun n => 1 + (R₁ n + R₂ n)) :=
    (sequence_subexponential_upper_const hs 1).add (hR₁.add hR₂ hs) hs
  have hsum0 : ∀ n, 0 ≤ 1 + (R₁ n + R₂ n) := fun n => by
    linarith [hR₁0 n, hR₂0 n]
  refine ⟨R, fun n => mul_nonneg (mul_nonneg hA (pow_nonneg (hsum0 n) _))
    (by positivity), ?_, ?_⟩
  · exact ((sequence_subexponential_upper_const hs A).mul
      (hsum.pow hs (Eventually.of_forall hsum0) c) (Eventually.of_forall (fun _ => hA))).mul
      (sequence_subexponential_upper_const hs ((1 + (2 : ℝ)) ^ c))
      (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (hsum0 n) _)))
  intro n d e hd he
  have hmem (j : Fin 2) : ![d, e] j ∈ exponentialCoordinateBox (ExpD ∘ eD)
      (finBasis ℝ H) (R₁ n + R₂ n) := by
    fin_cases j
    · exact ⟨cartanLog H eD ExpD hbijD d, exp_cartanLog H eD ExpD hbijD d,
        hd.trans (le_add_of_nonneg_right (hR₂0 n))⟩
    · exact ⟨cartanLog H eD ExpD hbijD e, exp_cartanLog H eD ExpD hbijD e,
        he.trans (le_add_of_nonneg_left (hR₁0 n))⟩
  obtain ⟨v, hv, hnorm⟩ := product_mem_exponentialCoordinateBox dynkinD eD ExpD hExpD hc
    (finBasis ℝ H) hK (add_nonneg (hR₁0 n) (hR₂0 n)) hbracket ![d, e] hmem
  have hv' : ExpD (eD v) = d * e := by simpa using hv
  rw [← hv', cartanLog_exp]
  simpa [R, A] using hnorm

end PolycyclicRecognition

end

end OAI
