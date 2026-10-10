import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanProducts

namespace OAI

/-! # Uniform Cartan logarithms for a fixed finite number of transitions -/

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

/-- Polynomial word growth is uniform for all prefixes of a fixed finite tuple,
even when the allowed single-transition radius varies subexponentially. -/
theorem exists_sequence_cartan_prefix_bound
    (hExpD : IsGroupExponential ExpD) (dynkinD : NilpotentDynkinExpansionInput ED D)
    (h : ℕ) (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hR0 : ∀ n, 0 ≤ R n) (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ S : ℕ → ℝ, (∀ n, 0 ≤ S n) ∧ HasSubexponentialUpperBoundSeq scale S ∧
      ∀ n (u : ℕ → D),
        (∀ j < h, ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD (u j))‖ ≤ R n) →
        ∀ m ≤ h, ‖(finBasis ℝ H).equivFun
          (cartanLog H eD ExpD hbijD (wordPrefix u m))‖ ≤ S n := by
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℝ H H
  obtain ⟨K, hK, hbracket⟩ := exists_basis_structureConstant_bound (finBasis ℝ H)
  let A : ℝ := (c : ℝ) * 2 ^ c * (1 + (finrank ℝ H : ℝ) ^ 2 * K) ^ c
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let S := fun n => A * (1 + R n) ^ c * (1 + (h : ℝ)) ^ c
  have hsum : HasSubexponentialUpperBoundSeq scale (fun n => 1 + R n) :=
    (sequence_subexponential_upper_const hs 1).add hR hs
  have hsum0 : ∀ n, 0 ≤ 1 + R n := fun n => by linarith [hR0 n]
  refine ⟨S, fun n => mul_nonneg (mul_nonneg hA (pow_nonneg (hsum0 n) _))
    (by positivity), ?_, ?_⟩
  · exact ((sequence_subexponential_upper_const hs A).mul
      (hsum.pow hs (Eventually.of_forall hsum0) c) (Eventually.of_forall (fun _ => hA))).mul
      (sequence_subexponential_upper_const hs ((1 + (h : ℝ)) ^ c))
      (Eventually.of_forall (fun n => mul_nonneg hA (pow_nonneg (hsum0 n) _)))
  intro n u hu m hm
  have hmem (j : Fin m) : u j.val ∈ exponentialCoordinateBox (ExpD ∘ eD)
      (finBasis ℝ H) (R n) :=
    ⟨cartanLog H eD ExpD hbijD (u j.val), exp_cartanLog H eD ExpD hbijD (u j.val),
      hu j.val (j.isLt.trans_le hm)⟩
  obtain ⟨v, hv, hnorm⟩ := product_mem_exponentialCoordinateBox dynkinD eD ExpD hExpD hc
    (finBasis ℝ H) hK (hR0 n) hbracket (fun j : Fin m => u j.val) hmem
  change ExpD (eD v) = wordPrefix u m at hv
  rw [← hv, cartanLog_exp]
  have hb : ‖(finBasis ℝ H).equivFun v‖ ≤
      A * (1 + R n) ^ c * (1 + (m : ℝ)) ^ c := by
    simpa only [Fintype.card_fin, A] using hnorm
  apply hb.trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left hm 1) c)
    (mul_nonneg hA (pow_nonneg (hsum0 n) _))

end PolycyclicRecognition

end

end OAI
