import OAI.GroupTheory.PolycyclicRecognition.Geometry.SequenceCartanProducts

namespace OAI

/-! # The Cartan coordinate of an overlap error

Two controlled Cartan positions and a bounded right displacement give a
subexponential logarithm for `d * b * e⁻¹`.
-/

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
  (ExpD : GroupLieAlgebra (𝓘(ℝ, ED)) D → D)
  (hbijD : Function.Bijective ExpD) (hExpD : IsGroupExponential ExpD)

include hExpD

omit [FiniteDimensional ℝ L] [H.IsCartanSubalgebra] [T2Space D] in
theorem cartanLog_inv (d : D) :
    cartanLog H eD ExpD hbijD d⁻¹ = -cartanLog H eD ExpD hbijD d := by
  have he : ExpD (eD (-cartanLog H eD ExpD hbijD d)) = d⁻¹ := by
    rw [map_neg, hExpD.map_neg, exp_cartanLog H eD ExpD hbijD d]
  rw [← he, cartanLog_exp H eD ExpD hbijD]

theorem exists_sequence_cartan_overlap_bound
    (dynkinD : NilpotentDynkinExpansionInput ED D)
    (scale RH RB : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hRH0 : ∀ n, 0 ≤ RH n) (hRB0 : ∀ n, 0 ≤ RB n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hRB : HasSubexponentialUpperBoundSeq scale RB) :
    ∃ R : ℕ → ℝ, (∀ n, 0 ≤ R n) ∧ HasSubexponentialUpperBoundSeq scale R ∧
      ∀ n (d b e : D),
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD d)‖ ≤ RH n →
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD b)‖ ≤ RB n →
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD e)‖ ≤ RH n →
        ‖(finBasis ℝ H).equivFun (cartanLog H eD ExpD hbijD (d * b * e⁻¹))‖ ≤ R n := by
  obtain ⟨R₁, hR₁0, hR₁, hprod₁⟩ := exists_sequence_cartan_product_bound H eD ExpD hbijD
    hExpD dynkinD scale RH RB hs hRH0 hRB0 hRH hRB
  obtain ⟨R₂, hR₂0, hR₂, hprod₂⟩ := exists_sequence_cartan_product_bound H eD ExpD hbijD
    hExpD dynkinD scale R₁ RH hs hR₁0 hRH0 hR₁ hRH
  refine ⟨R₂, hR₂0, hR₂, ?_⟩
  intro n d b e hd hb he
  apply hprod₂ n (d * b) e⁻¹ (hprod₁ n d b hd hb)
  simpa only [cartanLog_inv H eD ExpD hbijD hExpD, map_neg, norm_neg] using he

end PolycyclicRecognition

end

end OAI
