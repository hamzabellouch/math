import OAI.Analysis.BoundedHochschild.CompletelyPositiveCompression
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! Bounded pointwise weak-operator ultralimits of completely positive maps. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A H ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_completelyPositive_ultralimit (ω : Ultrafilter ι)
    (φ : ι → CompletelyPositiveMap A (H →L[ℂ] H)) {C : ℝ} (hC : 0 ≤ C)
    (hφ : ∀ i a, ‖φ i a‖ ≤ C * ‖a‖) :
    ∃ Φ : CompletelyPositiveMap A (H →L[ℂ] H),
      (∀ a, ‖Φ a‖ ≤ C * ‖a‖) ∧ ∀ a ξ η,
        Tendsto (fun i => inner ℂ η (φ i a ξ)) (ω : Filter ι)
          (𝓝 (inner ℂ η (Φ a ξ))) := by
  have hex (a : A) := Generator.Tracial.exists_weak_operator_ultralimit ω
    (fun i => φ i a) (C * ‖a‖) (mul_nonneg hC (norm_nonneg a)) (fun i => hφ i a)
  choose T hT ht using hex
  have hadd (a b : A) : T (a + b) = T a + T b := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (a + b) ξ η)
    simpa only [map_add, add_apply, inner_add_right] using (ht a ξ η).add (ht b ξ η)
  have hsmul (z : ℂ) (a : A) : T (z • a) = z • T a := by
    apply ContinuousLinearMap.ext
    intro ξ
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (z • a) ξ η)
    simpa only [map_smul, smul_apply, inner_smul_right, smul_eq_mul] using
      (ht a ξ η).const_mul z
  let L : A →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := T, map_add' := hadd, map_smul' := hsmul }
  have hpos (n : ℕ) (B : CStarMatrix (Fin n) (Fin n) A) (hB : 0 ≤ B) :
      0 ≤ B.map L := by
    apply operatorMatrix_nonneg_of_quadratic
    intro ξ
    have hl : Tendsto (fun i => ∑ j, ∑ k, inner ℂ (ξ j) (φ i (B j k) (ξ k)))
        (ω : Filter ι) (𝓝 (∑ j, ∑ k, inner ℂ (ξ j) (T (B j k) (ξ k)))) := by
      apply tendsto_finsetSum
      intro j _
      apply tendsto_finsetSum
      intro k _
      exact ht (B j k) (ξ k) (ξ j)
    change 0 ≤ ∑ j, ∑ k, inner ℂ (ξ j) (T (B j k) (ξ k))
    exact ge_of_tendsto hl (Eventually.of_forall fun i =>
      operatorMatrix_quadratic_nonneg (B.map (φ i)) ((φ i).map_cstarMatrix_nonneg B hB) ξ)
  exact ⟨{ L with map_cstarMatrix_nonneg' := hpos }, hT, ht⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
