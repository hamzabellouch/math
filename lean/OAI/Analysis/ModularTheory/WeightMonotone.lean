import OAI.Analysis.ModularTheory.WeightCutoffs
import OAI.Analysis.OperatorAlgebra.ScalarLpIntervalCommutant
import OAI.Analysis.Nuclearity.CommutingCompressionOrder
import OAI.Analysis.WeakInfiniteness.CPSchwarz

namespace OAI

/-! Monotonicity of the actual finite cutoff functionals on the positive
modular core. The proof uses interval-projection commutation, not an assumed
trace or a commutation rule for arbitrary operators on scalar L². -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

lemma modularWeightCutoffVector_project (n m : ℕ) (hnm : n ≤ m) :
    scalarIntervalProjection n (modularWeightCutoffVector m) =
      modularWeightCutoffVector n := by
  apply Lp.ext
  filter_upwards [scalarIntervalProjection_ae n (modularWeightCutoffVector m),
    modularWeightCutoffVector_ae m, modularWeightCutoffVector_ae n] with t hp hm hn
  rw [hp, hn]
  by_cases ht : t ∈ Icc (-(n : ℝ)) n
  · have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have ht' : t ∈ Icc (-(m : ℝ)) m :=
      ⟨(neg_le_neg hnm').trans ht.1, ht.2.trans hnm'⟩
    simp only [Set.indicator_of_mem ht, hm, modularWeightCutoffFunction,
      Set.indicator_of_mem ht']
  · simp only [Set.indicator_of_notMem ht, modularWeightCutoffFunction]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

theorem modularCoreCutoffFunctional_mono (n m : ℕ) (hnm : n ≤ m)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hcore : T ∈ modularCrossedProduct (volume : Measure ℝ) S) (hT : 0 ≤ T) :
    modularCoreCutoffFunctional S n T ≤ modularCoreCutoffFunctional S m T := by
  let X := modularFourierCompression S T
  let P := scalarIntervalProjection n
  let ξ := modularWeightCutoffVector m
  have hX : 0 ≤ X := completelyPositive_map_nonneg (modularFourierCompression_cp S) hT
  have hP : IsStarProjection P := scalarIntervalProjection_isStarProjection n
  have hc : Commute X P := scalarLp_commute_intervalProjection X
    (modularFourierCompression_commutes S T hcore) n
  have hle : P * X * P ≤ X := commuting_projection_compression_le P X hP hX hc.symm
  have hi := (ContinuousLinearMap.nonneg_iff_isPositive.mp
    (sub_nonneg.mpr hle)).inner_nonneg_right ξ
  have hbound : inner ℂ ξ ((P * X * P) ξ) ≤ inner ℂ ξ (X ξ) := by
    simpa only [sub_apply, inner_sub_right, sub_nonneg] using hi
  rw [modularCoreCutoffFunctional_compression, modularCoreCutoffFunctional_compression]
  change inner ℂ (modularWeightCutoffVector n) (X (modularWeightCutoffVector n)) ≤
    inner ℂ ξ (X ξ)
  rw [← modularWeightCutoffVector_project n m hnm]
  calc
    inner ℂ (P ξ) (X (P ξ)) = inner ℂ ξ ((P * X * P) ξ) := by
      calc
        _ = inner ℂ ξ ((star P) (X (P ξ))) :=
          (ContinuousLinearMap.adjoint_inner_right P ξ (X (P ξ))).symm
        _ = _ := by rw [hP.isSelfAdjoint.star_eq]; rfl
    _ ≤ inner ℂ ξ (X ξ) := hbound

end WeakPureInfiniteness

end

end OAI
