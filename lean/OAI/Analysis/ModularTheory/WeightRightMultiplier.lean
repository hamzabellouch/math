import OAI.Analysis.ModularTheory.WeightClosed
import OAI.Analysis.ModularTheory.TranslationWeight

namespace OAI

/-! Right multiplication by a contractive translation multiplier decreases
the core square weight. This follows from the proved scalar-compression
commutation, independently of traciality. -/

noncomputable section
open MeasureTheory
open scoped ComplexOrder ENNReal

namespace WeakPureInfiniteness

lemma commuting_contraction_compression_le {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (q a : A)
    (ha : 0 ≤ a) (hqa : Commute q a) (hq : ‖q‖ ≤ 1) :
    star q * a * q ≤ a := by
  have hs : IsSelfAdjoint a := IsSelfAdjoint.of_nonneg ha
  have hsq : Commute a (star q) := by
    simpa only [hs.star_eq] using hqa.star_star.symm
  have hqq : star q * q ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg q)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg q]
  have hc : Commute a (1 - star q * q) :=
    (Commute.one_right a).sub_right (hsq.mul_right hqa.symm)
  have hp := hc.mul_nonneg ha (sub_nonneg.mpr hqq)
  apply sub_nonneg.mp
  have he : a - star q * a * q = a * (1 - star q * q) := by
    rw [mul_sub, mul_one, ← mul_assoc, hsq.eq]
  rw [he]
  exact hp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : BoundedRecovery.StandardModularData H)

lemma modularCoreSquareWeight_rightMultiplier
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ))
    (hT : T ∈ modularCrossedProduct (volume : Measure ℝ) S)
    (g : BoundedContinuousFunction ℝ ℂ) (hg : ‖g‖ ≤ 1) :
    modularCoreSquareWeight S (T * modularTranslationCalculus g) ≤
      modularCoreSquareWeight S T := by
  let X := modularFourierCompression S (star T * T)
  let Q := scalarLpRepresentation volume g
  have hX : 0 ≤ X :=
    completelyPositive_map_nonneg (modularFourierCompression_cp S) (star_mul_self_nonneg T)
  have hQX : Commute Q X := (scalarLp_commute_continuousMultiplier X
    (modularFourierCompression_commutes S _ (mul_mem (star_mem hT) hT)) g).symm
  have hQ : ‖Q‖ ≤ 1 :=
    (NonUnitalStarAlgHom.norm_apply_le (scalarLpRepresentation volume) g).trans hg
  have hle := commuting_contraction_compression_le Q X hX hQX hQ
  apply iSup_le
  intro n
  apply le_trans _ (le_iSup (fun n => ENNReal.ofReal (‖T (modularCoreWeightVector S n)‖ ^ 2)) n)
  apply ENNReal.ofReal_le_ofReal
  let ξ := modularWeightCutoffVector n
  have hi : inner ℂ ξ ((star Q * X * Q) ξ) ≤ inner ℂ ξ (X ξ) := by
    have hp := (ContinuousLinearMap.nonneg_iff_isPositive.mp
      (sub_nonneg.mpr hle)).inner_nonneg_right ξ
    simpa only [sub_apply, inner_sub_right, sub_nonneg] using hp
  have he : inner ℂ ξ ((star Q * X * Q) ξ) = inner ℂ (Q ξ) (X (Q ξ)) := by
    change inner ℂ ξ (Q.adjoint (X (Q ξ))) = _
    exact ContinuousLinearMap.adjoint_inner_right _ _ _
  rw [he] at hi
  have hreal := (Complex.le_def.mp hi).1
  change (inner ℂ (Q ξ) (modularFourierCompression S (star T * T) (Q ξ))).re ≤
    (inner ℂ ξ (modularFourierCompression S (star T * T) ξ)).re at hreal
  rw [← modularFourierCompression_square_inner, ← modularFourierCompression_square_inner,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hreal
  norm_cast at hreal
  change ‖T (modularTranslationCalculus g
    (modularFourierInclusion S (modularWeightCutoffVector n)))‖ ^ 2 ≤ _
  rw [modularTranslationCalculus_fourierInclusion]
  exact hreal

end WeakPureInfiniteness

end

end OAI
