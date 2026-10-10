import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleRetainedStats
import OAI.Probability.SKBarriers.Hierarchy.WeightedMarkedIntegral
import OAI.Probability.SKBarriers.Scalar.ScalarTentMixed

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem weightedBranch_average (w : List (ℝ × (ℝ × ℝ))) (f g : ℝ → ℝ) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => g p.1)=
      fun p => scalarIncrementAverage (weightedUnderlying w) f g p.1 := by
  have H := vectorIncrementAverage_pullback (ContinuousLinearMap.fst ℝ ℝ ℝ) w f g
  rw [vectorIncrementAverage_real] at H
  exact H

theorem weightedList_integral (w : List (ℝ × (ℝ × ℝ))) {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {g : ℝ × ℝ → ℝ} (hg : Continuous g) (hE : HasExpGrowth g) (x : ℝ) :
    vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) g (x,0)=
      ∫ z,g (scalarSpinField w.length (fun i => (w.get i).2.1) z,
        coordinateLinear w.length (fun i => (w.get i).2.2) z)
        ∂hierarchyPathLaw w.length (fun i => (w.get i).1)
          (f ∘ scalarSpinField w.length (fun i => (w.get i).2.1)) x := by
  rw [vectorIncrementAverage_get]
  exact scalarWeightedTest_integral _ _ _ _ hf hg hE x

theorem weightedList_tent_square_error (w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈w,p.1∈Icc (0:ℝ) 1) (hs : w.Pairwise (fun p q => p.1 ≤ q.1))
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (l r s : Fin (w.length+1)) (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0<h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance w.length (fun i => (w.get i).2.1) r-
      scalarPrefixVariance w.length (fun i => (w.get i).2.1) l=B*h)
    (hright : scalarPrefixVariance w.length (fun i => (w.get i).2.1) s-
      scalarPrefixVariance w.length (fun i => (w.get i).2.1) r=B*h)
    (ha : (fun i => (w.get i).2.2)=scalarTentVector w.length (fun i => (w.get i).2.1) l r s h)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y,|g y| ≤ 1) (x : ℝ) :
    |vectorIncrementAverage w (fun p : ℝ × ℝ => f p.1) (fun p => p.2^2*g p.1) (x,0)-
      weightedVariance w*scalarIncrementAverage (weightedUnderlying w) f g x| ≤
      (B*scalarTentAtomMass w.length (fun i => (w.get i).1) l s)^2+
        B^2*scalarTentAtomMass w.length (fun i => (w.get i).1) l s := by
  have hG : HasExpGrowth g := HasExpGrowth.of_bounded zero_le_one (fun y => by
    simpa only [Real.norm_eq_abs] using hb y)
  have H := scalarPath_tent_square_error w.length (fun i => (w.get i).1) (fun i => (w.get i).2.1)
    (fun i => hm _ (List.get_mem w i)) (mass_get_monotone hs) hf hspin l r s hlr hrs hh hB hleft hright hg hb x
  rw [← ha,sum_get_map w (fun p => p.2.2^2)] at H
  have hg1 : Continuous (fun p : ℝ × ℝ => p.2^2*g p.1) := (continuous_snd.pow 2).mul (hg.continuous.comp continuous_fst)
  have he1 : HasExpGrowth (fun p : ℝ × ℝ => p.2^2*g p.1) :=
    ((HasExpGrowth.linear (ContinuousLinearMap.snd ℝ ℝ ℝ)).pow 2).mul
      (hG.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ))
  have HI := weightedList_integral w hf hg1 he1 x
  dsimp only [Function.comp_def] at HI
  rw [← HI] at H
  have He := weightedList_integral w hf (hg.continuous.comp continuous_fst)
    (hG.compCLM (ContinuousLinearMap.fst ℝ ℝ ℝ)) x
  dsimp only [Function.comp_def] at He
  rw [weightedBranch_average] at He
  rw [← He] at H
  exact H

theorem weightedSplit_tent_mixed_error (c w : List (ℝ × (ℝ × ℝ)))
    (hm : ∀ p∈c++w,p.1∈Icc (0:ℝ) 1) (hs : (c++w).Pairwise (fun p q => p.1 ≤ q.1))
    {f F : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (hF : BoundedDerivs F) (hFs : ScalarSpinConvex F)
    (l s : Fin ((c++w).length+1))
    (hlr : l ≤ ⟨c.length,by simp only [List.length_append]; omega⟩)
    (hrs : (⟨c.length,by simp only [List.length_append]; omega⟩ : Fin ((c++w).length+1)) ≤ s)
    {h B : ℝ} (hh : 0<h) (hB : 0 ≤ B)
    (hleft : scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1)
      ⟨c.length,by simp only [List.length_append]; omega⟩-
      scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1) l=B*h)
    (hright : scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1) s-
      scalarPrefixVariance (c++w).length (fun i => ((c++w).get i).2.1)
        ⟨c.length,by simp only [List.length_append]; omega⟩=B*h)
    (ha : (fun i => ((c++w).get i).2.2)=scalarTentVector (c++w).length
      (fun i => ((c++w).get i).2.1) l ⟨c.length,by simp only [List.length_append]; omega⟩ s h)
    {g : ℝ → ℝ} {M : ℝ≥0} (hg : LipschitzWith M g) (hb : ∀ y,|g y| ≤ 1) (x : ℝ) :
    |vectorIncrementAverage c (fun p => scalarIncrementChain (weightedUnderlying w) f p.1)
        (fun p => vectorIncrementAverage w (fun p => f p.1) (fun p => g p.1*p.2) p*rootGradient 0 F p.1) (x,0)-
      B*vectorIncrementAverage c (fun p => scalarIncrementChain (weightedUnderlying w) f p.1)
        (fun p => vectorIncrementAverage w (fun p => f p.1) (fun p => g p.1) p*rootHessian 0 F p.1) (x,0)| ≤
      B*scalarTentAtomMass (c++w).length (fun i => ((c++w).get i).1) l s := by
  have H := scalarPath_tent_mixed_error (c++w).length (fun i => ((c++w).get i).1) (fun i => ((c++w).get i).2.1)
    (fun i => hm _ (List.get_mem _ i)) (mass_get_monotone hs) hf hspin hF hFs l
    ⟨c.length,by simp only [List.length_append]; omega⟩ s hlr hrs hh hB hleft hright hg hb x
  rw [← ha] at H
  have hG : HasExpGrowth g := HasExpGrowth.of_bounded zero_le_one (fun y => by simpa only [Real.norm_eq_abs] using hb y)
  have hU : HasExpGrowth (rootGradient 0 F) := HasExpGrowth.of_bounded zero_le_one
    (fun y => by simpa only [Real.norm_eq_abs] using (hFs.bounds y).1)
  have hC : HasExpGrowth (rootHessian 0 F) := HasExpGrowth.of_bounded zero_le_one
    (fun y => by simpa only [Real.norm_eq_abs] using (hFs.bounds y).2)
  let L : MarkedWeightedState →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let Y : MarkedWeightedState →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let R : MarkedWeightedState →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ
  have HI := weightedSplit_integral c w hf (fun p => g p.1*p.2) (rootGradient 0 F)
    (((hg.continuous.comp L.continuous).mul Y.continuous).mul ((rootGradient_continuous 0 hF).comp R.continuous))
    (((hG.compCLM L).mul (HasExpGrowth.linear Y)).mul (hU.compCLM R)) x
  have HJ := weightedSplit_integral c w hf (fun p => g p.1) (rootHessian 0 F)
    ((hg.continuous.comp L.continuous).mul ((rootHessian_continuous 0 hF).comp R.continuous))
    ((hG.compCLM L).mul (hC.compCLM R)) x
  rw [HI,HJ]
  convert H using 1
  apply congrArg abs
  apply congrArg₂ (fun a b : ℝ => a-B*b)
  · apply integral_congr_ae
    filter_upwards [] with z
    ring
  · apply integral_congr_ae
    filter_upwards [] with z
    ring

end SK.Analytic

end
end

end OAI
