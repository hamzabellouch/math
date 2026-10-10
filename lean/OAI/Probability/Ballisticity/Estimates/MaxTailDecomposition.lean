import Mathlib
import OAI.Probability.Ballisticity.Estimates.SmallScaleGaussianMass

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma partialSumMax_add_le (X Y : ℕ → ℝ) (n : ℕ) :
    partialSumMax (fun k => X k+Y k) n ≤ partialSumMax X n+partialSumMax Y n := by
  induction n with
  | zero => simp [partialSumMax]
  | succ n ih =>
    apply max_le
    · exact ih.trans (add_le_add (partialSumMax_mono X (Nat.le_succ n)) (partialSumMax_mono Y (Nat.le_succ n)))
    · rw [show realPartialSum (fun k => X k+Y k) (n+1) = realPartialSum X (n+1)+realPartialSum Y (n+1) from by simp [realPartialSum,Finset.sum_add_distrib]]
      exact (abs_add_le _ _).trans (add_le_add (abs_partialSum_le_max X _) (abs_partialSum_le_max Y _))

lemma square_tail_le_fourth_add {M U V a : ℝ} (hM0 : 0 ≤ M) (hU0 : 0 ≤ U) (hV0 : 0 ≤ V)
    (ha : 0 < a) (hM : M ≤ U+V) :
    (if a < M then M^2 else 0) ≤ (16/a^2)*U^4+4*V^2 := by
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hnon : 0 ≤ (16/a^2)*U^4 := mul_nonneg (by positivity) (pow_nonneg hU0 _)
  by_cases ham : a < M
  · rw [ite_eq_left ham]
    by_cases hau : a/2 < U
    · have hs : a^2 ≤ 4*U^2 := by nlinarith
      have hp := mul_le_mul_of_nonneg_right hs (sq_nonneg U)
      have hu : 4*U^2 ≤ (16/a^2)*U^4 := by
        rw [show (16/a^2)*U^4 = (16*U^4)/a^2 by ring]
        apply (le_div_iff₀ ha2).mpr
        nlinarith [hp]
      have hm2 : M^2 ≤ 2*U^2+2*V^2 := by nlinarith [sq_nonneg (U-V),pow_le_pow_left₀ hM0 hM 2]
      nlinarith [sq_nonneg U,sq_nonneg V]
    · have hUV : U ≤ V := by linarith [le_of_not_gt hau]
      have hm2 : M^2 ≤ 4*V^2 := by nlinarith [pow_le_pow_left₀ hM0 hM 2,sq_nonneg (V-U)]
      linarith
  · rw [ite_eq_right ham]
    exact add_nonneg hnon (mul_nonneg (by norm_num) (pow_nonneg hV0 2))

lemma capped_max_tail_decomposition (X : ℕ → ℝ) (n : ℕ) {z R a : ℝ}
    (hz : 0 ≤ z) (hzR : z ≤ R) (ha : 0 < a) :
    (if a < partialSumMax X n then min ((partialSumMax X n)^2) (R^2) else 0) ≤
      (16/a^2)*(partialSumMax (fun k => symmetricTruncate z (X k)) n)^4+
      4*(partialSumMax (fun k => bandTruncate z R (X k)) n)^2+
      ∑ k ∈ Finset.range n, truncatedTailCost R (X k) := by
  have hcost0 : 0 ≤ ∑ k ∈ Finset.range n, truncatedTailCost R (X k) :=
    Finset.sum_nonneg (fun k _ => truncatedTailCost_nonneg _ _)
  have hfirst0 : 0 ≤ (16/a^2)*(partialSumMax (fun k => symmetricTruncate z (X k)) n)^4 := by positivity
  have hsecond0 : 0 ≤ 4*(partialSumMax (fun k => bandTruncate z R (X k)) n)^2 := by positivity
  by_cases hbig : ∃ k < n, R < |X k|
  · obtain ⟨k,hkn,hk⟩ := hbig
    have hcost : R^2 ≤ ∑ j ∈ Finset.range n, truncatedTailCost R (X j) := by
      have hh := Finset.single_le_sum (f := fun j => truncatedTailCost R (X j))
        (fun j _ => truncatedTailCost_nonneg _ _) (Finset.mem_range.mpr hkn)
      simpa only [truncatedTailCost,ite_eq_left hk] using hh
    split_ifs
    · exact (min_le_right _ _).trans (by linarith)
    · exact (pow_nonneg (hz.trans hzR) 2).trans
        (hcost.trans (le_add_of_nonneg_left (add_nonneg hfirst0 hsecond0)))
  · have hc (k) (hk : k < n) : X k = symmetricTruncate z (X k)+bandTruncate z R (X k) := by
      have hR : |X k| ≤ R := le_of_not_gt (fun hh => hbig ⟨k,hk,hh⟩)
      simp only [bandTruncate,symmetricTruncate,ite_eq_left hR]
      ring
    have heq := partialSumMax_congr n hc
    have hM : partialSumMax X n ≤ partialSumMax (fun k => symmetricTruncate z (X k)) n+
        partialSumMax (fun k => bandTruncate z R (X k)) n := by
      rw [heq]
      exact partialSumMax_add_le _ _ n
    have hh := square_tail_le_fourth_add (partialSumMax_nonneg X n)
      (partialSumMax_nonneg _ _) (partialSumMax_nonneg _ _) ha hM
    have hcap : (if a < partialSumMax X n then min ((partialSumMax X n)^2) (R^2) else 0) ≤
        (if a < partialSumMax X n then (partialSumMax X n)^2 else 0) := by
      split_ifs <;> first | exact min_le_left _ _ | rfl
    exact hcap.trans (hh.trans (le_add_of_nonneg_right hcost0))

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma integrable_truncatedTailCost_comp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (S : Ω → ℝ) (hS : Measurable S) (R : ℝ) :
    Integrable (fun x => truncatedTailCost R (S x)) μ := by
  apply integrable_of_abs_bound μ _ ((measurable_truncatedTailCost R).comp hS) (R^2)
  intro x
  change |truncatedTailCost R (S x)| ≤ R^2
  unfold truncatedTailCost
  split_ifs <;> simp [abs_of_nonneg (sq_nonneg R),sq_nonneg R]

lemma integral_iid_max_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hind : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hsym : IdentDistrib (X 0) (fun ω => -X 0 ω) μ μ)
    {z R a : ℝ} (hz : 0 ≤ z) (hzR : z ≤ R) (ha : 0 < a) (n : ℕ) :
    (∫ ω, (if a < partialSumMax (fun k => X k ω) n then
        min ((partialSumMax (fun k => X k ω) n)^2) (R^2) else 0) ∂μ) ≤
      (16/a^2)*(32*(n:ℝ)*z^2*truncatedVariance μ (X 0) z+
        96*(n:ℝ)^2*(truncatedVariance μ (X 0) z)^2)+
      16*(n:ℝ)*(truncatedVariance μ (X 0) R-truncatedVariance μ (X 0) z+
        z^2*μ.real {ω | z < |X 0 ω|}) := by
  let Y := fun k ω => symmetricTruncate z (X k ω)
  let B := fun k ω => bandTruncate z R (X k ω)
  have hY (k) : Measurable (Y k) := (measurable_symmetricTruncate z).comp (hX k)
  have hB (k) : Measurable (B k) := (measurable_bandTruncate z R).comp (hX k)
  have hBb (k) (ω) : |B k ω| ≤ R := bandTruncate_bound hz hzR _
  have hYi : Integrable (fun ω => (partialSumMax (fun k => Y k ω) n)^4) μ :=
    integrable_partialSumMax_pow μ Y hY hz (fun k ω => symmetricTruncate_bound hz _) n 4
  have hBi : Integrable (fun ω => (partialSumMax (fun k => B k ω) n)^2) μ :=
    integrable_partialSumMax_pow μ B hB (hz.trans hzR) hBb n 2
  have hTi (k) := integrable_truncatedTailCost_comp μ (X k) (hX k) R
  have hM : Measurable (fun ω => partialSumMax (fun k => X k ω) n) := measurable_partialSumMax X hX n
  have hLeft : Integrable (fun ω => if a < partialSumMax (fun k => X k ω) n then
      min ((partialSumMax (fun k => X k ω) n)^2) (R^2) else 0) μ := by
    apply integrable_of_abs_bound μ _ (Measurable.ite (measurableSet_lt measurable_const hM)
      ((hM.pow_const 2).min measurable_const) measurable_const) (R^2)
    intro ω
    split_ifs
    · rw [abs_of_nonneg (le_min (sq_nonneg _) (sq_nonneg R))]
      exact min_le_right _ _
    · simpa using sq_nonneg R
  have hDom := integral_mono hLeft (((hYi.const_mul (16/a^2)).add (hBi.const_mul 4)).add
    (integrable_finsetSum (Finset.range n) (fun k _ => hTi k)))
    (fun ω => capped_max_tail_decomposition (fun k => X k ω) n hz hzR ha)
  have hAdd₁ := integral_add ((hYi.const_mul (16/a^2)).add (hBi.const_mul 4))
    (integrable_finsetSum (Finset.range n) (fun k _ => hTi k))
  have hAdd₂ := integral_add (hYi.const_mul (16/a^2)) (hBi.const_mul 4)
  simp only [Pi.add_apply] at hDom hAdd₁ hAdd₂
  rw [hAdd₁,hAdd₂,integral_const_mul,integral_const_mul,
    integral_finsetSum _ (fun k _ => hTi k)] at hDom
  have hYbound := integral_iid_truncated_max_fourth_le μ X hX hind hident hsym hz le_rfl n
  have hBind : iIndepFun B μ := hind.comp (fun _ => bandTruncate z R) (fun _ => measurable_bandTruncate z R)
  have hBid (k) : IdentDistrib (B k) (B 0) μ μ := (hident k).comp (measurable_bandTruncate z R)
  have hBm0 : ∫ ω, B 0 ω ∂μ = 0 := integral_bandTruncate_zero μ (X 0) z R hsym
  have hBmean (k) : ∫ ω, B k ω ∂μ = 0 := (hBid k).integral_eq.trans hBm0
  have hBbound := integral_partialSumMax_square_le_sum μ B hB hBind hBmean (hz.trans hzR) hBb n
  have hBeq (k) : (∫ ω, (B k ω)^2 ∂μ) = ∫ ω, (B 0 ω)^2 ∂μ :=
    ((hBid k).comp (measurable_id.pow_const 2)).integral_eq
  simp only [hBeq,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hBbound
  have hTeq (k) : (∫ ω, truncatedTailCost R (X k ω) ∂μ) = R^2*μ.real {ω | R < |X 0 ω|} :=
    ((hident k).comp (measurable_truncatedTailCost R)).integral_eq.trans (integral_truncatedTailCost μ (X 0) (hX 0) R)
  simp only [hTeq,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hDom
  have heq := integral_bandTruncate_cost μ (X 0) (hX 0) hz hzR
  have htail0 : 0 ≤ R^2*μ.real {ω | R < |X 0 ω|} := mul_nonneg (sq_nonneg _) (measureReal_nonneg)
  have hproduct := mul_le_mul_of_nonneg_left hYbound (show 0 ≤ 16/a^2 by positivity)
  change (∫ ω, (B 0 ω)^2 ∂μ)+R^2*μ.real {ω | R < |X 0 ω|} = _ at heq
  rw [← heq]
  nlinarith [mul_nonneg (show 0 ≤ (n:ℝ) by positivity) htail0]

end DirectionalTransience

end

end

end OAI
