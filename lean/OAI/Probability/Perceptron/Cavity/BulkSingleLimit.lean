import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkLimitGeometry
import OAI.Probability.Perceptron.Variational.QuantileSingleReference

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma bulk_single_ratio_tendsto_of_reference (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (w w' : ℝ→ᵇℝ)
    (η : ProbabilityMeasure (WeightedRestorationRange g.f (singleRestorationBound g.f w w')))
    (hm : ∀ j,(∫ x,x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w w'))))=
      ∫ Q : CompactArray CompactOverlap,scalarRestorationSingleMoment g.f w w' j
        (fun i l => (Q i l).val) ∂(ν : Measure _)) :
    Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
      1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w')) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*restorationReciprocal g.f 1 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w w'))))) := by
  let Ψ : EuclideanSpace ℝ (Fin 1) →ᵇ ℝ := gaussianMixedTest (fun _ => w)
  let Φ : EuclideanSpace ℝ (Fin 1) →ᵇ ℝ := gaussianMixedTest (fun _ => w')
  let C := ‖(1 : CompactBlock CompactOverlap 1 →ᵇ ℝ)‖*‖restorationMarkTest 1 g.f Ψ 0‖*‖restorationMarkTest 1 g.f Φ 0‖+
    singleRestorationBound g.f w w'
  have hC : 0≤C := add_nonneg (by positivity) (singleRestorationBound_nonneg _ _ _)
  have hηB (x : WeightedRestorationRange g.f (singleRestorationBound g.f w w')) : |x.1.val|≤C :=
    (abs_le.mpr x.1.prop).trans (le_add_of_nonneg_left (by positivity))
  have hb (n : ℕ) (p : TwoFreshDisorder (s n+1) (M (s n))) :
      |bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n)) 1 Ψ Φ p|≤C :=
    (bulkFreshNumerator_bound _ _ _ _ _ _ _ _ _).trans
      (le_add_of_nonneg_right (singleRestorationBound_nonneg _ _ _))
  have hmoment j : Tendsto (fun n => ∫ p,
      bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n)) 1 Ψ Φ p *
      (bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n)) p).val^j
      ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w w'))))) := by
    rw [hm j]
    simp_rw [scalarRestorationSingleMoment_compact]
    exact bulkFresh_moment_tendsto M g.f v s hlim 1 1 Ψ Φ j
  have ht := restoration_ratio_tendsto
    (fun n => twoFreshDisorderLaw (s n+1) (M (s n)))
    (η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w w')))
    (Real.exp_pos _)
    (fun n => bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n)) 1 Ψ Φ)
    (fun x => x.1.val)
    (fun n => bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n))) (fun x => x.2)
    (fun n => bulkFreshNumerator_measurable _ _ _ _ _ _ _ _) (by fun_prop)
    (fun n => bulkFreshCompactDenominator_measurable _ _ _ _) (by fun_prop)
    hC hb hηB hmoment 1
  simpa only [div_eq_mul_inv, restorationReciprocal, ContinuousMap.coe_mk, bulkFreshCompactDenominator, Ψ, Φ] using ht

theorem bulk_single_limit_exists (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ c : ℝ, |c|≤‖w‖ ∧ ∀ b : Bool,
    Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 1 g.f (v (s n))
      1 (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>secondPairMark w b)) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^1
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop (𝓝 (c^(pairMarkPower b))) := by
  let q := boundedQuantile ((compactPositivePairLaw (bulkJointLaw ν)).map Prod.fst)
  have hq : Monotone q := boundedQuantile_monotone _
  obtain ⟨c,hc,href⟩ := quantile_single_reference_exists q hq g w
  refine ⟨c,hc,fun b => ?_⟩
  obtain ⟨ρ,η,hG,hge,hp,hm,hl⟩ := href b
  have hpair := (compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn).trans hp.symm
  have he (j : ℕ) : (∫ x,x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (singleRestorationBound g.f w (secondPairMark w b)))))=
      ∫ Q : CompactArray CompactOverlap,scalarRestorationSingleMoment g.f w (secondPairMark w b) j
        (fun i l => (Q i l).val) ∂(ν : Measure _) := by
    rw [hm j,←scalarGram_eq_of_pair_law (bulkJointLaw ν) ρ hGG hG hgeo hge hpair]
    exact bulkJointLaw_scalarGram_integral ν _ _
  have ht := bulk_single_ratio_tendsto_of_reference M g v s hlim w (secondPairMark w b) η he
  rwa [hl] at ht

def singleFieldMark (w : ℝ→ᵇℝ) (z : Fin 1→ℝ) : ℝ := w (z 0)
lemma singleFieldMark_measurable (w : ℝ→ᵇℝ) : Measurable (singleFieldMark w) := by
  unfold singleFieldMark; fun_prop
lemma singleFieldMark_bound (w : ℝ→ᵇℝ) (z : Fin 1→ℝ) : |singleFieldMark w z|≤‖w‖ := w.norm_coe_le_norm _

def bulkSingleAverage (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 1→NormalizedSpin (n+1)) : ℝ :=
  ((n+1:ℕ):ℝ)⁻¹*∑ i,singleFieldMark w (bulkPatternFields i a x)

lemma bulkSingleAverage_measurable (n M : ℕ) (w : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (bulkSingleAverage n M w)) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun i _ => (singleFieldMark_measurable w).comp (bulkPatternFields_measurable _ _ _ _)

lemma bulkSingleAverage_bound (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 1→NormalizedSpin (n+1)) : |bulkSingleAverage n M w a x|≤M/(n+1:ℕ)*‖w‖ := by
  unfold bulkSingleAverage
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(((n+1:ℕ):ℝ)⁻¹))]
  have h : |∑ i : Fin M,singleFieldMark w (bulkPatternFields i a x)|≤M*‖w‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => singleFieldMark_bound w _).trans_eq (by simp))
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

lemma bulk_marked_last_single (n M : ℕ) (f w w' : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    bulkReplicaMean n (M+2) f v 1 (fun a x =>
      singleFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x)*
      singleFieldMark w' (bulkPatternFields (Fin.last (M+1)) a x))=
    ∫ p,bulkFreshNumerator n M 1 f v 1
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w')) p /
      bulkFreshDenominator n M f v p^1 ∂twoFreshDisorderLaw (n+1) M := by
  rw [←bulkFresh_annealed_restoration]
  unfold bulkReplicaMean
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    apply congrArg (gibbsReplicaMean _ _ 1)
    funext x
    simp only [BoundedContinuousFunction.coe_one,Pi.one_apply,bulkMarkedTest,one_mul,gaussianMixedTest_apply,Fin.prod_univ_one,
      singleFieldMark]
    rfl

lemma bulkSingleAverage_first (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    bulkReplicaMean n (M+2) f v 1 (bulkSingleAverage n (M+2) w)=
    ((M+2:ℕ):ℝ)/(n+1:ℕ)*(∫ p,bulkFreshNumerator n M 1 f v 1
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>(1:ℝ→ᵇℝ))) p /
      bulkFreshDenominator n M f v p^1 ∂twoFreshDisorderLaw (n+1) M) := by
  unfold bulkSingleAverage
  rw [bulkReplicaMean_const_mul]
  have h := bulk_pattern_sum_first n (M+2) 1 f v (fun _=>1) measurable_const
    _ (singleFieldMark_measurable w) (by norm_num : (0:ℝ)≤1) (norm_nonneg w)
    (fun _=>by norm_num) (singleFieldMark_bound w) ((Fin.last M).castSucc)
  simp only [one_mul] at h
  rw [h,←bulk_marked_last_single n M f w 1 v]
  simp only [singleFieldMark,BoundedContinuousFunction.coe_one,Pi.one_apply,mul_one]
  ring

lemma bulkSingleAverage_second (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    bulkReplicaMean n (M+2) f v 1 (fun a x => (bulkSingleAverage n (M+2) w a x)^2)=
    ((M+2:ℕ):ℝ)/(n+1:ℕ)^2*
      bulkReplicaMean n (M+2) f v 1 (fun a x =>
        (singleFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x))^2)+
    (((M+2:ℕ):ℝ)*((M+1:ℕ):ℝ)/(n+1:ℕ)^2)*(∫ p,bulkFreshNumerator n M 1 f v 1
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w)) p /
      bulkFreshDenominator n M f v p^1 ∂twoFreshDisorderLaw (n+1) M) := by
  have hf : (fun a x => (bulkSingleAverage n (M+2) w a x)^2)=
      (fun a x => (((n+1:ℕ):ℝ)⁻¹)^2*((∑ i,singleFieldMark w (bulkPatternFields i a x))^2)) := by
    funext a x; unfold bulkSingleAverage; ring
  have hkl : (Fin.last M).castSucc≠Fin.last (M+1) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at this
    omega
  rw [hf,bulkReplicaMean_const_mul]
  have h := bulk_pattern_sum_second n (M+2) 1 f v (fun _=>1) measurable_const
    _ (singleFieldMark_measurable w) (by norm_num : (0:ℝ)≤1) (norm_nonneg w)
    (fun _=>by norm_num) (singleFieldMark_bound w) _ _ hkl
  simp only [one_mul] at h
  rw [h,bulk_marked_last_single]
  simp only [div_eq_mul_inv,inv_pow]
  push_cast
  ring

lemma bulkSingleAverage_diagonal_bound (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) :
    |bulkReplicaMean n (M+2) f v 1 (fun a x =>
        (singleFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x))^2)|≤‖w‖^2 := by
  apply bulkReplicaMean_bound _ _ _ _ _ _
    (((singleFieldMark_measurable w).comp (bulkPatternFields_measurable _ _ _ _)).pow_const 2) (by positivity)
  intro a x
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (singleFieldMark_bound w _) 2

end SphericalPerceptronFreeEnergy
end

end OAI
