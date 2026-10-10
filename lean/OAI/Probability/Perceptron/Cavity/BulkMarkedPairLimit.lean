import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkLimitGeometry
import OAI.Probability.Perceptron.Variational.RoundedMarkedReference

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction

lemma bulk_marked_ratio_tendsto_of_reference (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (w w' : ℝ→ᵇℝ) (F : CompactOverlap→ᵇℝ)
    (η : ProbabilityMeasure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F)))
    (hm : ∀ j,(∫ x,x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F))))=
      ∫ Q : CompactArray CompactOverlap,scalarRestorationPairMoment g.f w w' F j
        (fun i l => (Q i l).val) ∂(ν : Measure _)) :
    Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
      (compactPairTest F) (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w')) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*restorationReciprocal g.f 2 x.2
        ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F))))) := by
  let Ψ : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ := gaussianMixedTest (fun _ => w)
  let Φ : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ := gaussianMixedTest (fun _ => w')
  let C := ‖compactPairTest F‖*‖restorationMarkTest 2 g.f Ψ 0‖*‖restorationMarkTest 2 g.f Φ 0‖+
    pairRestorationBound g.f w w' F
  have hC : 0≤C := add_nonneg (by positivity) (pairRestorationBound_nonneg _ _ _ _)
  have hηB (x : WeightedRestorationRange g.f (pairRestorationBound g.f w w' F)) : |x.1.val|≤C :=
    (abs_le.mpr x.1.prop).trans (le_add_of_nonneg_left (by positivity))
  have hb (n : ℕ) (p : TwoFreshDisorder (s n+1) (M (s n))) :
      |bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Φ p|≤C :=
    (bulkFreshNumerator_bound _ _ _ _ _ _ _ _ _).trans
      (le_add_of_nonneg_right (pairRestorationBound_nonneg _ _ _ _))
  have hmoment j : Tendsto (fun n => ∫ p,
      bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Φ p *
      (bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n)) p).val^j
      ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F))))) := by
    rw [hm j]
    simp_rw [scalarRestorationPairMoment_compact]
    exact bulkFresh_moment_tendsto M g.f v s hlim 2 (compactPairTest F) Ψ Φ j
  have ht := restoration_ratio_tendsto
    (fun n => twoFreshDisorderLaw (s n+1) (M (s n)))
    (η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w w' F)))
    (Real.exp_pos _)
    (fun n => bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Φ)
    (fun x => x.1.val)
    (fun n => bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n))) (fun x => x.2)
    (fun n => bulkFreshNumerator_measurable _ _ _ _ _ _ _ _) (by fun_prop)
    (fun n => bulkFreshCompactDenominator_measurable _ _ _ _) (by fun_prop)
    hC hb hηB hmoment 2
  simpa only [div_eq_mul_inv, restorationReciprocal, ContinuousMap.coe_mk, bulkFreshCompactDenominator, Ψ, Φ] using ht

theorem bulk_marked_pair_limit_exists (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ a : ℝ→ℝ, Monotone a ∧ (∀ r,0≤a r ∧ a r≤‖w‖^2) ∧
      ∀ (F : CompactOverlap→ᵇℝ) (b : Bool),
    Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
      (compactPairTest F) (gaussianMixedTest (fun _=>w))
      (gaussianMixedTest (fun _=>secondPairMark w b)) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
        ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^(pairMarkPower b) ∂(ν : Measure _))) := by
  let q := boundedQuantile ((compactPositivePairLaw (bulkJointLaw ν)).map Prod.fst)
  have hq : Monotone q := boundedQuantile_monotone _
  obtain ⟨a,ham,hab,href⟩ := quantile_marked_pair_reference_exists q hq g w
  refine ⟨a,ham,hab,fun F b => ?_⟩
  obtain ⟨ρ,η,hG,hge,hp,hm,hl⟩ := href F b
  have hpair := (compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn).trans hp.symm
  have he (j : ℕ) : (∫ x,x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f w (secondPairMark w b) F))))=
      ∫ Q : CompactArray CompactOverlap,scalarRestorationPairMoment g.f w (secondPairMark w b) F j
        (fun i l => (Q i l).val) ∂(ν : Measure _) := by
    rw [hm j,←scalarGram_eq_of_pair_law (bulkJointLaw ν) ρ hGG hG hgeo hge hpair]
    exact bulkJointLaw_scalarGram_integral ν _ _
  have ht := bulk_marked_ratio_tendsto_of_reference M g v s hlim w (secondPairMark w b) F η he
  rw [hl] at ht
  have hmG : Measurable (fun z : CompactOverlap => F z*(a z.val)^(pairMarkPower b)) :=
    F.measurable.mul ((ham.measurable.comp measurable_subtype_coe).pow_const _)
  have hvalue : (∫ u,F (timeSpin (q u))*(a (q u))^(pairMarkPower b) ∂timeLaw)=
      ∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^(pairMarkPower b) ∂(ν : Measure _) := by
    change (∫ u,F (timeSpin (q u))*(a (timeSpin (q u)).val)^(pairMarkPower b) ∂timeLaw)=_
    rw [←quantileSpinLaw_integral q hq.measurable (fun z => F z*(a z.val)^(pairMarkPower b)) hmG,
      ←compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn]
    have hi := integral_map (μ := (bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)))
      (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
        from by fun_prop).aemeasurable hmG.aestronglyMeasurable
    refine hi.trans ?_
    exact compactMapLaw_integral bulkJointEmbedding bulkJointEmbedding_continuous ν
      (fun Q => F (Q 0 1).1*(a (Q 0 1).1.val)^(pairMarkPower b))
      (F.measurable.comp (by fun_prop) |>.mul ((ham.measurable.comp (by fun_prop)).pow_const _))
  rwa [hvalue] at ht

def pairFieldMark (w : ℝ→ᵇℝ) (z : Fin 2→ℝ) : ℝ := ∏ i,w (z i)
lemma pairFieldMark_measurable (w : ℝ→ᵇℝ) : Measurable (pairFieldMark w) := by
  unfold pairFieldMark
  fun_prop
lemma pairFieldMark_bound (w : ℝ→ᵇℝ) (z : Fin 2→ℝ) : |pairFieldMark w z|≤‖w‖^2 := by
  simp only [pairFieldMark,Fin.prod_univ_two,abs_mul,pow_two]
  exact mul_le_mul (w.norm_coe_le_norm _) (w.norm_coe_le_norm _) (abs_nonneg _) (norm_nonneg _)

def bulkPairAverage (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 2→NormalizedSpin (n+1)) : ℝ :=
  ((n+1:ℕ):ℝ)⁻¹*∑ i,pairFieldMark w (bulkPatternFields i a x)

lemma bulkPairAverage_measurable (n M : ℕ) (w : ℝ→ᵇℝ) :
    Measurable (Function.uncurry (bulkPairAverage n M w)) := by
  apply Measurable.const_mul
  exact Finset.measurable_sum _ fun i _ => (pairFieldMark_measurable w).comp (bulkPatternFields_measurable _ _ _ _)

lemma bulkPairAverage_bound (n M : ℕ) (w : ℝ→ᵇℝ) (a : BulkDisorder (n+1) M)
    (x : Fin 2→NormalizedSpin (n+1)) : |bulkPairAverage n M w a x|≤M/(n+1:ℕ)*‖w‖^2 := by
  unfold bulkPairAverage
  rw [abs_mul,abs_of_nonneg (by positivity : 0≤(((n+1:ℕ):ℝ)⁻¹))]
  have h : |∑ i : Fin M,pairFieldMark w (bulkPatternFields i a x)|≤M*‖w‖^2 :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => pairFieldMark_bound w _).trans_eq (by simp))
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by ring)

def bulkPairOverlapTest (n : ℕ) (F : CompactOverlap→ᵇℝ) (x : Fin 2→NormalizedSpin (n+1)) : ℝ :=
  F (bulkOverlap (x 1) (x 0))
lemma bulkPairOverlapTest_measurable (n : ℕ) (F : CompactOverlap→ᵇℝ) : Measurable (bulkPairOverlapTest n F) := by
  unfold bulkPairOverlapTest bulkOverlap spinOverlap
  fun_prop

lemma bulk_last_two_fields (n M : ℕ) (a : BulkDisorder (n+1) (M+2))
    (x : Fin 2→NormalizedSpin (n+1)) :
    (fun i => gaussianRows (fun i => (x i).val) (bulkSeparateTwo (n+1) M a).2.1 i)=
      bulkPatternFields ((Fin.last M).castSucc) a x ∧
    (fun i => gaussianRows (fun i => (x i).val) (bulkSeparateTwo (n+1) M a).2.2 i)=
      bulkPatternFields (Fin.last (M+1)) a x := by
  constructor <;> funext i <;>
    simp only [gaussianRows_apply,bulkSeparateTwo,bulkSeparateLast,bulkPatternFields,
      EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]

lemma bulk_marked_last_pair (n M : ℕ) (f w w' : ℝ→ᵇℝ) (v : ℕ→ℝ)
    (F : CompactOverlap→ᵇℝ) :
    bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*
      pairFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x)*
      pairFieldMark w' (bulkPatternFields (Fin.last (M+1)) a x))=
    ∫ p,bulkFreshNumerator n M 2 f v (compactPairTest F)
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w')) p /
      bulkFreshDenominator n M f v p^2 ∂twoFreshDisorderLaw (n+1) M := by
  rw [←bulkFresh_annealed_restoration]
  unfold bulkReplicaMean
  apply integral_congr_ae
  exact ae_of_all _ fun a => by
    congr 1

lemma bulkPairAverage_first (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (F : CompactOverlap→ᵇℝ) :
    bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*bulkPairAverage n (M+2) w a x)=
    ((M+2:ℕ):ℝ)/(n+1:ℕ)*(∫ p,bulkFreshNumerator n M 2 f v (compactPairTest F)
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>(1:ℝ→ᵇℝ))) p /
      bulkFreshDenominator n M f v p^2 ∂twoFreshDisorderLaw (n+1) M) := by
  have hf : (fun a x => bulkPairOverlapTest n F x*bulkPairAverage n (M+2) w a x)=
      (fun a x => ((n+1:ℕ):ℝ)⁻¹*(bulkPairOverlapTest n F x*∑ i,pairFieldMark w (bulkPatternFields i a x))) := by
    funext a x; unfold bulkPairAverage; ring
  rw [hf,bulkReplicaMean_const_mul,bulk_pattern_sum_first n (M+2) 2 f v _ (bulkPairOverlapTest_measurable n F)
    _ (pairFieldMark_measurable w) (norm_nonneg F) (sq_nonneg ‖w‖)
    (fun x => F.norm_coe_le_norm _) (pairFieldMark_bound w) ((Fin.last M).castSucc)]
  rw [←bulk_marked_last_pair n M f w 1 v F]
  simp only [pairFieldMark,BoundedContinuousFunction.coe_one,Pi.one_apply,Finset.prod_const_one,mul_one]
  ring

lemma bulkPairAverage_second (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (F : CompactOverlap→ᵇℝ) :
    bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*(bulkPairAverage n (M+2) w a x)^2)=
    ((M+2:ℕ):ℝ)/(n+1:ℕ)^2*
      bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*
        (pairFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x))^2)+
    (((M+2:ℕ):ℝ)*((M+1:ℕ):ℝ)/(n+1:ℕ)^2)*(∫ p,bulkFreshNumerator n M 2 f v (compactPairTest F)
      (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w)) p /
      bulkFreshDenominator n M f v p^2 ∂twoFreshDisorderLaw (n+1) M) := by
  have hf : (fun a x => bulkPairOverlapTest n F x*(bulkPairAverage n (M+2) w a x)^2)=
      (fun a x => (((n+1:ℕ):ℝ)⁻¹)^2*(bulkPairOverlapTest n F x*(∑ i,pairFieldMark w (bulkPatternFields i a x))^2)) := by
    funext a x; unfold bulkPairAverage; ring
  have hkl : (Fin.last M).castSucc≠Fin.last (M+1) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_castSucc,Fin.val_last] at this
    omega
  rw [hf,bulkReplicaMean_const_mul,bulk_pattern_sum_second n (M+2) 2 f v _ (bulkPairOverlapTest_measurable n F)
    _ (pairFieldMark_measurable w) (norm_nonneg F) (sq_nonneg ‖w‖)
    (fun x => F.norm_coe_le_norm _) (pairFieldMark_bound w) ((Fin.last M).castSucc) (Fin.last (M+1)) hkl,
    bulk_marked_last_pair n M f w w v F]
  simp only [div_eq_mul_inv,inv_pow]
  push_cast
  ring

lemma bulkPairAverage_diagonal_bound (n M : ℕ) (f w : ℝ→ᵇℝ) (v : ℕ→ℝ) (F : CompactOverlap→ᵇℝ) :
    |bulkReplicaMean n (M+2) f v 2 (fun a x => bulkPairOverlapTest n F x*
        (pairFieldMark w (bulkPatternFields ((Fin.last M).castSucc) a x))^2)|≤‖F‖*‖w‖^4 := by
  apply bulkReplicaMean_bound _ _ _ _ _ _
    ((bulkPairOverlapTest_measurable n F |>.comp measurable_snd).mul
      (((pairFieldMark_measurable w).comp (bulkPatternFields_measurable _ _ _ _)).pow_const 2)) (by positivity)
  intro a x
  rw [abs_mul,abs_pow]
  apply (mul_le_mul (F.norm_coe_le_norm _) (pow_le_pow_left₀ (abs_nonneg _) (pairFieldMark_bound w _) 2)
    (by positivity) (norm_nonneg _)).trans_eq
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
