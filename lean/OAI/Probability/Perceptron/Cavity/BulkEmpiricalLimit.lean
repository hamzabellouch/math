import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkMarkedPairLimit

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction NNReal ENNReal BigOperators

lemma bulk_density_factors (M s : ℕ→ℕ) (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α)) :
    Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2) atTop (𝓝 0) ∧
    Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)*((M (s n)+1:ℕ):ℝ)/(s n+1:ℕ)^2)
      atTop (𝓝 (α^2)) := by
  have hn : Tendsto (fun n => ((s n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hs)
  have hi : Tendsto (fun n => (((s n+1:ℕ):ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hn
  have hfirst := hd.mul hi
  have hsecond := hd.mul (hd.sub hi)
  constructor
  · convert hfirst using 1 <;> try simp
    funext n
    field_simp
  · convert hsecond using 1 <;> try ring_nf
    funext n
    push_cast
    field_simp
    ring

lemma bulkPairAverage_first_limit (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (α : ℝ) (w : ℝ→ᵇℝ) (a : ℝ→ℝ) (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ht : ∀ F : CompactOverlap→ᵇℝ,
      Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
        (compactPairTest F) (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>(1:ℝ→ᵇℝ))) p /
        bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
          ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
        (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1)*a (Q 0 1).val ∂(ν : Measure _))))
    (F : CompactOverlap→ᵇℝ) :
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
      (fun d x => bulkPairOverlapTest (s n) F x*bulkPairAverage (s n) (M (s n)+2) w d x))
      atTop (𝓝 (α*(∫ Q : CompactArray CompactOverlap,F (Q 0 1)*a (Q 0 1).val ∂(ν : Measure _)))) := by
  simp_rw [bulkPairAverage_first]
  exact hd.mul (ht F)

lemma bulkPairAverage_second_limit (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ) (w : ℝ→ᵇℝ) (a : ℝ→ℝ)
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ht : ∀ F : CompactOverlap→ᵇℝ,
      Tendsto (fun n => ∫ p,bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
        (compactPairTest F) (gaussianMixedTest (fun _=>w)) (gaussianMixedTest (fun _=>w)) p /
        bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
          ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
        (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^2 ∂(ν : Measure _))))
    (F : CompactOverlap→ᵇℝ) :
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
      (fun d x => bulkPairOverlapTest (s n) F x*(bulkPairAverage (s n) (M (s n)+2) w d x)^2))
      atTop (𝓝 (α^2*(∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^2 ∂(ν : Measure _)))) := by
  have hfac := bulk_density_factors M s hs α hd
  have herr : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2*
      bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2 (fun d x => bulkPairOverlapTest (s n) F x*
        (pairFieldMark w (bulkPatternFields ((Fin.last (M (s n))).castSucc) d x))^2)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) (by simpa only [zero_mul] using hfac.1.mul_const (‖F‖*‖w‖^4))
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (by positivity : 0≤((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2)]
    exact mul_le_mul_of_nonneg_left (bulkPairAverage_diagonal_bound (s n) (M (s n)) g.f w (v (s n)) F) (by positivity : 0≤((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)^2)
  simp_rw [bulkPairAverage_second]
  simpa using herr.add (hfac.2.mul (ht F))

theorem bulk_marked_empirical_limits (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (w : ℝ→ᵇℝ) : ∃ a : ℝ→ℝ, Monotone a ∧ (∀ r,0≤a r ∧ a r≤‖w‖^2) ∧
      ∀ F : CompactOverlap→ᵇℝ,
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
      (fun d x => bulkPairOverlapTest (s n) F x*bulkPairAverage (s n) (M (s n)+2) w d x))
      atTop (𝓝 (α*(∫ Q : CompactArray CompactOverlap,F (Q 0 1)*a (Q 0 1).val ∂(ν : Measure _)))) ∧
    Tendsto (fun n => bulkReplicaMean (s n) (M (s n)+2) g.f (v (s n)) 2
      (fun d x => bulkPairOverlapTest (s n) F x*(bulkPairAverage (s n) (M (s n)+2) w d x)^2))
      atTop (𝓝 (α^2*(∫ Q : CompactArray CompactOverlap,F (Q 0 1)*(a (Q 0 1).val)^2 ∂(ν : Measure _)))) := by
  obtain ⟨a,ham,hab,ht⟩ := bulk_marked_pair_limit_exists M g v s hlim hGG hgeo hn w
  refine ⟨a,ham,hab,fun F => ⟨?_,?_⟩⟩
  · apply bulkPairAverage_first_limit M g v s α w a ν hd _ F
    intro F
    simpa [secondPairMark,pairMarkPower] using ht F false
  · apply bulkPairAverage_second_limit M g v s hs α w a ν hd _ F
    intro F
    simpa [secondPairMark,pairMarkPower] using ht F true

lemma bulk_pair_restoration_exact (n M : ℕ) (g : Jet3) (v : ℕ→ℝ)
    (F : CompactOverlap →ᵇ ℝ) :
    (∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(bulkGibbsArrayLaw n (M+2) g.f v : Measure _))=
      ∫ p,bulkFreshNumerator n M 2 g.f v (compactPairTest F)
        (gaussianMixedTest (fun _=>1)) (gaussianMixedTest (fun _=>1)) p /
        bulkFreshDenominator n M g.f v p^2 ∂twoFreshDisorderLaw (n+1) M := by
  have he := bulkFresh_annealed_restoration n M 2 g.f v (compactPairTest F)
    (gaussianMixedTest (fun _=>1)) (gaussianMixedTest (fun _=>1))
  let A : CompactBlock CompactOverlap 2 →ᵇ ℝ := F.compContinuous ⟨fun Q=>Q 0 1,by fun_prop⟩
  have hb := bulkGibbsArray_block n (M+2) g.f v 2 A
  change (∫ Q,A (compactBlock 2 Q) ∂(bulkGibbsArrayLaw n (M+2) g.f v : Measure _))=_
  rw [hb,←he]
  apply integral_congr_ae
  filter_upwards [] with a
  congr 1
  funext x
  simp only [bulkMarkedTest,gaussianMixedTest_apply,BoundedContinuousFunction.coe_one,Pi.one_apply,Finset.prod_const_one,mul_one]
  change F (bulkOverlap (x 0) (x 1))=F (bulkOverlap (x 1) (x 0))
  congr 1
  apply Subtype.ext
  exact real_inner_comm _ _

lemma bulk_full_pair_tendsto (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (F : CompactOverlap →ᵇ ℝ) :
    Tendsto (fun n => ∫ Q : CompactArray CompactOverlap,F (Q 0 1)
      ∂(bulkGibbsArrayLaw (s n) (M (s n)+2) g.f (v (s n)) : Measure _)) atTop
      (𝓝 (∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(ν : Measure _))) := by
  simp_rw [bulk_pair_restoration_exact]
  exact bulk_pair_restoration_ratio_tendsto M g v s hlim hGG hgeo hn F

lemma bulk_limit_geometry (M : ℕ→ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1≤v n p)
    (hd : ∀ p, Tendsto (fun n => bulkDeviationAt n (M n) f p (v n)) atTop (𝓝 0))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν)) :
    (∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(bulkJointLaw ν : Measure _), 0≤(Q 0 1).1.val) ∧
    (∀ r (i : Fin r) (F : CompactBlock CompactJointOverlap r→ᵇℝ) (g : CompactJointOverlap→ᵇℝ),
      compactGGDefect (bulkJointLaw ν) r i F g=0) := by
  have hGG := compactMapLaw_gg bulkJointEmbedding bulkJointEmbedding_continuous ν
    (bulk_limit_gg M f v hv hd hs hlim)
  have hR := bulkJointLaw_gram (bulkGibbsArray_limit_gram f M v s hlim)
  have hD := bulkJointLaw_diagonal (bulkGibbsArray_limit_diagonal f M v s hlim)
  have hEx (e : Equiv.Perm ℕ) := compactMapLaw_exchangeable bulkJointEmbedding bulkJointEmbedding_continuous ν e
    (compact_exchangeability_limit hlim e (fun n => bulkGibbsArray_exchangeable (s n) (M (s n)) f (v (s n)) e))
  exact ⟨compact_gg_spin_geometry _ hEx hGG hR hD,
    compact_spin_nonnegative _ (compactRealLaw_gg _ hGG) hR,hGG⟩

lemma bulk_full_omitted_pair_integral (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {μ ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (homit : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 μ))
    (hfull : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)+2) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw μ) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw μ : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw μ : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (F : CompactOverlap →ᵇ ℝ) :
    (∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(μ : Measure _))=
      ∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(ν : Measure _) := by
  let A : CompactArray CompactOverlap →ᵇ ℝ := F.compContinuous ⟨fun Q=>Q 0 1,by fun_prop⟩
  exact tendsto_nhds_unique (bulk_full_pair_tendsto M g v s homit hGG hgeo hn F)
    ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction A).continuousAt.tendsto.comp hfull)

end SphericalPerceptronFreeEnergy
end

end OAI
