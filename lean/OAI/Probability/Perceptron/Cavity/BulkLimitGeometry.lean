import Mathlib
import OAI.Probability.Perceptron.Control.FreshControl
import OAI.Probability.Perceptron.Cavity.BulkCompactGG
import OAI.Probability.Perceptron.Cavity.BulkRestorationLimit
import OAI.Probability.Perceptron.Variational.LabelProfilePairReference
import OAI.Probability.Perceptron.Interpolation.GibbsArrayGeometry

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal ENNReal

def bulkJointEmbedding (q : CompactOverlap) : CompactJointOverlap := (q,0)
lemma bulkJointEmbedding_continuous : Continuous bulkJointEmbedding := by
  unfold bulkJointEmbedding; fun_prop

def bulkJointLaw (μ : ProbabilityMeasure (CompactArray CompactOverlap)) :
    ProbabilityMeasure (CompactArray CompactJointOverlap) :=
  compactMapLaw bulkJointEmbedding bulkJointEmbedding_continuous μ

lemma bulkGibbsArray_exchangeable (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ) (e : Equiv.Perm ℕ) :
    MeasurePreserving (compactRelabel (K:=CompactOverlap) e)
      (bulkGibbsArrayLaw n M f v : Measure _) (bulkGibbsArrayLaw n M f v : Measure _) :=
  gibbsOverlapArray_exchangeable _ _ _ _ _ _ e

lemma bulkGibbsArray_closed_full (n M : ℕ) (f : ℝ→ᵇℝ) (v : ℕ→ℝ)
    {F : Set (CompactArray CompactOverlap)} (hF : IsClosed F)
    (hfull : ∀ x : ℕ→NormalizedSpin (n+1), overlapArray bulkOverlap x ∈ F) :
    bulkGibbsArrayLaw n M f v F=1 :=
  gibbsOverlapArray_closed_full _ _ _ _ _ _ hF hfull

lemma compact_scalar_gram_closed (r : ℕ) :
    IsClosed {Q : CompactArray CompactOverlap | Matrix.PosSemidef (fun i j : Fin r => (Q i j).val)} :=
  (isClosed_matrix_posSemidef r).preimage (by fun_prop)

lemma bulkGibbsArray_limit_gram (f : ℝ→ᵇℝ) (M : ℕ→ℕ) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q : CompactArray CompactOverlap ∂(ν : Measure _), ∀ r,
      Matrix.PosSemidef (fun i j : Fin r => (Q i j).val) := by
  rw [ae_all_iff]
  intro r
  apply (mem_ae_iff_prob_eq_one (compact_scalar_gram_closed r).measurableSet).mpr
  have hv := weak_limit_closed_full hlim (compact_scalar_gram_closed r)
    (fun n => bulkGibbsArray_closed_full (s n) (M (s n)) f (v (s n))
      (compact_scalar_gram_closed r) (fun x => Matrix.posSemidef_gram ℝ (fun i : Fin r => (x i).val)))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

lemma bulkGibbsArray_limit_diagonal (f : ℝ→ᵇℝ) (M : ℕ→ℕ) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f (v (s n))) atTop (𝓝 ν)) :
    ∀ᵐ Q : CompactArray CompactOverlap ∂(ν : Measure _), ∀ i, (Q i i).val=1 := by
  rw [ae_all_iff]
  intro i
  have hc : IsClosed {Q : CompactArray CompactOverlap | (Q i i).val=1} :=
    isClosed_eq (by fun_prop) continuous_const
  apply (mem_ae_iff_prob_eq_one hc.measurableSet).mpr
  have hv := weak_limit_closed_full hlim hc
    (fun n => bulkGibbsArray_closed_full (s n) (M (s n)) f (v (s n)) hc
      (fun x => spinOverlap_self (x i)))
  simp only [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hv,ENNReal.coe_one]

lemma bulkJointLaw_gram {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hR : ∀ᵐ Q : CompactArray CompactOverlap ∂(ν : Measure _), ∀ r,
      Matrix.PosSemidef (fun i j : Fin r => (Q i j).val)) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(bulkJointLaw ν : Measure _), ∀ r,
      Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val) := by
  apply (ae_map_iff (compactMapArray_continuous bulkJointEmbedding_continuous).measurable.aemeasurable
    (show MeasurableSet {Q : CompactArray CompactJointOverlap | ∀ r,
      Matrix.PosSemidef (fun i j : Fin r => (Q i j).1.val)} by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun r => (compact_spin_gram_closed r).measurableSet)).mpr
  exact hR

lemma bulkJointLaw_diagonal {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hd : ∀ᵐ Q : CompactArray CompactOverlap ∂(ν : Measure _), ∀ i, (Q i i).val=1) :
    ∀ᵐ Q : CompactArray CompactJointOverlap ∂(bulkJointLaw ν : Measure _), ∀ i, (Q i i).1.val=1 := by
  apply (ae_map_iff (compactMapArray_continuous bulkJointEmbedding_continuous).measurable.aemeasurable
    (show MeasurableSet {Q : CompactArray CompactJointOverlap | ∀ i, (Q i i).1.val=1} by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_eq_fun (by fun_prop) measurable_const)).mpr
  exact hd

lemma omitted_bulk_limit_geometry (α : ℝ) (f : ℝ→ᵇℝ) (v : ℕ→ℕ→ℝ)
    (hv : ∀ᶠ n in atTop, ∀ p, 1≤v n p)
    (hd : ∀ p, Tendsto (fun n => omittedBulkDeviation α f n p (v n)) atTop (𝓝 0))
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)} {s : ℕ→ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (patternCount α (s n+1)-2) f (v (s n))) atTop (𝓝 ν)) :
    (∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q) ∧
    (∀ᵐ Q : CompactArray CompactJointOverlap ∂(bulkJointLaw ν : Measure _), 0≤(Q 0 1).1.val) ∧
    (∀ r (i : Fin r) (F : CompactBlock CompactJointOverlap r→ᵇℝ) (g : CompactJointOverlap→ᵇℝ),
      compactGGDefect (bulkJointLaw ν) r i F g=0) := by
  have hGG := compactMapLaw_gg bulkJointEmbedding bulkJointEmbedding_continuous ν
    (omitted_bulk_limit_gg α f v hv hd hs hlim)
  have hR := bulkJointLaw_gram (bulkGibbsArray_limit_gram f (fun n => patternCount α (n+1)-2) v s hlim)
  have hD := bulkJointLaw_diagonal (bulkGibbsArray_limit_diagonal f (fun n => patternCount α (n+1)-2) v s hlim)
  have hEx (e : Equiv.Perm ℕ) := compactMapLaw_exchangeable bulkJointEmbedding bulkJointEmbedding_continuous ν e
    (compact_exchangeability_limit hlim e (fun n => bulkGibbsArray_exchangeable (s n)
      (patternCount α (s n+1)-2) f (v (s n)) e))
  exact ⟨compact_gg_spin_geometry _ hEx hGG hR hD,
    compact_spin_nonnegative _ (compactRealLaw_gg _ hGG) hR,hGG⟩

lemma bulkJointLaw_scalarGram_integral (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (r : ℕ) (F : Matrix (Fin r) (Fin r) ℝ →ᵇ ℝ) :
    (∫ Q : CompactArray CompactJointOverlap, F (fun i j => (Q i j).1.val) ∂(bulkJointLaw ν : Measure _))=
      ∫ Q : CompactArray CompactOverlap, F (fun i j => (Q i j).val) ∂(ν : Measure _) := by
  exact compactMapLaw_integral bulkJointEmbedding bulkJointEmbedding_continuous ν
    (fun Q => F (fun i j => (Q i j).1.val)) (F.continuous.comp (by fun_prop)).measurable

lemma bulk_pair_restoration_ratio_tendsto (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray CompactOverlap)}
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (F : CompactOverlap →ᵇ ℝ) :
    Tendsto (fun n => ∫ p, bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n))
      (compactPairTest F) (gaussianMixedTest (fun _ => 1)) (gaussianMixedTest (fun _ => 1)) p /
      bulkFreshDenominator (s n) (M (s n)) g.f (v (s n)) p^2
      ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ Q : CompactArray CompactOverlap, F (Q 0 1) ∂(ν : Measure _))) := by
  let q := boundedQuantile ((compactPositivePairLaw (bulkJointLaw ν)).map Prod.fst)
  obtain ⟨ρ,η,hG,hge,hp,hm,hl⟩ := quantile_pair_reference_exists q (boundedQuantile_monotone _) g F
  have hpair := (compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn).trans hp.symm
  have he (j : ℕ) : (∫ x, x.1.val*x.2.val^j
      ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
      ∫ Q : CompactArray CompactOverlap, scalarRestorationPairMoment g.f 1 1 F j
        (fun i l => (Q i l).val) ∂(ν : Measure _) := by
    rw [hm j,←scalarGram_eq_of_pair_law (bulkJointLaw ν) ρ hGG hG hgeo hge hpair]
    exact bulkJointLaw_scalarGram_integral ν _ _
  let Ψ : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ := gaussianMixedTest (fun _ => (1 : ℝ →ᵇ ℝ))
  let C := ‖compactPairTest F‖*‖restorationMarkTest 2 g.f Ψ 0‖*‖restorationMarkTest 2 g.f Ψ 0‖+
    pairRestorationBound g.f 1 1 F
  have hC : 0≤C := add_nonneg (by positivity) (pairRestorationBound_nonneg _ _ _ _)
  have hηB (x : WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F)) : |x.1.val|≤C :=
    (abs_le.mpr x.1.prop).trans (le_add_of_nonneg_left (by positivity))
  have hb (n : ℕ) (p : TwoFreshDisorder (s n+1) (M (s n))) :
      |bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Ψ p|≤C :=
    (bulkFreshNumerator_bound _ _ _ _ _ _ _ _ _).trans
      (le_add_of_nonneg_right (pairRestorationBound_nonneg _ _ _ _))
  have hmoment j : Tendsto (fun n => ∫ p,
      bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Ψ p *
      (bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n)) p).val^j
      ∂twoFreshDisorderLaw (s n+1) (M (s n))) atTop
      (𝓝 (∫ x,x.1.val*x.2.val^j ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))) := by
    rw [he j]
    simp_rw [scalarRestorationPairMoment_compact]
    exact bulkFresh_moment_tendsto M g.f v s hlim 2 (compactPairTest F) Ψ Ψ j
  have ht := restoration_ratio_tendsto
    (fun n => twoFreshDisorderLaw (s n+1) (M (s n)))
    (η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F)))
    (Real.exp_pos _)
    (fun n => bulkFreshNumerator (s n) (M (s n)) 2 g.f (v (s n)) (compactPairTest F) Ψ Ψ)
    (fun x => x.1.val)
    (fun n => bulkFreshCompactDenominator (s n) (M (s n)) g.f (v (s n))) (fun x => x.2)
    (fun n => bulkFreshNumerator_measurable _ _ _ _ _ _ _ _) (by fun_prop)
    (fun n => bulkFreshCompactDenominator_measurable _ _ _ _) (by fun_prop)
    hC hb hηB hmoment 2
  have hvalue : (∫ x,x.1.val/x.2.val^2
      ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=
      ∫ Q : CompactArray CompactOverlap,F (Q 0 1) ∂(ν : Measure _) := by
    simp only [div_eq_mul_inv]
    change (∫ x,x.1.val*restorationReciprocal g.f 2 x.2 ∂(η : Measure (WeightedRestorationRange g.f (pairRestorationBound g.f 1 1 F))))=_
    rw [hl,←compactPositivePairLaw_spin_quantile (bulkJointLaw ν) hn]
    have hi := integral_map (μ := (bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)))
      (show Measurable (fun Q : CompactArray CompactJointOverlap => (Q 0 1).1)
        from by fun_prop).aemeasurable
      (show Measurable (fun z : CompactOverlap => F z) from F.continuous.measurable).aestronglyMeasurable
    refine hi.trans ?_
    exact compactMapLaw_integral bulkJointEmbedding bulkJointEmbedding_continuous ν
      (fun Q => F (Q 0 1).1) (by fun_prop)
  rw [hvalue] at ht
  exact ht

end SphericalPerceptronFreeEnergy
end

end OAI
