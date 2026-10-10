import Mathlib
import OAI.Probability.Perceptron.Variational.QuantileReference
import OAI.Probability.Perceptron.Variational.QuantileLimit

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

instance compactPositivePairLaw_fst_isProbability
    (ν : ProbabilityMeasure (CompactArray CompactJointOverlap)) :
    IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
  inferInstance

lemma compactPositivePairLaw_spin_quantile
    (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hn : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val) :
    (ν : Measure (CompactArray CompactJointOverlap)).map (fun Q => (Q 0 1).1)=
      (quantileSpinLaw (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))
        (boundedQuantile_measurable _) : Measure CompactOverlap) := by
  have : IsProbabilityMeasure ((compactPositivePairLaw ν).map Prod.fst) :=
    inferInstance
  change _=timeLaw.map (timeSpin ∘ boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))
  rw [←Measure.map_map timeSpin_continuous.measurable (boundedQuantile_measurable _),
    timeLaw_eq_volume,boundedQuantile_law]
  unfold compactPositivePairLaw
  rw [Measure.map_map (f := fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1))
    measurable_fst (by exact compactPositivePair_measurable.comp (by fun_prop))]
  rw [Measure.map_map timeSpin_continuous.measurable
    (show Measurable (Prod.fst ∘ fun Q : CompactArray CompactJointOverlap => compactPositivePair (Q 0 1)) from
      measurable_fst.comp (compactPositivePair_measurable.comp (by fun_prop)))]
  apply Measure.map_congr
  filter_upwards [hn] with Q hQ
  apply Subtype.ext
  change (Q 0 1).1.val=max 0 (Q 0 1).1.val
  exact (max_eq_right hQ).symm

theorem compactGG_freshLog_control (ν : ProbabilityMeasure (CompactArray CompactJointOverlap))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect ν r i G a=0)
    (hgeo : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (g : Jet3) (η : ProbabilityMeasure (FreshPartitionRange g.f))
    (hm : ∀ r, (∫ x, x.val^r ∂(η : Measure (FreshPartitionRange g.f)))=
      ∫ Q, freshReplicaArrayKernel (expBCF 1 g.f) r Q ∂(ν : Measure _))
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    (∫ x, Real.log x.val ∂(η : Measure (FreshPartitionRange g.f)))=
      controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))) := by
  obtain ⟨ρ,ξ,hG,hge,hp,hξ,hl⟩ := quantile_reference_exists
    (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst)) (boundedQuantile_monotone _) g P hB
  rw [freshLog_eq_of_pair_law ν ρ hGG hG hgeo hge
    ((compactPositivePairLaw_spin_quantile ν hn).trans hp.symm) g.f η ξ hm hξ]
  exact hl

theorem source_contact_freshLog_control (k : ℕ) (g : Jet3) (p d : ℕ → ℕ) (z : Fin k → ℝ)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1)
    (t : ℕ → ℝ≥0) (h : ℕ → Fin (k+1) → ℝ)
    (hh0 : ∀ n l, 0≤h n l) (hh : ∀ n, Monotone (h n))
    (u : (n : ℕ) → Fin (n+1) → ℝ)
    (hu : ∀ n, u n ∈ Icc (fun _ => 1) (fun _ => 2))
    (hmin : ∀ n, IsMinOn (fun v => quadraticBoxPenalty (sourcePenaltyWeight (n+1)) v-
      sourceExpectedPressure n k g.f (fun j => p j.val) (fun j => d j.val) (h n) z (t n) v)
      (Icc (fun _ : Fin (n+1) => 1) (fun _ => 2)) (u n))
    {H T : ℝ} (hH : 0≤H) (hhH : ∀ n, h n 0≤H) (ht : ∀ n, (t n:ℝ)≤T)
    (hcover : ∀ a b : ℕ, 1≤a+b → ∃ j, p j=a ∧ d j=b)
    {ν : ProbabilityMeasure (CompactArray CompactJointOverlap)} {s : ℕ → ℕ} (hs : StrictMono s)
    (hlim : Tendsto (fun n => sourceGibbsArrayLaw (s n) k g.f
      (fun a => p a.val) (fun a => d a.val) (h (s n)) (u (s n)) z (t (s n))) atTop (𝓝 ν))
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    Tendsto (fun n => sourceFreshLog (s n) k g.f (fun a => p a.val) (fun a => d a.val)
      (h (s n)) (u (s n)) z (t (s n))) atTop
      (𝓝 (controlValue P g.f (quantileTrial (boundedQuantile ((compactPositivePairLaw ν).map Prod.fst))))) := by
  obtain ⟨η,hη,hm,hl⟩ := sourceFreshLog_tendsto k g.f (fun _ a => p a.val) (fun _ a => d a.val)
    h hh0 hh u z t s hlim
  have hGG := source_contact_limit_joint_gg k g.f p d z hz hz0 hz1 t h hh0 hh u hu hmin
    hH hhH ht hs hlim hcover
  have hgeo := source_contact_limit_spin_geometry k g.f p d z hz hz0 hz1 t h hh0 hh u hu hmin
    hH hhH ht hcover hs hlim
  have hn := compact_spin_nonnegative ν (compactRealLaw_gg ν hGG)
    (sourceGibbsArray_limit_gram k g.f (fun _ a => p a.val) (fun _ a => d a.val) h u z t s hlim).1
  rwa [compactGG_freshLog_control ν hGG hgeo hn g η hm P hB] at hl

end SphericalPerceptronFreeEnergy
end

end OAI
