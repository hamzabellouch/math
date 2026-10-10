import OAI.Dynamics.StandardMap.BridgeRealBound

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def arrayObservation {R : ℕ} (a b : Fin R → DyadicTime)
    (F : (Fin R → ℝ) → ℝ) (d : DistanceArray) : ℝ := F (fun i => arrayShortfall (a i) (b i) d)
lemma continuous_arrayObservation {R : ℕ} (a b : Fin R → DyadicTime)
    (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) : Continuous (arrayObservation a b F) :=
  hF.comp (continuous_pi fun i => continuous_arrayShortfall (a i) (b i))
lemma arrayObservation_sample {R : ℕ} (k : ℝ) (hk : 0≤ k) (n : ℕ) (hn : 0< n)
    (a b : Fin R → DyadicTime) (A : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀i,0< m i)
    (ha : ∀i,(n:ℝ)*(a i:ℝ)=(A i:ℝ)) (hb : ∀i,(n:ℝ)*(b i:ℝ)=(A i:ℝ)+(m i:ℝ))
    (F : (Fin R → ℝ) → ℝ) (z : Torus) :
    arrayObservation a b F (sampleArray k hk z n hn)=shortfallObservation k A m F z := by
  unfold arrayObservation shortfallObservation
  congr 1
  funext i
  exact shortfall_sample_aligned k hk z n hn (a i) (b i) (A i) (m i) (hm i) (ha i) (hb i)
lemma array_fast_sample (k : ℝ) (hk : 0≤ k) (z : Torus) (n : ℕ) (hn : 0< n)
    (u v : DyadicTime) (a : ℤ) (N : ℕ)
    (hu : (n:ℝ)*(u:ℝ)=(a:ℝ)) (hv : (n:ℝ)*(v:ℝ)=(a:ℝ)+(N:ℝ))
    (hf : (999/1000:ℝ)*((v:ℝ)-(u:ℝ))< (sampleArray k hk z n hn).val u v) :
    torusFastBridge k (torusIter k a z) N := by
  change _< rescaledDistance k z n u v at hf
  rw [rescaledDistance_aligned k z n u v a (a+(N:ℤ)) hu (by push_cast; exact hv),
    productDistance_forward] at hf
  have hshift := torusSegmentTransfer_shift k z 0 a N
  rw [zero_add] at hshift
  unfold torusFastBridge
  rw [hshift,Real.rpow_le_iff_le_log (by linarith [growthBase_ge_four k hk])
    (lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk z a N).1)]
  have hnp : (0:ℝ)< n := by exact_mod_cast hn
  have hg : 0< Real.log (growthBase k) := log_growthBase_pos k hk
  have hl : (n:ℝ)*((v:ℝ)-(u:ℝ))=N := by linarith
  have he := (lt_div_iff₀ hnp).mp hf
  have he' := (lt_div_iff₀ hg).mp he
  nlinarith
lemma integral_observable_sample {R : ℕ} (k : ℝ) (hk : 0≤ k) (n : ℕ) (hn : 0< n)
    (a b : Fin R → DyadicTime) (A : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀i,0< m i)
    (ha : ∀i,(n:ℝ)*(a i:ℝ)=(A i:ℝ)) (hb : ∀i,(n:ℝ)*(b i:ℝ)=(A i:ℝ)+(m i:ℝ))
    (F : (Fin R → ℝ) → ℝ) (hF : Continuous F) :
    (∫ d,arrayObservation a b F d ∂sampleLaw k hk n hn)=∫ z,shortfallObservation k A m F z ∂area := by
  rw [integral_sampleLaw k hk n hn _ (continuous_arrayObservation a b F hF)]
  apply integral_congr_ae
  exact Eventually.of_forall (arrayObservation_sample k hk n hn a b A m hm ha hb F)
lemma integral_supported_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F W : X → ℝ) (hF : Integrable F μ) (hW : Integrable W μ) (E : Set X) (hE : MeasurableSet E)
    (D : ℝ) (_hD : 0≤ D) (_hW0 : ∀x,0≤ W x)
    (hb : ∀x,x∈E → F x≤ D*W x) (hz : ∀x,x∉E → F x=0) :
    (∫ x,F x ∂μ)≤ D*(∫ x in E,W x ∂μ) := by
  rw [←integral_const_mul,←integral_indicator hE]
  apply integral_mono hF ((hW.const_mul D).indicator hE)
  intro x
  by_cases hx : x∈E
  · simpa only [indicator_of_mem hx] using hb x hx
  · rw [hz x hx,indicator_of_notMem hx]
end StandardMapEntropy

end OAI
