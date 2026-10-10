import OAI.Dynamics.StandardMap.ArrayMoments

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def scaleLaw (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) : Measure DistanceArray :=
  ENNReal.ofReal (1/ε) • ∑ i∈Finset.range l,sampleLaw k hk (2^(p+i)) (by positivity)
noncomputable instance scaleLawFinite (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) :
    IsFiniteMeasure (scaleLaw k hk p l ε) := by
  unfold scaleLaw
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top
lemma integral_scaleLaw (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (hε : 0<ε)
    (F : DistanceArray → ℝ) (hF : Continuous F) :
    (∫ d,F d ∂scaleLaw k hk p l ε)=(∑ i∈Finset.range l,∫ d,F d ∂sampleLaw k hk (2^(p+i)) (by positivity))/ε := by
  rw [scaleLaw,integral_smul_measure,ENNReal.toReal_ofReal (by positivity : 0≤1/ε)]
  rw [integral_finsetSum_measure]
  · simp only [smul_eq_mul]; ring
  · intro i hi
    exact hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma scaleLaw_dilate_boundary (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) :
    (scaleLaw k hk p l ε).map arrayDilate+
      ENNReal.ofReal (1/ε) • sampleLaw k hk (2^p) (by positivity)=
      scaleLaw k hk p l ε+ENNReal.ofReal (1/ε) • sampleLaw k hk (2^(p+l)) (by positivity) := by
  unfold scaleLaw
  rw [Measure.map_smul _ continuous_arrayDilate.measurable.aemeasurable,Measure.map_finset_sum continuous_arrayDilate.measurable.aemeasurable]

  simp_rw [sampleLaw_dilate]
  have he (i : ℕ) : 2^(p+i)+2^(p+i)=2^(p+(i+1)) := by
    rw [show p+(i+1)=(p+i)+1 by omega,pow_succ,Nat.mul_two]
  simp_rw [he]
  have hsum : (∑ i∈Finset.range l,sampleLaw k hk (2^(p+(i+1))) (by positivity))+
      sampleLaw k hk (2^p) (by positivity)=
      (∑ i∈Finset.range l,sampleLaw k hk (2^(p+i)) (by positivity))+
        sampleLaw k hk (2^(p+l)) (by positivity) := by
    induction l with
    | zero => simp
    | succ l ih =>
      rw [Finset.sum_range_succ,Finset.sum_range_succ]
      calc
        _ = ((∑ i∈Finset.range l,sampleLaw k hk (2^(p+(i+1))) (by positivity))+sampleLaw k hk (2^p) (by positivity))+
          sampleLaw k hk (2^(p+(l+1))) (by positivity) := by ac_rfl
        _ = _ := by rw [ih]
  rw [← smul_add,← smul_add,hsum]
lemma scaleLaw_translate (k : ℝ) (hk : 0≤k) (p l : ℕ) (ε : ℝ) (r : DyadicTime)
    (a : ℤ) (ha : ((2^p:ℕ):ℝ)*(r:ℝ)=(a:ℝ)) :
    (scaleLaw k hk p l ε).map (arrayTranslate r)=scaleLaw k hk p l ε := by
  unfold scaleLaw
  rw [Measure.map_smul _ (continuous_arrayTranslate r).measurable.aemeasurable,Measure.map_finset_sum (continuous_arrayTranslate r).measurable.aemeasurable]

  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply sampleLaw_translate k hk _ _ r (a*2^i)
  push_cast at ha ⊢
  rw [pow_add]
  calc
    _ = (((2:ℝ)^p)*(r:ℝ))*(2:ℝ)^i := by ring
    _ = _ := by rw [ha]
end StandardMapEntropy

end OAI
