import OAI.Dynamics.StandardMap.TestObservations

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
noncomputable def clippedTest (j : ArrayTestIndex) : DistanceArray → ℝ :=
  arrayObservation (testLeft j.val.1 j.val.2) (testRight j.val.1 j.val.2) testObservation
lemma clippedTest_eq (j : ArrayTestIndex) (d : DistanceArray) :
    clippedTest j d=arrayJ j.val.1 j.val.2 d+
      (unitClip (arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d)-
        unitClip (arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d))^2 := by rfl
lemma clippedTest_nonneg (j : ArrayTestIndex) (d : DistanceArray) : 0≤ clippedTest j d := by
  rw [clippedTest_eq]
  exact add_nonneg (arrayJ_nonneg _ _ j.property d) (sq_nonneg _)
lemma clippedTest_le (j : ArrayTestIndex) (d : DistanceArray) : clippedTest j d≤ arrayTest j d := by
  rw [clippedTest_eq]
  have hh := unitClip_lipschitz.dist_le_mul
    (arrayShortfall j.val.1 (dyadicMid j.val.1 j.val.2) d)
    (arrayShortfall (dyadicMid j.val.1 j.val.2) j.val.2 d)
  simp only [NNReal.coe_one,one_mul,Real.dist_eq] at hh
  have hs := mul_self_le_mul_self (abs_nonneg _) hh
  simp only [←sq, sq_abs] at hs
  change _≤ arrayJ j.val.1 j.val.2 d+arrayV j.val.1 j.val.2 d
  unfold arrayV
  linarith
lemma continuous_clippedTest (j : ArrayTestIndex) : Continuous (clippedTest j) :=
  continuous_arrayObservation _ _ _ testObservation_lipschitz.continuous
lemma integrable_clippedTest (μ : Measure DistanceArray) [IsFiniteMeasure μ] (j : ArrayTestIndex) :
    Integrable (clippedTest j) μ :=
  (continuous_clippedTest j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma unitArray_shortfall_mem (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) (hst : (s:ℝ)< (t:ℝ)) :
    arrayShortfall s t d∈Icc (0:ℝ) 1 := by
  have hlen := sub_pos.mpr hst
  have hn := d.property.1 s t
  have hu := hd s t
  rw [abs_of_pos hlen] at hu
  unfold arrayShortfall
  constructor
  · have hh := (div_le_one hlen).mpr hu
    linarith
  · have hh := div_nonneg hn hlen.le
    linarith
lemma clippedTest_unit (j : ArrayTestIndex) (d : DistanceArray) (hd : UnitArray d) : clippedTest j d=arrayTest j d := by
  apply testObservation_eq_arrayTest
  · exact unitArray_shortfall_mem d hd _ _ (by rw [dyadicMid_val]; linarith [j.property])
  · exact unitArray_shortfall_mem d hd _ _ (by rw [dyadicMid_val]; linarith [j.property])
noncomputable def clippedShortfall (s t : DyadicTime) (d : DistanceArray) : ℝ := unitClip (arrayShortfall s t d)
lemma clippedShortfall_nonneg (s t : DyadicTime) (d : DistanceArray) : 0≤ clippedShortfall s t d := (unitClip_mem _).1
lemma continuous_clippedShortfall (s t : DyadicTime) : Continuous (clippedShortfall s t) :=
  unitClip_lipschitz.continuous.comp (continuous_arrayShortfall s t)
lemma clippedShortfall_unit (d : DistanceArray) (hd : UnitArray d) (s t : DyadicTime) (hst : (s:ℝ)< (t:ℝ)) :
    clippedShortfall s t d=arrayShortfall s t d := unitClip_eq (unitArray_shortfall_mem d hd s t hst)
lemma clippedShortfall_sample (k : ℝ) (hk : 0≤ k) (z : Torus) (n : ℕ) (hn : 0< n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0< m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    clippedShortfall s t (sampleArray k hk z n hn)=torusShortfall k z a m := by
  unfold clippedShortfall
  rw [shortfall_sample_aligned k hk z n hn s t a m hm hs ht]
  exact unitClip_eq (torusShortfall_mem k hk z a m hm)
lemma integral_clippedShortfall_sample (k : ℝ) (hk : 0≤ k) (n : ℕ) (hn : 0< n)
    (s t : DyadicTime) (a : ℤ) (m : ℕ) (hm : 0< m)
    (hs : (n:ℝ)*(s:ℝ)=(a:ℝ)) (ht : (n:ℝ)*(t:ℝ)=(a:ℝ)+(m:ℝ)) :
    (∫d,clippedShortfall s t d ∂sampleLaw k hk n hn)=meanDeficit k m := by
  rw [integral_sampleLaw k hk n hn _ (continuous_clippedShortfall s t)]
  simp_rw [clippedShortfall_sample k hk _ n hn s t a m hm hs ht]
  have hz (z : Torus) : torusShortfall k z a m=torusShortfall k (torusIter k a z) 0 m := by rw [torusShortfall_shift,zero_add]
  simp_rw [hz]
  rw [integral_torusIter k a (fun z => torusShortfall k z 0 m),←meanDeficit_eq_integral_shortfall k hk m]
end StandardMapEntropy

end OAI
