import Mathlib
import OAI.Probability.Ballisticity.Estimates.ConvolutionCentersClose
import OAI.Probability.Ballisticity.Coupling.QuenchedConditionedTubeTransfer
import OAI.Probability.Ballisticity.Estimates.SuccessfulAverage

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem successfulAverage_tube_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (b : ℕ → ℝ) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (z : ℕ → ℝ) (hz : Tendsto z atTop atTop) :
    limsup (fun i => (successfulAverage ν (realPosition (step e)) (H i)).real
      (MedianTubeFailure (realPosition (step e)) f b (H i) (z i))) atTop ≤
    10*limsup (fun i => (conditionedLaw ν (realPosition (step e))).real
      (MedianTubeFailure (realPosition (step e)) f b (H i) (z i/10))) atTop := by
  let ℓ := realPosition (step e)
  let μ := fun i => successfulAverage ν ℓ (H i)
  let η := fun i => rawConditionedWeight ν ℓ (fun ω => (crossingQuenched ℓ 0 (H i) ω)⁻¹)
  let : ∀ i, IsProbabilityMeasure (μ i) := fun i => successfulAverage_probability ν hue ℓ (signed_direction_unit e) htrans (H i)
  let : IsProbabilityMeasure (quenchedConditionedAverage ν ℓ) :=
    quenchedConditionedAverage_probability ν hue ℓ (signed_direction_unit e) htrans
  let a := fun i => (μ i).real (MedianTubeFailure ℓ f b (H i) (z i))
  let q := fun i => (quenchedConditionedAverage ν ℓ).real (MedianTubeFailure ℓ f b (H i) (z i))
  have hab : IsBoundedUnder (· ≤ ·) atTop a := ⟨1,
    (show ∀ᶠ i in atTop, a i ≤ 1 from Eventually.of_forall fun _ => measureReal_le_one)⟩
  have hqb : IsBoundedUnder (· ≤ ·) atTop q := ⟨1,
    (show ∀ᶠ i in atTop, q i ≤ 1 from Eventually.of_forall fun _ => measureReal_le_one)⟩
  have hac : IsCoboundedUnder (· ≤ ·) atTop a :=
    (show IsBoundedUnder (· ≥ ·) atTop a from ⟨0,
      (show ∀ᶠ i in atTop, 0 ≤ a i from Eventually.of_forall fun _ => measureReal_nonneg)⟩).isCoboundedUnder_le
  have hm : Tendsto (fun i => (η i).real Set.univ) atTop (𝓝 1) := by
    have hh := (ENNReal.continuousAt_toReal (by simp : (1:ℝ≥0∞) ≠ ∞)).tendsto.comp
      ((raw_crossingDensity_mass_tendsto ν hue ℓ (signed_direction_unit e) htrans).comp hH)
    simpa only [Function.comp_def,Measure.real,ENNReal.toReal_one,η] using hh
  have hmain : limsup a atTop ≤ limsup q atTop := by
    apply (limsup_le_iff hac hab).mpr
    intro u hu
    have hqt := eventually_lt_of_limsup_lt
      (show limsup q atTop < limsup q atTop+(u-limsup q atTop)/3 by linarith) hqb
    have hmt := hm.eventually (lt_mem_nhds (show 1-(u-limsup q atTop)/3 < (1:ℝ) by linarith))
    filter_upwards [hqt,hmt] with i hi hi'
    have hb := successfulAverage_comparison ν hue ℓ (signed_direction_unit e) htrans (H i)
      (MedianTubeFailure ℓ f b (H i) (z i)) (measurableSet_medianTubeFailure ℓ f b (H i) (z i))
    change a i ≤ q i+1-(η i).real Set.univ at hb
    linarith
  exact hmain.trans (quenchedConditioned_tube_transfer ν hue e f htrans b H z hz)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma conditioned_median_tube_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (e f : Direction d) (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ) {z : ℝ} (hz : 0 < z) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    p^2/2 * (conditionedLaw ν ℓ).real
      (MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z) ≤
      5*(H:ℝ)/fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) z := by
  dsimp only
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have he : MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H z =ᵐ[conditionedLaw ν ℓ]
      {X | ∃ j, 0 < j ∧ j ≤ H ∧ z < |signedCoordinate f (recordIndexPosition ℓ j X)-(recordMedian ν ℓ hp f j:ℝ)|} := by
    filter_upwards [(conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν)] with X hX
    apply propext
    constructor
    · rintro ⟨j,hj,hbad⟩
      have hj0 : 0 < j := by
        by_contra hn
        have hjz : j = 0 := by omega
        simp [hjz,recordIndexPosition,recordIndexTime_zero,hX,recordMedian_zero,signedCoordinate] at hbad
        linarith
      exact ⟨j,hj0,hj,hbad⟩
    · rintro ⟨j,_,hj,hbad⟩
      exact ⟨j,hj,hbad⟩
  rw [measureReal_congr he]
  exact conditioned_median_max_bound ν ℓ htrans (signedHeight e) (signedHeight_projection e)
    (signedHeight_step_le e) f H hz

lemma conditioned_median_tube_short_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {r c t : ℝ} (hr : 0 < r) (hc : 0 < c) (hc1 : c ≤ 1) (ht : 0 ≤ t)
    (H : ℕ) (hH : (H:ℝ) ≤ t*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    (conditionedLaw ν ℓ).real (MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H (c*r)) ≤
      10*t/(p^2*c^2) := by
  dsimp only
  let ℓ := realPosition (step e)
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  have hs := measurable_commonIncrementProcess ℓ f 0
  have hne := independent_commonWordIncrement_nonzero ν hue e f hef htrans
  have hnr : 0 < fluctuationScale μ S r := div_pos (sq_pos_of_pos hr) (truncatedVariance_pos μ S hs hne hr)
  have hnc : 0 < fluctuationScale μ S (c*r) := div_pos (sq_pos_of_pos (mul_pos hc hr))
    (truncatedVariance_pos μ S hs hne (mul_pos hc hr))
  have hsc := fluctuationScale_scaling μ S hs hne hr hc hc1
  have hb := conditioned_median_tube_bound ν e f htrans H (mul_pos hc hr)
  have hfrac : 5*(H:ℝ)/fluctuationScale μ S (c*r) ≤ 5*t/c^2 := by
    apply (div_le_iff₀ hnc).mpr
    have hh := mul_le_mul_of_nonneg_left hsc (show 0 ≤ 5*t/c^2 by positivity)
    have heq : (5*t/c^2)*(c^2*fluctuationScale μ S r) = 5*t*fluctuationScale μ S r := by field_simp
    rw [heq] at hh
    nlinarith
  have hh := hb.trans hfrac
  have hd : 0 < p^2/2 := by positivity
  have heq : 5*t/c^2 = (p^2/2)*(10*t/(p^2*c^2)) := by field_simp; ring
  rw [heq] at hh
  exact (mul_le_mul_iff_right₀ hd).mp hh

theorem quenched_median_tube_short_uniform {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 10) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      ∀ H : ℕ, (H:ℝ) ≤ t*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      let ℓ := realPosition (step e)
      let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
      (quenchedConditionedAverage ν ℓ).real
        (MedianTubeFailure ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) H (w*r)) ≤ C*t := by
  let ℓ := realPosition (step e)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let C := 100/(p^2*(w/10)^2)
  have hC : 0 < C := by dsimp [C]; positivity
  let μ := quenchedConditionedAverage ν ℓ
  let : IsProbabilityMeasure μ := quenchedConditionedAverage_probability ν hue ℓ (signed_direction_unit e) htrans
  let n := fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0)
  let b := fun j => (recordMedian ν ℓ hp f j:ℝ)
  refine ⟨2*C,by positivity,?_⟩
  intro t ht
  by_contra hn
  push Not at hn
  have hbad (i : ℕ) : ∃ r : ℝ, (max (i:ℝ) 1) ≤ r ∧ ∃ H : ℕ, (H:ℝ) ≤ t*n r ∧
      2*C*t < μ.real (MedianTubeFailure ℓ f b H (w*r)) := by
    obtain ⟨r,hr,H,hH,hbad⟩ := hn (max (i:ℝ) 1) (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
    exact ⟨r,hr,H,hH,lt_of_not_ge hbad⟩
  choose r hr H hH hbad using hbad
  have hrpos (i : ℕ) : 0 < r i := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans (hr i))
  have hrinf : Tendsto r atTop atTop := tendsto_atTop_mono (fun i => (le_max_left _ _).trans (hr i)) tendsto_natCast_atTop_atTop
  let q := fun i => (conditionedLaw ν ℓ).real (MedianTubeFailure ℓ f b (H i) ((w*r i)/10))
  let a := fun i => μ.real (MedianTubeFailure ℓ f b (H i) (w*r i))
  have hqb : ∀ i, q i ≤ 10*t/(p^2*(w/10)^2) := by
    intro i
    have hh := conditioned_median_tube_short_bound ν hue e f hef htrans (hrpos i)
      (show 0 < w/10 by positivity) (show w/10 ≤ 1 by linarith) ht.le (H i) (hH i)
    simpa only [show w/10*r i = w*r i/10 by ring] using hh
  have hqc : IsCoboundedUnder (· ≤ ·) atTop q :=
    (show IsBoundedUnder (· ≥ ·) atTop q from ⟨0,
      (show ∀ᶠ i in atTop, 0 ≤ q i from Eventually.of_forall fun _ => measureReal_nonneg)⟩).isCoboundedUnder_le
  have hlimq := limsup_le_of_le hqc (Eventually.of_forall hqb)
  have htransfer := quenchedConditioned_tube_transfer ν hue e f htrans b H (fun i => w*r i) (hrinf.const_mul_atTop hw)
  have hlim : limsup a atTop ≤ C*t := by
    have hh := htransfer.trans (mul_le_mul_of_nonneg_left hlimq (by norm_num : (0:ℝ) ≤ 10))
    have heq : 10*(10*t/(p^2*(w/10)^2)) = C*t := by dsimp [C]; ring
    rwa [heq] at hh
  have hab : IsBoundedUnder (· ≤ ·) atTop a := ⟨1,
    (show ∀ᶠ i in atTop, a i ≤ 1 from Eventually.of_forall fun _ => measureReal_le_one)⟩
  have hlo : 2*C*t ≤ limsup a atTop := le_limsup_of_frequently_le
    (Frequently.of_forall fun i => (hbad i).le) hab
  nlinarith

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
