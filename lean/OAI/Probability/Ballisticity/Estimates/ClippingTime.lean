import Mathlib
import OAI.Probability.Ballisticity.Geometry.TubeHeightMono
import OAI.Probability.Ballisticity.Estimates.ScaledMaxMoment

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma exists_clipping_time {a b C D M η ε : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C) (hD : 0 < D)
    (hM : 0 < M) (hη : 0 < η) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t ≤ a ∧ t ≤ b ∧ t ≤ 1 ∧
      C*Real.sqrt t ≤ η/8 ∧ 2*D*M*t ≤ ε/16 := by
  let t := min a (min b (min 1 (min ((η/(8*C))^2) (ε/(32*D*M)))))
  have ht : 0 < t := by dsimp [t]; positivity
  have hta : t ≤ a := min_le_left _ _
  have htb : t ≤ b := (min_le_right _ _).trans (min_le_left _ _)
  have ht1 : t ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have htc : t ≤ (η/(8*C))^2 := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hte : t ≤ ε/(32*D*M) := (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨t,ht,hta,htb,ht1,?_,?_⟩
  · have hh : Real.sqrt t ≤ η/(8*C) := (Real.sqrt_le_iff).mpr ⟨by positivity,htc⟩
    have hh := (le_div_iff₀ (by positivity : 0 < 8*C)).mp hh
    nlinarith
  · have hh := (le_div_iff₀ (by positivity : 0 < 32*D*M)).mp hte
    nlinarith
end DirectionalTransience

end

section

open MeasureTheory Filter
namespace DirectionalTransience
lemma clipping_error_bound {J D M t r η ε V B : ℝ}
    (hJ : 0 ≤ J) (hD : 0 ≤ D) (hM : 0 < M) (ht : 0 < t) (hr : 0 < r)
    (hη : 0 < η) (hε : 0 < ε) (hJt : J*t ≤ M)
    (hfail : B ≤ D*t^2) (hsmall : 2*D*M*t ≤ ε/16)
    (hV : V/r^2 ≤ 4*(ε*η^2/(1024*M))*t) :
    2*(J*B+(4*J*V)/(η*r/2)^2) < ε := by
  have h1 : 2*J*B ≤ ε/16 := calc
    _ ≤ 2*J*(D*t^2) := mul_le_mul_of_nonneg_left hfail (by positivity)
    _ = 2*D*(J*t)*t := by ring
    _ ≤ 2*D*M*t := by gcongr
    _ ≤ _ := hsmall
  have h2 : 32*J*(V/r^2)/η^2 ≤ ε/8 := calc
    _ ≤ 32*J*(4*(ε*η^2/(1024*M))*t)/η^2 := by gcongr
    _ = (ε/(8*M))*(J*t) := by field_simp; ring
    _ ≤ (ε/(8*M))*M := mul_le_mul_of_nonneg_left hJt (by positivity)
    _ = ε/8 := by field_simp
  have he : 2*(J*B+4*J*V/(η*r/2)^2)=2*J*B+32*J*(V/r^2)/η^2 := by
    field_simp
    ring
  rw [he]
  linarith
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

theorem clipping_zero_profile {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrinf : Tendsto r atTop atTop)
    (F : ℕ → ℝ) (hFlim : Tendsto F atTop (𝓝 0))
    (hF : ∀ j, Tendsto (fun n => truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (dyadicCut j*r n)/
      truncatedVariance (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r n)) atTop (𝓝 (F j)))
    {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∀ᶠ n in atTop, ∃ θ : ℝ,
      (environmentLaw ν).real {ω | quenchedKernel (ω,0)
        (TubePrefix (realPosition (step e)) f 0 θ (η*r n)
          ⌈T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
            (commonIncrementProcess (realPosition (step e)) f 0) (r n)⌉₊) < c} < ε := by
  let ℓ := realPosition (step e)
  let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
  have hp0 : 0 < p := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let K := 40000/p^2
  have hK : 0 < K := by dsimp [K]; positivity
  let M := 2*T+1
  have hM : 0 < M := by dsimp [M]; linarith
  let ζ := ε*η^2/(1024*M)
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  obtain ⟨j,hjF,hjb⟩ := ((hFlim.eventually (gt_mem_nhds (div_pos hζ hK))).and
    (dyadicCut_tendsto.eventually (gt_mem_nhds (by positivity : 0 < η/8)))).exists
  let b := dyadicCut j
  have hb : 0 < b := dyadicCut_pos j
  have hbη : b < η/8 := hjb
  have hKF : K*F j < ζ := by
    have hh := (lt_div_iff₀ hK).mp hjF
    simpa only [mul_comm] using hh
  obtain ⟨C,hC,t₁,ht₁,hmed⟩ := recordMedian_shortBlock ν hue e f hef htrans
  obtain ⟨D,hD,t₀,ht₀,hfail⟩ := curveIncrement_short_block ν hue e f hef htrans hb
  obtain ⟨t,ht,htt₀,htt₁,ht1,hCs,hDt⟩ :=
    exists_clipping_time ht₀ ht₁ hC hD hM hη hε
  obtain ⟨J,hJT,hJM⟩ := exists_block_count hT ht ht1
  obtain ⟨δ,hδ,hδ1,R,hR,hfail⟩ := hfail t ht htt₀
  let δe := ENNReal.ofReal δ
  have hδe : 0 < δe := ENNReal.ofReal_pos.mpr hδ
  have hδe1 : δe ≤ 1 := ENNReal.ofReal_le_one.mpr hδ1
  let c := δe^J/2
  have hc : 0 < c := ENNReal.div_pos (pow_ne_zero _ hδe.ne') (by norm_num)
  have hc1 : c ≤ 1 := by
    apply (ENNReal.div_le_iff (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num)).mpr
    exact (pow_le_one₀ (zero_le : (0:ℝ≥0∞) ≤ δe) hδe1).trans (by norm_num)
  let N := fun n => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r n)
  have hN : Tendsto N atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hrinf
  let H := fun n => ⌊t*N n⌋₊
  have hH : Tendsto H atTop atTop := tendsto_nat_floor_atTop.comp (hN.const_mul_atTop ht)
  have hHt : ∀ᶠ n in atTop, (H n:ℝ) ≤ t*N n := by
    filter_upwards [hN.eventually (eventually_ge_atTop (0:ℝ))] with n hn
    exact Nat.floor_le (mul_nonneg ht.le hn)
  let med := fun a => (recordMedian ν ℓ hp f a:ℝ)
  let Q := fun n => successfulAverage ν ℓ (H n)
  let W := fun n X => medianDeviation ℓ f med (H n) X
  let a := fun n => cappedMoment (Q n) (fun X => W n X/r n) b
  have ha : limsup a atTop ≤ K*t*F j := successful_small_variance_bound ν hue e f hef htrans
    r hr hrinf H hH hb hHt (hF j)
  have hab : IsBoundedUnder (· ≤ ·) atTop a := by
    apply isBoundedUnder_of
    refine ⟨b^2,fun n => ?_⟩
    let := successfulAverage_probability ν hue ℓ (signed_direction_unit e) htrans (H n)
    exact (cappedMoment_bounds (Q n) _ ((measurable_medianDeviation ℓ f med (H n)).div_const (r n))
      (fun X => div_nonneg (medianDeviation_nonneg ℓ f med (H n) X) (hr n).le) hb).2
  have hal : limsup a atTop < 2*ζ*t := by
    have hh := mul_lt_mul_of_pos_right hKF ht
    nlinarith
  have hae := eventually_lt_of_limsup_lt hal hab
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [hae,hHt,eventually_ceil_horizon_covered N hN hT ht J hJT,
    hrinf.eventually (eventually_ge_atTop R)] with n han hhn hcover hrR
  have hrn := hr n
  have hHn : 0 < H n := hcover.1
  let dum := medianDummy e f (H n) (recordMedian ν ℓ hp f (H n))
  have hdh : signedHeight e dum=H n := medianDummy_height e f hef _ _
  have hdb : signedCoordinate f dum=med (H n) := medianDummy_coordinate e f hef _ _
  let E := {u : Lattice d | |signedCoordinate f u-med (H n)| ≤ 0}
  let μ := curvePolicy_average ν ℓ f med (b*r n) hHn E hδe (by norm_num : (0:ℝ≥0∞)<1) dum
  let θ := (∫ u, signedCoordinate f u ∂μ.toMeasure)/(H n:ℝ)
  refine ⟨θ,?_⟩
  have hline := hmed t ht htt₁ (r n) (hr n) (H n) hHn hhn
  have hprob := curvePolicy_real_tube_probability ν e f med (mul_nonneg hb.le (hr n).le)
    (by positivity : 0 ≤ C*Real.sqrt t*r n) hHn (by positivity : 0 < η*r n/2)
    hline E hδe (by norm_num : (0:ℝ≥0∞)<1) hδe1 (by norm_num : (1:ℝ≥0∞)≤1)
    dum hdh hdb J hcover.2.1 hcover.2.2
  have hwidth : η*r n/2+2*(b*r n)+C*Real.sqrt t*r n ≤ η*r n := by
    have hh := mul_le_mul_of_nonneg_right hCs (hr n).le
    have hb' := mul_lt_mul_of_pos_right hbη (hr n)
    nlinarith
  have hlow : (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r n) ⌈T*N n⌉₊) < c} ≤
      (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r n/2+2*(b*r n)+C*Real.sqrt t*r n) ⌈T*N n⌉₊) < c} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    exact (measure_mono (tubePrefix_mono_width ℓ f 0 θ hwidth _)).trans_lt hω
  have hm := curvePolicy_average_zero_moment ν hue e f htrans med (mul_pos hb (hr n)) hHn
    hδe (by norm_num : (0:ℝ≥0∞)<1) dum hdb
  have hdsc := cappedMoment_descaled (Q n) (W n) (r:=r n) (B:=b) (hr n)
  have hV : (∫ u, (signedCoordinate f u-med (H n))^2 ∂μ.toMeasure)/(r n)^2 ≤ 4*ζ*t := by
    have hh : (∫ u, (signedCoordinate f u-med (H n))^2 ∂μ.toMeasure) ≤ 2*((r n)^2*a n) := by
      change _ ≤ 2*((r n)^2*cappedMoment (Q n) (fun X => W n X/r n) b)
      rw [←hdsc]
      exact hm
    apply (div_le_iff₀ (sq_pos_of_pos (hr n))).mpr
    have hhan := mul_le_mul_of_nonneg_left han.le (sq_nonneg (r n))
    nlinarith
  have hf := hfail (r n) hrR (H n) hHn hhn
  have he := clipping_error_bound (show (0:ℝ)≤J by positivity) hD.le hM ht (hr n) hη hε
    hJM hf hDt hV
  have hprob' : (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r n/2+2*(b*r n)+C*Real.sqrt t*r n) ⌈T*N n⌉₊) < c} ≤
      2*((J:ℝ)*(environmentLaw ν).real {ω | curveIncrement ℓ f 0 med (b*r n) (H n) ω Set.univ < δe}+
        (4*(J:ℝ)*(∫ u, (signedCoordinate f u-med (H n))^2 ∂μ.toMeasure))/(η*r n/2)^2) := by
    simpa only [one_mul] using hprob
  exact hlow.trans hprob' |>.trans_lt he
end DirectionalTransience

end

end

end OAI
