import Mathlib
import OAI.Probability.Ballisticity.Estimates.ClippingTime
import OAI.Probability.Ballisticity.Renewal.ClippingPositiveNumbers
import OAI.Probability.Ballisticity.Estimates.SmallScaleTailMoment

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience
lemma positive_scale_moment_arithmetic {V z r s ρ A bad tail ζ t : ℝ}
    (hr : 0 < r) (hz : 0 < z) (hζ : 0 < ζ) (hA : 0 < A)
    (hρ : ρ^2 ≤ ζ) (hbad : bad < ζ/A^2) (htail : tail < ζ)
    (hV : V ≤ (ρ*z)^2+(A*z)^2*bad+2*(z^2*tail))
    (hs : s^2 ≤ t) (hsz : z=s*r) : V/r^2 ≤ 4*ζ*t := by
  have hba := (lt_div_iff₀ (sq_pos_of_pos hA)).mp hbad
  have ht' := mul_lt_mul_of_pos_left htail (sq_pos_of_pos hz)
  have hρ' := mul_le_mul_of_nonneg_left hρ (sq_nonneg z)
  have hba' := mul_lt_mul_of_pos_left hba (sq_pos_of_pos hz)
  have hVz : V ≤ z^2*(4*ζ) := by nlinarith only [hV,ht',hρ',hba']
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  have hh := mul_le_mul_of_nonneg_right hs (show 0 ≤ r^2*(4*ζ) by positivity)
  rw [hsz] at hVz
  nlinarith only [hVz,hh]

lemma curve_positive_scale {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (hp : annealedLaw ν (NoDrop (realPosition (step e)) 0) ≠ 0)
    {r s b A ρ t C D M η ε : ℝ} (hr : 0 < r) (hs : 0 < s) (hb : 0 < b)
    (hA : 0 < A) (hρ : 0 < ρ) (ht : 0 < t) (hC : 0 < C) (hD : 0 < D)
    (hM : 0 < M) (hη : 0 < η) (hε : 0 < ε)
    (hbη : b < η/8) (hAs : A*s < b) (hst : s^2 ≤ t)
    (hρsq : ρ^2 ≤ ε*η^2/(1024*M)) (hCs : C*Real.sqrt t ≤ η/8)
    (hDt : 2*D*M*t ≤ ε/16)
    {H K J : ℕ} (hH : 0 < H) (hK : 0 < K) (hKJ : K ≤ J*H) (hJt : (J:ℝ)*t ≤ M)
    {δ α : ℝ≥0∞} (hδ : 0 < δ) (hα : 0 < α) (hδ1 : δ ≤ 1) (hα1 : α ≤ 1)
    (hline : ∀ j ≤ H, |(recordMedian ν (realPosition (step e)) hp f j:ℝ)-
      (j:ℝ)*(recordMedian ν (realPosition (step e)) hp f H:ℝ)/H| ≤ C*Real.sqrt t*r)
    (hfail : (environmentLaw ν).real {ω | curveIncrement (realPosition (step e)) f 0
      (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ)) (b*r) H ω Set.univ < δ} ≤ D*t^2)
    (hbad : (environmentLaw ν).real {ω | ¬ α*crossingQuenched (realPosition (step e)) 0 H ω ≤
      curveIncrement (realPosition (step e)) f 0 (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ))
        (b*r) H ω {u | |signedCoordinate f u-(recordMedian ν (realPosition (step e)) hp f H:ℝ)| ≤ ρ*(s*r)}} <
      (ε*η^2/(1024*M))/A^2)
    (htail : cappedTailMoment (successfulAverage ν (realPosition (step e)) H)
      (fun X => medianDeviation (realPosition (step e)) f
        (fun j => (recordMedian ν (realPosition (step e)) hp f j:ℝ)) H X/(s*r)) A (b/s) < ε*η^2/(1024*M)) :
    ∃ θ : ℝ, (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix (realPosition (step e)) f 0 θ (η*r) K) < (α*δ)^J/2} < ε := by
  let ℓ := realPosition (step e)
  let med := fun a => (recordMedian ν ℓ hp f a:ℝ)
  let dum := medianDummy e f H (recordMedian ν ℓ hp f H)
  have hdh : signedHeight e dum=H := medianDummy_height e f hef _ _
  have hdb : signedCoordinate f dum=med H := medianDummy_coordinate e f hef _ _
  let E := {u : Lattice d | |signedCoordinate f u-med H| ≤ ρ*(s*r)}
  let υ := curvePolicy_average ν ℓ f med (b*r) hH E hδ hα dum
  let θ := (∫ u, signedCoordinate f u ∂υ.toMeasure)/(H:ℝ)
  refine ⟨θ,?_⟩
  have hprob := curvePolicy_real_tube_probability ν e f med (mul_nonneg hb.le hr.le)
    (by positivity : 0 ≤ C*Real.sqrt t*r) hH (by positivity : 0 < η*r/2)
    hline E hδ hα hδ1 hα1 dum hdh hdb J hK hKJ
  have hwidth : η*r/2+2*(b*r)+C*Real.sqrt t*r ≤ η*r := by
    have hh := mul_le_mul_of_nonneg_right hCs hr.le
    have hb' := mul_lt_mul_of_pos_right hbη hr
    nlinarith only [hh,hb',mul_pos hη hr]
  have hlow : (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r) K) < (α*δ)^J/2} ≤
      (environmentLaw ν).real {ω | quenchedKernel (ω,0)
      (TubePrefix ℓ f 0 θ (η*r/2+2*(b*r)+C*Real.sqrt t*r) K) < (α*δ)^J/2} := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hω
    exact (measure_mono (tubePrefix_mono_width ℓ f 0 θ hwidth _)).trans_lt hω
  have hzn : 0 < s*r := mul_pos hs hr
  have hAB : A*(s*r) < b*r := by nlinarith only [mul_lt_mul_of_pos_right hAs hr]
  have hm := curvePolicy_average_moment ν hue e f htrans med (mul_nonneg hA.le hzn.le) hAB
    (mul_nonneg hρ.le hzn.le) hH hδ hα dum hdb
  have hdsc := cappedTailMoment_descaled (successfulAverage ν ℓ H)
    (fun X => medianDeviation ℓ f med H X) (r:=s*r) (A:=A) (B:=b/s) hzn
  have hbz : (b/s)*(s*r)=b*r := by field_simp
  rw [hbz] at hdsc
  dsimp only at hm
  rw [hdsc] at hm
  have hV := positive_scale_moment_arithmetic hr hzn (show 0 < ε*η^2/(1024*M) by positivity)
    hA hρsq hbad htail hm hst rfl
  exact (hlow.trans hprob).trans_lt (clipping_error_bound (show (0:ℝ)≤J by positivity)
    hD.le hM ht hr hη hε hJt hfail hDt hV)
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

theorem clipping_positive_profile {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrinf : Tendsto r atTop atTop)
    (F : ℕ → ℝ) {F₀ : ℝ} (hF₀ : 0 < F₀) (hF₀1 : F₀ ≤ 1)
    (hFle : ∀ j, F₀ ≤ F j) (hFlim : Tendsto F atTop (𝓝 F₀))
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
  let μ := independentConditionedPairLaw ν ℓ
  let S := commonIncrementProcess ℓ f 0
  let : IsProbabilityMeasure μ := independentConditionedPairLaw_probability ν ℓ hp
  let K := 16000/p^2
  have hK : 0 < K := by dsimp [K]; positivity
  let M := 8*T+1
  have hM : 0 < M := by dsimp [M]; linarith
  let ζ := ε*η^2/(1024*M)
  have hζ : 0 < ζ := by dsimp [ζ]; positivity
  let ρ := Real.sqrt ζ/2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρsq : ρ^2 ≤ ζ := by
    have hh := Real.sq_sqrt hζ.le
    dsimp [ρ]
    nlinarith only [hh,hζ.le]
  obtain ⟨A,hA,hAK⟩ := exists_large_tail_cut hK hζ
  obtain ⟨B,hBF,hBb⟩ := (((hFlim.div_const F₀).sub_const 1).eventually
    (gt_mem_nhds (show F₀/F₀-1 < ζ/(128*K) by rw [div_self hF₀.ne',sub_self]; positivity))).and
    (dyadicCut_tendsto.eventually (gt_mem_nhds (by positivity : 0 < η/8))) |>.exists
  let b := dyadicCut B
  have hb : 0 < b := dyadicCut_pos B
  have hbη : b < η/8 := hBb
  have hBK : K*(16*(F B/F₀-1)) < ζ/8 := by
    have hh := (lt_div_iff₀ (show 0 < 128*K by positivity)).mp hBF
    nlinarith only [hh]
  obtain ⟨C,hC,t₁,ht₁,hmed⟩ := recordMedian_shortBlock ν hue e f hef htrans
  obtain ⟨D,hD,t₀,ht₀,hfail⟩ := curveIncrement_short_block ν hue e f hef htrans hb
  obtain ⟨τ,hτ,hτ₀,hτ₁,hτ1,hCs,hDt⟩ := exists_clipping_time ht₀ ht₁ hC hD hM hη hε
  obtain ⟨cα,hcα,hGaussian⟩ := small_scale_gaussian_mass ν hue e f hef htrans hρ
  let α := min cα 1
  have hα : 0 < α := lt_min hcα zero_lt_one
  have hα1 : α ≤ 1 := min_le_right _ _
  have hαc : α ≤ cα := min_le_left _ _
  have htail := small_scale_tail_moment ν hue e f hef htrans r hr hrinf F hF₀ hFle hFlim hF
    hA B (show 0 < ζ/4 by positivity)
  have hgauss := hGaussian r hr hrinf F F₀ hF₀ hFle hFlim hF b hb 0 (ζ/A^2) (by positivity)
  have htlim : Tendsto (fun j => 2*(dyadicCut j)^2/F₀) atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : 2 ≠ 0),mul_zero,zero_div] using ((dyadicCut_tendsto.pow 2).const_mul 2).div_const F₀
  obtain ⟨j,hjtail,hjgauss,hjt,hjF,hjA⟩ := (htail.and (hgauss.and
    ((htlim.eventually (gt_mem_nhds hτ)).and ((hFlim.eventually (gt_mem_nhds (by linarith : F₀ < 2*F₀))).and
      (dyadicCut_tendsto.eventually (gt_mem_nhds (div_pos hb hA))))))).exists
  let s := dyadicCut j
  have hs : 0 < s := dyadicCut_pos j
  let t := 2*s^2/F₀
  have ht : 0 < t := by dsimp [t]; positivity
  have htt : t ≤ τ := le_of_lt hjt
  have htt₀ : t ≤ t₀ := htt.trans hτ₀
  have htt₁ : t ≤ t₁ := htt.trans hτ₁
  have ht1 : t ≤ 1 := htt.trans hτ1
  have hCs' : C*Real.sqrt t ≤ η/8 := (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htt) hC.le).trans hCs
  have hDt' : 2*D*M*t ≤ ε/16 := (mul_le_mul_of_nonneg_left htt (by positivity)).trans hDt
  have hAs : A*s < b := by
    have hh := (lt_div_iff₀ hA).mp hjA
    simpa only [mul_comm] using hh
  obtain ⟨J,hJT,hJM⟩ := exists_block_count (show 0 < 4*T by positivity) ht ht1
  have hJt : (J:ℝ)*t ≤ M := by dsimp [M]; linarith
  obtain ⟨δ,hδ,hδ1,R,hR,hfail⟩ := hfail t ht htt₀
  let δe := ENNReal.ofReal δ
  let αe := ENNReal.ofReal α
  have hδe : 0 < δe := ENNReal.ofReal_pos.mpr hδ
  have hαe : 0 < αe := ENNReal.ofReal_pos.mpr hα
  have hδe1 : δe ≤ 1 := ENNReal.ofReal_le_one.mpr hδ1
  have hαe1 : αe ≤ 1 := ENNReal.ofReal_le_one.mpr hα1
  let c := (αe*δe)^J/2
  have hc : 0 < c := ENNReal.div_pos (pow_ne_zero _ (mul_ne_zero hαe.ne' hδe.ne')) (by norm_num)
  have hc1 : c ≤ 1 := by
    apply (ENNReal.div_le_iff (by norm_num : (2:ℝ≥0∞) ≠ 0) (by norm_num)).mpr
    exact (pow_le_one₀ (zero_le : (0:ℝ≥0∞) ≤ αe*δe)
      ((mul_le_of_le_one_left (zero_le : (0:ℝ≥0∞) ≤ δe) hαe1).trans hδe1)).trans (by norm_num)
  let N := fun n => fluctuationScale μ S (r n)
  let z := fun n => s*r n
  let Nz := fun n => fluctuationScale μ S (z n)
  let H := fun n => ⌊Nz n⌋₊
  have hN : Tendsto N atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans r hrinf
  have hz : ∀ n, 0 < z n := fun n => mul_pos hs (hr n)
  have hNz : Tendsto Nz atTop atTop := recordFluctuationScale_tendsto ν hue e f hef htrans z (hrinf.const_mul_atTop hs)
  have hH : Tendsto H atTop atTop := tendsto_nat_floor_atTop.comp hNz
  have hratio := profile_scale_ratio μ S (measurable_commonIncrementProcess ℓ f 0)
    (independent_commonWordIncrement_nonzero ν hue e f hef htrans) r hr hs (hF₀.trans_le (hFle j)) (hF j)
  have hrt : s^2/F j < t := calc
    _ ≤ s^2/F₀ := div_le_div_of_nonneg_left (sq_nonneg s) hF₀ (hFle j)
    _ < 2*(s^2/F₀) := by linarith only [show 0 < s^2/F₀ by positivity]
    _ = t := by dsimp [t]; ring
  have hlr : t/4 < s^2/F j := by
    have hh := div_lt_div_of_pos_left (sq_pos_of_pos hs) (hF₀.trans_le (hFle j)) hjF
    have he : t/4=s^2/(2*F₀) := by dsimp [t]; ring
    rw [he]
    exact hh
  have hbounds : ∀ᶠ n in atTop, 0 < H n ∧ (H n:ℝ) ≤ t*N n ∧ ⌈T*N n⌉₊ ≤ J*H n ∧ 0 < ⌈T*N n⌉₊ := by
    filter_upwards [hN.eventually (eventually_gt_atTop (0:ℝ)), hratio.eventually (Ioo_mem_nhds hlr hrt),
      eventually_ceil_horizon_covered N hN hT (show 0 < t/4 by positivity) J (by linarith)] with n hNn hn hc
    have hupper : Nz n ≤ t*N n := ((div_lt_iff₀ hNn).mp hn.2).le
    have hlower : t/4*N n ≤ Nz n := ((lt_div_iff₀ hNn).mp hn.1).le
    have hfloor : ⌊t/4*N n⌋₊ ≤ H n := Nat.floor_mono hlower
    exact ⟨hc.1.trans_le hfloor,(Nat.floor_le (fluctuationScale_nonneg μ S (z n))).trans hupper,
      hc.2.2.trans (Nat.mul_le_mul_left J hfloor),hc.2.1⟩
  let med := fun a => (recordMedian ν ℓ hp f a:ℝ)
  let Q := fun n => successfulAverage ν ℓ (H n)
  let W := fun n X => medianDeviation ℓ f med (H n) X
  let tail := fun n => cappedTailMoment (Q n) (fun X => W n X/z n) A (b/s)
  have htailBound : IsBoundedUnder (· ≤ ·) atTop tail := by
    apply isBoundedUnder_of
    refine ⟨(b/s)^2,fun n => ?_⟩
    let := successfulAverage_probability ν hue ℓ (signed_direction_unit e) htrans (H n)
    exact (cappedTailMoment_bounds (Q n) _ ((measurable_medianDeviation ℓ f med (H n)).div_const (z n))
      (fun X => div_nonneg (medianDeviation_nonneg ℓ f med (H n) X) (hz n).le) A (div_pos hb hs)).2
  have htailSmall : limsup tail atTop < ζ := by
    have hh : limsup tail atTop ≤ K*(2048/(A/40)^2+16*(F B/F₀-1))+ζ/4 := hjtail
    nlinarith only [hh,hAK,hBK,hζ]
  have htailEv := eventually_lt_of_limsup_lt htailSmall htailBound
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [htailEv,hjgauss,hbounds,hrinf.eventually (eventually_ge_atTop R)] with n htn hgn hbds hrR
  have hrn := hr n
  have hzn := hz n
  have hHn : 0 < H n := hbds.1
  have hline := hmed t ht htt₁ (r n) hrn (H n) hHn hbds.2.1
  have hbad := (curveGaussian_failure_le ν hue e f htrans hp hHn (b*r n) (ρ*z n) hα hαc).trans_lt hgn
  have hs2 : s^2 ≤ t := by
    dsimp [t]
    apply (le_div_iff₀ hF₀).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hF₀1 (sq_nonneg s),sq_nonneg s]
  exact curve_positive_scale ν hue e f hef htrans hp hrn hs hb hA hρ ht hC hD hM hη hε
    hbη hAs hs2 hρsq hCs' hDt' hHn hbds.2.2.2 hbds.2.2.1 hJt hδe hαe hδe1 hαe1
    hline (hfail (r n) hrR (H n) hHn hbds.2.1) hbad htn
end DirectionalTransience

end

end

end OAI
