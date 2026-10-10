import Mathlib
import OAI.Probability.SLELocalization.StoppedIto
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Loewner Field estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SLEExactGauge.LoewnerField
open LoewnerCutoff GreenPhysical
open scoped unitInterval
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)

lemma height_pos (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : 0 < height hε hT U z t :=
  hε.trans_le (le_max_left _ _)

lemma smooth (p a sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t : ℝ) :
    ContDiff ℝ 3 (field hε hT p a sdev U z t) :=
  contDiff_green_driver p a _ _ _ sdev (height_pos hε hT U z t)

lemma continuous_field (p a sdev : ℝ) (z : ℂ) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => field hε hT p a sdev q.1.1 z q.1.2 q.2) := by
  have hH := (continuous_position hε hT z).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hL := (continuous_logDerivative hε hT z).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  apply continuous_green_comp p a
  · exact (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd)
  · exact continuous_const.max (Complex.continuous_im.comp hH)
  · exact hL
  · intro q
    exact height_pos hε hT q.1.1 z q.1.2

lemma continuous_drift (p a sdev : ℝ) (z : ℂ) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => drift hε hT p a sdev q.1.1 z q.1.2 q.2) := by
  have hH := (continuous_position hε hT z).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hD := (continuous_joint_extendDriver T).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hV := (continuous_velocity hε).comp (hD.prodMk hH)
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => sdev*q.2))
  have hy : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => height hε hT q.1.1 z q.1.2) :=
    continuous_const.max (Complex.continuous_im.comp hH)
  have hv := (continuous_variation hε hT z).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  unfold drift
  apply (continuous_field hε hT p a sdev z).mul
  apply Continuous.sub
  · exact (continuous_const.mul hv).add
      ((continuous_const.mul (Complex.continuous_im.comp hV)).div hy
        (fun q => (height_pos hε hT q.1.1 z q.1.2).ne'))
  · exact (continuous_const.mul ((hx.mul (Complex.continuous_re.comp hV)).add
      (hy.mul (Complex.continuous_im.comp hV)))).div ((hx.pow 2).add (hy.pow 2))
        (fun q => (q_pos _ (height_pos hε hT q.1.1 z q.1.2)).ne')

lemma field_upper (p a sdev : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a)
    (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) :
    field hε hT p a sdev U z t b ≤ (2*ε/Real.exp ((2/ε^2)*T))^(-p) := by
  apply green_le_fixed_radius p a _ _ _ _ (height_pos hε hT U z t) ha hp (by positivity)
  have hL : Real.exp (logDerivative hε hT U z t) ≤ Real.exp ((2/ε^2)*T) :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_logDerivative_le hε hT U z t))
  calc
    2*ε / Real.exp ((2/ε^2)*T) ≤ 2*ε / Real.exp (logDerivative hε hT U z t) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hL
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
      (Real.exp_pos _).le

lemma field_third_bound (p a sdev : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a)
    (U : C(I, ℝ)) (z : ℂ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t b, |iteratedDeriv 3 (field hε hT p a sdev U z t) b| ≤ K := by
  let M := (2*ε/Real.exp ((2/ε^2)*T))^(-p)
  refine ⟨|sdev|^3 * (M*(a*(a+2)*(a+4))/ε^3), by positivity, ?_⟩
  intro t b
  change |iteratedDeriv 3 (fun b => green p a ((position hε hT U z t).re-sdev*b)
    (height hε hT U z t) (logDerivative hε hT U z t)) b| ≤ _
  rw [iteratedDeriv_green_driver p a _ _ _ sdev (height_pos hε hT U z t) 3 b,
    abs_mul, abs_pow, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact third_green_bound hε (le_max_left _ _) ha (field_upper hε hT p a sdev hp ha U z t b)

lemma time_deriv (p a sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) {t : ℝ}
    (ht : t ∈ Ioo 0 T) (hy : ε < (position hε hT U z t).im) (b : ℝ) :
    HasDerivAt (fun s => field hε hT p a sdev U z s b) (drift hε hT p a sdev U z t b) t := by
  have hH := position_deriv hε hT U z ht
  have hL := hasDerivAt_logDerivative hε hT U z ht
  have hIm := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hH
  have hRe := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hH
  dsimp only [Function.comp_def, Complex.imCLM_apply, Complex.reCLM_apply] at hIm hRe
  have hY : HasDerivAt (height hε hT U z)
      (velocity ε (extendDriver T U t) (position hε hT U z t)).im t := by
    apply hIm.congr_of_eventuallyEq
    have hc := hIm.continuousAt
    filter_upwards [hc.preimage_mem_nhds (Ioi_mem_nhds hy)] with s hs
    exact max_eq_right hs.le
  exact hasDerivAt_green_path p a (hRe.sub_const (sdev*b)) hY hL (height_pos hε hT U z t)

lemma second_eq (p a sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) :
    iteratedDeriv 2 (field hε hT p a sdev U z t) b =
      sdev^2 * (field hε hT p a sdev U z t b *
        (a*(a+1)*((position hε hT U z t).re-sdev*b)^2 - a*(height hε hT U z t)^2) /
        (((position hε hT U z t).re-sdev*b)^2+(height hε hT U z t)^2)^2) := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, field]
  exact deriv_deriv_green_driver p a _ _ _ sdev b (height_pos hε hT U z t)

lemma continuous_second (p a sdev : ℝ) (z : ℂ) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => iteratedDeriv 2 (field hε hT p a sdev q.1.1 z q.1.2) q.2) := by
  simp only [second_eq]
  have hH := (continuous_position hε hT z).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => sdev*q.2))
  have hy : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => height hε hT q.1.1 z q.1.2) :=
    continuous_const.max (Complex.continuous_im.comp hH)
  apply continuous_const.mul
  apply Continuous.div
  · exact (continuous_field hε hT p a sdev z).mul
      ((continuous_const.mul (hx.pow 2)).sub (continuous_const.mul (hy.pow 2)))
  · exact ((hx.pow 2).add (hy.pow 2)).pow 2
  · exact fun q => pow_ne_zero 2 (q_pos _ (height_pos hε hT q.1.1 z q.1.2)).ne'

lemma first_eq (p a sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) :
    iteratedDeriv 1 (field hε hT p a sdev U z t) b =
      sdev*a*((position hε hT U z t).re-sdev*b) /
        (((position hε hT U z t).re-sdev*b)^2+(height hε hT U z t)^2) *
        field hε hT p a sdev U z t b := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, field]
  exact deriv_green_driver p a _ _ _ sdev b (height_pos hε hT U z t)

lemma continuous_first (p a sdev : ℝ) (z : ℂ) :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => iteratedDeriv 1 (field hε hT p a sdev q.1.1 z q.1.2) q.2) := by
  simp only [first_eq]
  have hH := (continuous_position hε hT z).comp (continuous_fst : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => q.1))
  have hx := (Complex.continuous_re.comp hH).sub (continuous_const.mul continuous_snd :
    Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => sdev*q.2))
  have hy : Continuous (fun q : (C(I, ℝ) × ℝ) × ℝ => height hε hT q.1.1 z q.1.2) :=
    continuous_const.max (Complex.continuous_im.comp hH)
  exact ((continuous_const.mul hx).div ((hx.pow 2).add (hy.pow 2))
    (fun q => (q_pos _ (height_pos hε hT q.1.1 z q.1.2)).ne')).mul
      (continuous_field hε hT p a sdev z)

lemma first_bound (p a sdev : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a)
    (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) :
    |iteratedDeriv 1 (field hε hT p a sdev U z t) b| ≤
      |sdev| * ((2*ε/Real.exp ((2/ε^2)*T))^(-p)*a/ε) := by
  change |iteratedDeriv 1 (fun b => green p a ((position hε hT U z t).re-sdev*b)
    (height hε hT U z t) (logDerivative hε hT U z t)) b| ≤ _
  rw [iteratedDeriv_green_driver p a _ _ _ sdev (height_pos hε hT U z t) 1 b,
    abs_mul, abs_pow, abs_neg, pow_one]
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  exact mul_le_mul_of_nonneg_left
    (first_green_bound hε (le_max_left _ _) ha (field_upper hε hT p a sdev hp ha U z t b))
    (abs_nonneg _)

lemma second_bound (p a sdev : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a)
    (U : C(I, ℝ)) (z : ℂ) (t b : ℝ) :
    |iteratedDeriv 2 (field hε hT p a sdev U z t) b| ≤
      |sdev|^2 * ((2*ε/Real.exp ((2/ε^2)*T))^(-p)*(a*(a+2))/ε^2) := by
  change |iteratedDeriv 2 (fun b => green p a ((position hε hT U z t).re-sdev*b)
    (height hε hT U z t) (logDerivative hε hT U z t)) b| ≤ _
  rw [iteratedDeriv_green_driver p a _ _ _ sdev (height_pos hε hT U z t) 2 b,
    abs_mul, abs_pow, abs_neg]
  exact mul_le_mul_of_nonneg_left
    (second_green_bound hε (le_max_left _ _) ha (field_upper hε hT p a sdev hp ha U z t b))
    (by positivity)

lemma variation_of_unclipped (U : C(I, ℝ)) (z : ℂ) (t : ℝ)
    (hy : ε ≤ (position hε hT U z t).im) :
    variation hε hT U z t =
      -2 * (((position hε hT U z t).re - extendDriver T U t)^2 - (position hε hT U z t).im^2) /
        (((position hε hT U z t).re - extendDriver T U t)^2 + (position hε hT U z t).im^2)^2 := by
  unfold variation
  rw [clampIm_eq (by simpa using hy)]
  simp only [Complex.div_re, Complex.neg_re, Complex.re_ofNat, Complex.neg_im,
    Complex.im_ofNat, neg_zero, zero_mul, map_pow]
  simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.normSq_apply]
  ring

lemma drift_cancellation (κ : ℝ) (hκ : 0 < κ) (U : C(I, ℝ)) (z : ℂ) (t b : ℝ)
    (hy : ε ≤ (position hε hT U z t).im)
    (hU : extendDriver T U t = Real.sqrt κ * b) :
    drift hε hT (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t b +
      (1/2 : ℝ) * iteratedDeriv 2 (field hε hT (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t) b = 0 := by
  have hypos := hε.trans_le hy
  have hh : height hε hT U z t = (position hε hT U z t).im := max_eq_right hy
  rw [second_eq, Real.sq_sqrt hκ.le]
  dsimp only [drift]
  rw [variation_of_unclipped hε hT U z t hy, velocity_eq hy,
    hh, hU]
  have hc := green_drift_cancellation κ
    ((position hε hT U z t).re-Real.sqrt κ*b) (position hε hT U z t).im
    (field hε hT (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t b) hκ.ne' hypos
  dsimp only at hc
  simp only [Complex.div_re, Complex.div_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
    sub_zero, zero_mul, Complex.normSq_apply] at *
  convert hc using 1
  ring

end SLEExactGauge.LoewnerField

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace SLEExactGauge.LoewnerField
open LoewnerCutoff
open scoped unitInterval

lemma field_prefix_eq {ε S T : ℝ} (hε : 0 < ε) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hST : S ≤ T) (U V : C(I, ℝ)) (z : ℂ) (p a sdev : ℝ)
    (hUV : EqOn (extendDriver S U) (extendDriver T V) (Icc 0 S))
    {t : ℝ} (ht : t ∈ Icc 0 S) :
    field hε hS p a sdev U z t = field hε hT p a sdev V z t := by
  have hH := position_prefix_eq hε hS hT hS le_rfl hST U V z hUV ht
  have hL := logDerivative_prefix_eq hε hS hT hS le_rfl hST U V z hUV ht
  funext b
  simp only [field, height, hH, hL]

end SLEExactGauge.LoewnerField

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.ContinuousExit

def extend (p : C(I, ℝ)) (t : ℝ) : ℝ := p (projIcc 0 1 zero_le_one t)

lemma continuous_extend (p : C(I, ℝ)) : Continuous (extend p) :=
  p.continuous.comp (continuous_projIcc (a := (0:ℝ)) (b := 1) (h := zero_le_one))

lemma extend_coe (p : C(I, ℝ)) (t : I) : extend p t = p t := by
  simp only [extend, projIcc, max_eq_right t.property.1, min_eq_right t.property.2]

def exitSet (p : C(I, ℝ)) : Set ℝ := insert 1 (Icc 0 1 ∩ {t | extend p t ≤ 0})

def time (p : C(I, ℝ)) : ℝ := sInf (exitSet p)

lemma exitSet_nonempty (p : C(I, ℝ)) : (exitSet p).Nonempty := ⟨1, mem_insert _ _⟩

lemma exitSet_subset (p : C(I, ℝ)) : exitSet p ⊆ Icc 0 1 := by
  rintro t (rfl | ht)
  · exact ⟨zero_le_one,le_rfl⟩
  · exact ht.1

lemma compact_exitSet (p : C(I, ℝ)) : IsCompact (exitSet p) := by
  exact (isCompact_Icc.inter_right (isClosed_le (continuous_extend p) continuous_const)).insert 1

lemma time_mem (p : C(I, ℝ)) : time p ∈ exitSet p :=
  (compact_exitSet p).sInf_mem (exitSet_nonempty p)

lemma time_bounds (p : C(I, ℝ)) : time p ∈ Icc 0 1 := exitSet_subset p (time_mem p)

lemma time_le_of_nonpos {p : C(I, ℝ)} {t : ℝ} (ht : t ∈ Icc 0 1) (hp : extend p t ≤ 0) :
    time p ≤ t := csInf_le ((compact_exitSet p).bddBelow) (mem_insert_of_mem 1 ⟨ht,hp⟩)

lemma positive_before {p : C(I, ℝ)} {t : ℝ} (ht : 0 ≤ t) (hτ : t < time p) :
    0 < extend p t := by
  by_contra hn
  exact (not_le_of_gt hτ) (time_le_of_nonpos ⟨ht,hτ.le.trans (time_bounds p).2⟩ (not_lt.1 hn))

lemma nonpos_at_of_lt_one {p : C(I, ℝ)} (hτ : time p < 1) : extend p (time p) ≤ 0 := by
  rcases time_mem p with h | h
  · exact (ne_of_lt hτ h).elim
  · exact h.2

lemma lt_time_iff {p : C(I, ℝ)} {t : ℝ} (ht : t ∈ Ico 0 1) :
    t < time p ↔ ∀ s ∈ Icc 0 t, 0 < extend p s := by
  constructor
  · intro h s hs
    exact positive_before hs.1 (hs.2.trans_lt h)
  · intro h
    by_contra hn
    have hτ : time p ≤ t := not_lt.1 hn
    have hp := h (time p) ⟨(time_bounds p).1,hτ⟩
    exact (not_lt_of_ge (nonpos_at_of_lt_one (hτ.trans_lt ht.2))) hp

lemma isOpen_positive_on (t : ℝ) :
    IsOpen {p : C(I, ℝ) | ∀ s ∈ Icc 0 t, 0 < extend p s} := by
  let S : Set (C(I, ℝ) × Icc 0 t) := {q | extend q.1 q.2 ≤ 0}
  have hc : IsClosed S := by
    apply isClosed_le ?_ continuous_const
    exact continuous_eval.comp (continuous_fst.prodMk
      ((continuous_projIcc (a := (0:ℝ)) (b := 1) (h := zero_le_one)).comp (continuous_subtype_val.comp continuous_snd)))
  have hh := isClosedMap_fst_of_compactSpace S hc
  have he : {p : C(I, ℝ) | ∀ s ∈ Icc 0 t, 0 < extend p s} = (Prod.fst '' S)ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, mem_image, S, not_exists, not_and]
    constructor
    · intro hp q hq hqp
      subst p
      exact (not_lt_of_ge hq) (hp q.2 q.2.property)
    · intro hp s hs
      by_contra hn
      exact hp (p,⟨s,hs⟩) (not_lt.1 hn) rfl
  rw [he]
  exact hh.isOpen_compl

lemma measurable_time : @Measurable C(I, ℝ) ℝ (borel _) _ time := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  apply measurable_of_Ioi
  intro t
  by_cases h0 : t < 0
  · have he : time ⁻¹' Ioi t = univ := by
      ext p
      simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact h0.trans_le (time_bounds p).1
    rw [he]
    exact MeasurableSet.univ
  by_cases h1 : 1 ≤ t
  · have he : time ⁻¹' Ioi t = ∅ := by
      ext p
      simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false]
      exact not_lt_of_ge ((time_bounds p).2.trans h1)
    rw [he]
    exact MeasurableSet.empty
  have he : time ⁻¹' Ioi t = {p : C(I, ℝ) | ∀ s ∈ Icc 0 t, 0 < extend p s} := by
    ext p
    exact lt_time_iff ⟨not_lt.1 h0,not_le.1 h1⟩
  rw [he]
  exact (isOpen_positive_on t).measurableSet

lemma time_pos {p : C(I, ℝ)} (h0 : 0 < extend p 0) : 0 < time p := by
  apply (lt_time_iff (p := p) (t := 0) ⟨le_rfl, zero_lt_one⟩).2
  intro s hs
  have hs0 : s = 0 := le_antisymm hs.2 hs.1
  simpa only [hs0] using h0

lemma nonneg_until {p : C(I, ℝ)} (h0 : 0 < extend p 0) {t : ℝ}
    (ht : t ∈ Icc 0 (time p)) : 0 ≤ extend p t := by
  rcases lt_or_eq_of_le ht.2 with hlt | rfl
  · exact (positive_before ht.1 hlt).le
  have htend : Tendsto (extend p) (𝓝[<] time p) (𝓝 (extend p (time p))) :=
    (continuous_extend p).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto htend
  filter_upwards [Ioo_mem_nhdsLT (time_pos h0)] with s hs
  exact (positive_before hs.1.le hs.2).le

lemma eq_zero_at_of_lt_one {p : C(I, ℝ)} (h0 : 0 < extend p 0)
    (hτ : time p < 1) : extend p (time p) = 0 :=
  le_antisymm (nonpos_at_of_lt_one hτ) (nonneg_until h0 ⟨(time_bounds p).1, le_rfl⟩)

end SLEExactGauge.ContinuousExit

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.LoewnerExit
open LoewnerCutoff
open scoped unitInterval
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)

def radius (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℝ :=
  2*(position hε hT U z t).im / Real.exp (logDerivative hε hT U z t)

def sine (U : C(I, ℝ)) (z : ℂ) (t : ℝ) : ℝ :=
  (position hε hT U z t).im /
    ‖clampIm ε (position hε hT U z t - (extendDriver T U t : ℂ))‖

def deficit (U : C(I, ℝ)) (z : ℂ) (ρ δ t : ℝ) : ℝ :=
  min (radius hε hT U z t - ρ)
    (min ((position hε hT U z t).im-ε) (sine hε hT U z t-δ))

lemma continuous_radius (z : ℂ) :
    Continuous (fun q : C(I, ℝ) × ℝ => radius hε hT q.1 z q.2) := by
  exact (continuous_const.mul (Complex.continuous_im.comp (continuous_position hε hT z))).div
    (Real.continuous_exp.comp (continuous_logDerivative hε hT z)) (fun _ => Real.exp_ne_zero _)

lemma continuous_sine (z : ℂ) :
    Continuous (fun q : C(I, ℝ) × ℝ => sine hε hT q.1 z q.2) := by
  exact (Complex.continuous_im.comp (continuous_position hε hT z)).div
    (((continuous_clampIm ε).comp ((continuous_position hε hT z).sub
      (Complex.continuous_ofReal.comp (continuous_joint_extendDriver T)))).norm)
    (fun _ => norm_ne_zero_iff.2 (clampIm_ne_zero hε _))

lemma continuous_deficit (z : ℂ) (ρ δ : ℝ) :
    Continuous (fun q : C(I, ℝ) × ℝ => deficit hε hT q.1 z ρ δ q.2) :=
  ((continuous_radius hε hT z).sub continuous_const).min
    (((Complex.continuous_im.comp (continuous_position hε hT z)).sub continuous_const).min
      ((continuous_sine hε hT z).sub continuous_const))

lemma deficit_pos_iff (U : C(I, ℝ)) (z : ℂ) (ρ δ t : ℝ) :
    0 < deficit hε hT U z ρ δ t ↔
      ρ < radius hε hT U z t ∧ ε < (position hε hT U z t).im ∧ δ < sine hε hT U z t := by
  simp only [deficit, lt_min_iff, sub_pos]

lemma deficit_nonneg_iff (U : C(I, ℝ)) (z : ℂ) (ρ δ t : ℝ) :
    0 ≤ deficit hε hT U z ρ δ t ↔
      ρ ≤ radius hε hT U z t ∧ ε ≤ (position hε hT U z t).im ∧ δ ≤ sine hε hT U z t := by
  simp only [deficit, le_min_iff, sub_nonneg]

def exitPath (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ) : C(I, ℝ) := by
  refine ⟨fun q => deficit hε hT U z ρ δ (T*q), ?_⟩
  have hp : Continuous (fun q : I => (U,T*q)) :=
    continuous_const.prodMk (continuous_const.mul continuous_subtype_val)
  have hc := (continuous_deficit hε hT z ρ δ).comp hp
  dsimp only [Function.comp_def] at hc
  exact hc

def stop (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ) : ℝ :=
  T * ContinuousExit.time (exitPath hε hT U z ρ δ)

lemma stop_bounds (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ) :
    stop hε hT U z ρ δ ∈ Icc 0 T := by
  have hh := ContinuousExit.time_bounds (exitPath hε hT U z ρ δ)
  exact ⟨mul_nonneg hT hh.1, by simpa only [stop, mul_one] using mul_le_mul_of_nonneg_left hh.2 hT⟩

lemma exitPath_extend (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ContinuousExit.extend (exitPath hε hT U z ρ δ) t = deficit hε hT U z ρ δ (T*t) := by
  simpa only [exitPath, ContinuousMap.coe_mk] using ContinuousExit.extend_coe
    (exitPath hε hT U z ρ δ) (⟨t,ht⟩ : I)

lemma exitPath_extend_div (hTp : 0 < T) (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ContinuousExit.extend (exitPath hε hT U z ρ δ) (t/T) = deficit hε hT U z ρ δ t := by
  rw [exitPath_extend hε hT U z ρ δ
    ⟨div_nonneg ht.1 hT, (div_le_one hTp).2 ht.2⟩, mul_div_cancel₀ _ hTp.ne']

lemma positive_before (hTp : 0 < T) (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (htτ : t < stop hε hT U z ρ δ) :
    0 < deficit hε hT U z ρ δ t := by
  rw [← exitPath_extend_div hε hT hTp U z ρ δ ⟨ht,htτ.le.trans (stop_bounds hε hT U z ρ δ).2⟩]
  apply ContinuousExit.positive_before (div_nonneg ht hT)
  exact (div_lt_iff₀ hTp).2 (by simpa only [stop, mul_comm] using htτ)

lemma stop_pos (hTp : 0 < T) (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    (h0 : 0 < deficit hε hT U z ρ δ 0) : 0 < stop hε hT U z ρ δ := by
  apply mul_pos hTp (ContinuousExit.time_pos _)
  simpa only [exitPath_extend hε hT U z ρ δ ⟨le_rfl,zero_le_one⟩, mul_zero] using h0

lemma nonneg_until (hTp : 0 < T) (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    (h0 : 0 < deficit hε hT U z ρ δ 0) {t : ℝ}
    (ht : t ∈ Icc 0 (stop hε hT U z ρ δ)) : 0 ≤ deficit hε hT U z ρ δ t := by
  rw [← exitPath_extend_div hε hT hTp U z ρ δ ⟨ht.1,ht.2.trans (stop_bounds hε hT U z ρ δ).2⟩]
  apply ContinuousExit.nonneg_until
  · simpa only [exitPath_extend hε hT U z ρ δ ⟨le_rfl,zero_le_one⟩, mul_zero] using h0
  · exact ⟨div_nonneg ht.1 hT, (div_le_iff₀ hTp).2 (by simpa only [stop, mul_comm] using ht.2)⟩

lemma nonpos_at_of_lt (hTp : 0 < T) (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    (hτ : stop hε hT U z ρ δ < T) :
    deficit hε hT U z ρ δ (stop hε hT U z ρ δ) ≤ 0 := by
  have hs : ContinuousExit.time (exitPath hε hT U z ρ δ) < 1 := by
    apply (mul_lt_mul_iff_right₀ hTp).mp
    simpa only [mul_one, stop] using hτ
  exact (exitPath_extend hε hT U z ρ δ (ContinuousExit.time_bounds _)) ▸
    ContinuousExit.nonpos_at_of_lt_one hs

lemma lt_stop_iff (hTp : 0 < T) (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    {t : ℝ} (ht : t ∈ Ico 0 T) :
    t < stop hε hT U z ρ δ ↔ ∀ s ∈ Icc 0 t, 0 < deficit hε hT U z ρ δ s := by
  constructor
  · intro hh s hs
    exact positive_before hε hT hTp U z ρ δ hs.1 (hs.2.trans_lt hh)
  · intro hh
    change t < T * ContinuousExit.time (exitPath hε hT U z ρ δ)
    rw [mul_comm]
    apply (div_lt_iff₀ hTp).1
    apply (ContinuousExit.lt_time_iff (p := exitPath hε hT U z ρ δ)
      ⟨div_nonneg ht.1 hT, (div_lt_one hTp).2 ht.2⟩).2
    intro s hs
    rw [exitPath_extend hε hT U z ρ δ
      ⟨hs.1, hs.2.trans ((div_le_one hTp).2 ht.2.le)⟩]
    apply hh
    exact ⟨mul_nonneg hT hs.1, (mul_le_mul_of_nonneg_left hs.2 hT).trans_eq
      (mul_div_cancel₀ _ hTp.ne')⟩

lemma isOpen_positive_on (z : ℂ) (ρ δ t : ℝ) :
    IsOpen {U : C(I, ℝ) | ∀ s ∈ Icc 0 t, 0 < deficit hε hT U z ρ δ s} := by
  let S : Set (C(I, ℝ) × Icc 0 t) := {q | deficit hε hT q.1 z ρ δ q.2 ≤ 0}
  have hmap : Continuous (fun q : C(I, ℝ) × Icc 0 t => (q.1,(q.2:ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hd := (continuous_deficit hε hT z ρ δ).comp hmap
  dsimp only [Function.comp_def] at hd
  have hc : IsClosed S := isClosed_le hd continuous_const
  have hh := isClosedMap_fst_of_compactSpace S hc
  have he : {U : C(I, ℝ) | ∀ s ∈ Icc 0 t, 0 < deficit hε hT U z ρ δ s} = (Prod.fst '' S)ᶜ := by
    ext U
    simp only [mem_ofPred_eq, mem_compl_iff, mem_image, S, not_exists, not_and]
    constructor
    · intro hp q hq hqp
      subst U
      exact (not_lt_of_ge hq) (hp q.2 q.2.property)
    · intro hp s hs
      by_contra hn
      exact hp (U,⟨s,hs⟩) (not_lt.1 hn) rfl
  rw [he]
  exact hh.isOpen_compl

end SLEExactGauge.LoewnerExit

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.LoewnerExit
open LoewnerCutoff
open scoped unitInterval

lemma deficit_prefix_eq {ε S T : ℝ} (hε : 0 < ε) (hS : 0 ≤ S) (hT : 0 ≤ T)
    (hST : S ≤ T) (U V : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    (hUV : EqOn (extendDriver S U) (extendDriver T V) (Icc 0 S)) :
    EqOn (deficit hε hS U z ρ δ) (deficit hε hT V z ρ δ) (Icc 0 S) := by
  have hH := position_prefix_eq hε hS hT hS le_rfl hST U V z hUV
  have hL := logDerivative_prefix_eq hε hS hT hS le_rfl hST U V z hUV
  intro t ht
  simp only [deficit, radius, sine, hH ht, hL ht, hUV ht]

end SLEExactGauge.LoewnerExit

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.LoewnerLocalized
open LoewnerCutoff LoewnerField LoewnerExit BrownianField
open scoped unitInterval

lemma regular {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (p a sdev : ℝ)
    (hp : 0 ≤ p) (ha : 0 ≤ a) (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ)
    (b : ℝ → ℝ) (hb : Continuous b) :
    FieldRegular (field hε hT.le p a sdev U z) (drift hε hT.le p a sdev U z) b
      (stop hε hT.le U z ρ δ) := by
  constructor
  · exact smooth hε hT.le p a sdev U z
  · exact field_third_bound hε hT.le p a sdev hp ha U z
  · intro x
    have hm : Continuous (fun t : ℝ => ((U,t),x)) :=
      (continuous_const.prodMk continuous_id).prodMk continuous_const
    have hc := (continuous_field hε hT.le p a sdev z).comp hm
    exact hc.continuousOn
  · intro t ht x
    have htT : t ∈ Ioo 0 T := ⟨ht.1,ht.2.trans_le (stop_bounds hε hT.le U z ρ δ).2⟩
    have hh := (deficit_pos_iff hε hT.le U z ρ δ t).1
      (positive_before hε hT.le hT U z ρ δ ht.1.le ht.2)
    exact time_deriv hε hT.le p a sdev U z htT hh.2.1 x
  · have hm : Continuous (fun q : ℝ × ℝ => ((U,q.1),b q.2)) :=
      (continuous_const.prodMk continuous_fst).prodMk (hb.comp continuous_snd)
    have hc := (continuous_drift hε hT.le p a sdev z).comp hm
    exact hc.continuousOn
  · have hm : Continuous (fun t : ℝ => ((U,t),b t)) :=
      (continuous_const.prodMk continuous_id).prodMk hb
    have hc := (continuous_second hε hT.le p a sdev z).comp hm
    exact hc.continuousOn

lemma integral_drift_cancel {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ) (b : ℝ → ℝ)
    (hU : ∀ s ∈ Icc 0 T, extendDriver T U s = Real.sqrt κ * b s) :
    (∫ t in (0:ℝ)..(stop hε hT.le U z ρ δ), drift hε hT.le (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t (b t)) +
      (1/2 : ℝ)*∫ t in (0:ℝ)..(stop hε hT.le U z ρ δ),
        iteratedDeriv 2 (field hε hT.le (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t) (b t) = 0 := by
  have he : (∫ t in (0:ℝ)..(stop hε hT.le U z ρ δ), drift hε hT.le (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t (b t)) =
      ∫ t in (0:ℝ)..(stop hε hT.le U z ρ δ),
        -(1/2 : ℝ)*iteratedDeriv 2 (field hε hT.le (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t) (b t) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (stop_bounds hε hT.le U z ρ δ).1
    intro t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1.le,ht.2.le.trans (stop_bounds hε hT.le U z ρ δ).2⟩
    have hh := (deficit_pos_iff hε hT.le U z ρ δ t).1
      (positive_before hε hT.le hT U z ρ δ ht.1.le ht.2)
    have hc := drift_cancellation hε hT.le κ hκ U z t (b t) hh.2.1.le (hU t htT)
    linarith
  rw [he, intervalIntegral.integral_const_mul]
  ring

end SLEExactGauge.LoewnerLocalized

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.ContinuousDriver

lemma aemeasurable_selectedLimit {Ω Y : Type*} [MeasurableSpace Ω]
    [MetricSpace Y] [CompleteSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology Y] {P : Measure Ω}
    (y₀ : Y) (a : ℕ → Ω → Y) (ha : ∀ n, AEMeasurable (a n) P) :
    AEMeasurable (fun sample => selectedLimit y₀ (fun n => a n sample)) P := by
  have hm : Measurable (fun a : ℕ → Y => selectedLimit y₀ a) :=
    measurable_selectedLimit y₀ (fun (n : ℕ) (a : ℕ → Y) => a n) (fun n => measurable_pi_apply n)
  exact hm.comp_aemeasurable (AEMeasurable.of_eval ha)

lemma aemeasurable_path {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (x : Ω → I → ℝ) (hx : ∀ t, AEMeasurable (fun sample => x sample t) P) :
    @AEMeasurable Ω C(I, ℝ) (borel C(I, ℝ)) _ (fun sample => path (x sample)) P := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  apply aemeasurable_selectedLimit
  intro n
  apply Finset.aemeasurable_fun_sum
  intro k _
  exact (hx (bernstein.z k)).smul aemeasurable_const

end SLEExactGauge.ContinuousDriver

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.BrownianDriver
open BrownianPredictable LoewnerCutoff
open scoped unitInterval

def path {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (sdev : ℝ) (T : ℝ≥0) (sample : Ω) : C(I, ℝ) :=
  ContinuousDriver.path (fun q : I => sdev * B ((T:ℝ)*q).toNNReal sample)

lemma path_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (sdev : ℝ) (T : ℝ≥0) :
    @Measurable Ω C(I, ℝ) (pastSigma B T) (borel C(I, ℝ)) (path B sdev T) := by
  let : MeasurableSpace Ω := pastSigma B T
  apply ContinuousDriver.measurable_path
  intro q
  apply Measurable.const_mul
  apply past_measurable_eval
  have hh : (T:ℝ)*q ≤ T := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left q.property.2 T.coe_nonneg
  exact (Real.toNNReal_le_toNNReal hh).trans_eq Real.toNNReal_coe

lemma path_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (sdev : ℝ) (T : ℝ≥0) :
    @AEMeasurable Ω C(I, ℝ) (borel C(I, ℝ)) _ (path B sdev T) P := by
  apply ContinuousDriver.aemeasurable_path
  intro q
  exact ((hB.toIsPreBrownianReal.hasLaw_eval _).aemeasurable).const_mul sdev

lemma path_eval {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (sdev : ℝ) (T : ℝ≥0) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) (q : I) :
    path B sdev T sample q = sdev * B ((T:ℝ)*q).toNNReal sample := by
  apply ContinuousDriver.path_eval_of_continuous
  exact continuous_const.mul (hc.comp (continuous_real_toNNReal.comp
    (continuous_const.mul continuous_subtype_val)))

lemma extend_eq {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (sdev : ℝ) (T : ℝ≥0) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) {t : ℝ} (ht : t ∈ Icc 0 (T:ℝ)) :
    extendDriver T (path B sdev T sample) t = sdev * B t.toNNReal sample := by
  rw [extendDriver, path_eval B sdev T sample hc]
  by_cases hT : (T:ℝ) = 0
  · have ht0 : t = 0 := le_antisymm (hT ▸ ht.2) ht.1
    simp only [hT, ht0, zero_mul]
  · have hTp : 0 < (T:ℝ) := lt_of_le_of_ne T.coe_nonneg (Ne.symm hT)
    rw [projIcc_of_mem zero_le_one ⟨div_nonneg ht.1 T.coe_nonneg, (div_le_one hTp).2 ht.2⟩,
      mul_div_cancel₀ _ hT]

lemma prefix_eq {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (sdev : ℝ) (S T : ℝ≥0) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) (hST : S ≤ T) :
    EqOn (extendDriver S (path B sdev S sample)) (extendDriver T (path B sdev T sample)) (Icc 0 (S:ℝ)) := by
  intro t ht
  rw [extend_eq B sdev S sample hc ht, extend_eq B sdev T sample hc ⟨ht.1,ht.2.trans hST⟩]

end SLEExactGauge.BrownianDriver

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.LoewnerLocalized
open LoewnerCutoff LoewnerField LoewnerExit BrownianPredictable BrownianStopped BrownianIto TaylorMeshes
open scoped unitInterval
variable {ε : ℝ} (hε : 0 < ε)

def coeffAt (k : ℕ) (s : ℝ≥0) (p a sdev : ℝ) (z : ℂ) (ρ δ : ℝ)
    (q : C(I, ℝ) × ℝ) : ℝ := by
  classical
  exact if ∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg q.1 z ρ δ t then
    iteratedDeriv k (field hε s.coe_nonneg p a sdev q.1 z s) q.2 else 0

lemma coeffAt_measurable (k : ℕ) (hk : k = 1 ∨ k = 2) (s : ℝ≥0)
    (p a sdev : ℝ) (z : ℂ) (ρ δ : ℝ) :
    @Measurable (C(I, ℝ) × ℝ) ℝ (@Prod.instMeasurableSpace _ _ (borel _) inferInstance) _ (coeffAt hε k s p a sdev z ρ δ) := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  have hc : Continuous (fun q : C(I, ℝ) × ℝ =>
      iteratedDeriv k (field hε s.coe_nonneg p a sdev q.1 z s) q.2) := by
    have hp : Continuous (fun q : C(I, ℝ) × ℝ => ((q.1,(s:ℝ)),q.2)) :=
      (continuous_fst.prodMk continuous_const).prodMk continuous_snd
    rcases hk with rfl | rfl
    · have hc := (continuous_first hε s.coe_nonneg p a sdev z).comp hp
      dsimp only [Function.comp_def] at hc
      exact hc
    · have hc := (continuous_second hε s.coe_nonneg p a sdev z).comp hp
      dsimp only [Function.comp_def] at hc
      exact hc
  apply hc.measurable.ite _ measurable_const
  exact ((isOpen_positive_on hε s.coe_nonneg z ρ δ s).preimage continuous_fst).measurableSet

def rawCoeff {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (p a sdev : ℝ) (z : ℂ) (ρ δ : ℝ) (sample : Ω) : ℝ :=
  if s < T then coeffAt hε k s p a sdev z ρ δ (BrownianDriver.path B sdev s sample, B s sample) else 0

lemma rawCoeff_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (hk : k = 1 ∨ k = 2) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (p a sdev : ℝ) (z : ℂ) (ρ δ : ℝ) :
    Measurable[pastSigma B s] (rawCoeff hε k B T s p a sdev z ρ δ) := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  let : MeasurableSpace Ω := pastSigma B s
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s p a sdev z ρ δ).comp
      ((BrownianDriver.path_measurable_past B sdev s).prodMk (past_measurable_eval B (s := s) le_rfl))
  · exact measurable_const

lemma rawCoeff_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (k : ℕ) (hk : k = 1 ∨ k = 2) (T s : ℝ≥0)
    (p a sdev : ℝ) (z : ℂ) (ρ δ : ℝ) :
    AEMeasurable (rawCoeff hε k B T s p a sdev z ρ δ) P := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s p a sdev z ρ δ).comp_aemeasurable
      ((BrownianDriver.path_aemeasurable hB sdev s).prodMk (hB.toIsPreBrownianReal.hasLaw_eval s).aemeasurable)
  · exact aemeasurable_const

lemma rawCoeff_eq {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (hT : 0 < (T:ℝ)) (p a sdev : ℝ) (z : ℂ) (ρ δ : ℝ) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) :
    rawCoeff hε k B T s p a sdev z ρ δ sample =
      if (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ then
        iteratedDeriv k (field hε T.coe_nonneg p a sdev (BrownianDriver.path B sdev T sample) z s) (B s sample) else 0 := by
  classical
  by_cases hsT : s < T
  · have he := BrownianDriver.prefix_eq B sdev s T sample hc hsT.le
    have hf := field_prefix_eq hε s.coe_nonneg T.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) z p a sdev he
      ⟨s.coe_nonneg, le_rfl⟩
    have hd := deficit_prefix_eq hε s.coe_nonneg T.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) z ρ δ he
    have hi : (∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg (BrownianDriver.path B sdev s sample) z ρ δ t) ↔
        (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ := by
      rw [lt_stop_iff hε T.coe_nonneg hT _ z ρ δ ⟨s.coe_nonneg,hsT⟩]
      exact forall₂_congr (fun t ht => by rw [hd ht])
    simp only [rawCoeff, ite_eq_left hsT, coeffAt, hi, hf]
  · have hstop : ¬ (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ :=
      not_lt_of_ge ((stop_bounds hε T.coe_nonneg _ z ρ δ).2.trans (not_lt.1 hsT))
    simp only [rawCoeff, ite_eq_right hsT, ite_eq_right hstop]

lemma rawCoeff_stoppedCoeff_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (k : ℕ) (T : ℝ≥0)
    (hT : 0 < (T:ℝ)) (p a sdev : ℝ) (z : ℂ) (ρ δ : ℝ) (n i : ℕ) :
    rawCoeff hε k B T (dyadicTime T n i) p a sdev z ρ δ =ᵐ[P]
      stoppedCoeff k B T
        (fun sample => stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ)
        (fun sample => field hε T.coe_nonneg p a sdev (BrownianDriver.path B sdev T sample) z) n i := by
  filter_upwards [hB.cont] with sample hc
  rw [rawCoeff_eq hε k B T _ hT p a sdev z ρ δ sample hc]
  simp only [stoppedCoeff, coe_dyadicTime]

end SLEExactGauge.LoewnerLocalized

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.LoewnerLocalized
open LoewnerCutoff LoewnerField LoewnerExit BrownianPredictable BrownianStopped BrownianIto TaylorMeshes
open scoped unitInterval

lemma coeff_uniform_bound {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (k : ℕ) (hk : k = 1 ∨ k = 2) (p a sdev : ℝ) (hp : 0 ≤ p) (ha : 0 ≤ a)
    (z : ℂ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (U : C(I, ℝ)) (t b : ℝ),
      |iteratedDeriv k (field hε hT p a sdev U z t) b| ≤ K := by
  rcases hk with rfl | rfl
  · refine ⟨max 0 (|sdev| * ((2*ε/Real.exp ((2/ε^2)*T))^(-p)*a/ε)), le_max_left _ _, ?_⟩
    intro U t b
    exact (first_bound hε hT p a sdev hp ha U z t b).trans (le_max_right _ _)
  · refine ⟨max 0 (|sdev|^2 * ((2*ε/Real.exp ((2/ε^2)*T))^(-p)*(a*(a+2))/ε^2)), le_max_left _ _, ?_⟩
    intro U t b
    exact (second_bound hε hT p a sdev hp ha U z t b).trans (le_max_right _ _)

theorem localized_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (z : ℂ) (ρ δ : ℝ) :
    let U := BrownianDriver.path B (Real.sqrt κ) T
    let τ := fun sample => stop hε T.coe_nonneg (U sample) z ρ δ
    let F := fun sample => field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
    Integrable (fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample)) P ∧
      (∫ sample, F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) ∂P) = 0 := by
  dsimp only
  let U := BrownianDriver.path B (Real.sqrt κ) T
  let τ := fun sample => stop hε T.coe_nonneg (U sample) z ρ δ
  let F := fun sample => field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
  let V := fun sample => drift hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
  have hp : 0 ≤ 1-κ/8 := by linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := by
    have hh : (1:ℝ) ≤ 8/κ := (le_div_iff₀ hκ.1).2 (by simpa using hκ.2.le)
    linarith
  have hreg : ∀ᵐ sample ∂P, BrownianField.FieldRegular (F sample) (V sample)
      (fun t => B t.toNNReal sample) (τ sample) := by
    filter_upwards [hB.cont] with sample hc
    exact regular hε hT (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha (U sample) z ρ δ _
      (hc.comp continuous_real_toNNReal)
  have htau : ∀ᵐ sample ∂P, 0 ≤ τ sample ∧ τ sample ≤ T :=
    Filter.Eventually.of_forall (fun sample => stop_bounds hε T.coe_nonneg (U sample) z ρ δ)
  obtain ⟨K₁,hK₁,hb₁⟩ := coeff_uniform_bound hε T.coe_nonneg 1 (Or.inl rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  obtain ⟨K₂,hK₂,hb₂⟩ := coeff_uniform_bound hε T.coe_nonneg 2 (Or.inr rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  have hsbound (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
      (hb : ∀ (W : C(I, ℝ)) (t b : ℝ),
        |iteratedDeriv k (field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) W z t) b| ≤ K)
      (n i : ℕ) : ∀ᵐ sample ∂P, |stoppedCoeff k B T τ F n i sample| ≤ K := by
    apply Filter.Eventually.of_forall
    intro sample
    unfold stoppedCoeff
    split_ifs
    · exact hb _ _ _
    · simpa only [abs_zero] using hK
  let A := fun n i => rawCoeff hε 1 B T (dyadicTime T n i) (1-κ/8) (8/κ-1) (Real.sqrt κ) z ρ δ
  let C := fun n i => rawCoeff hε 2 B T (dyadicTime T n i) (1-κ/8) (8/κ-1) (Real.sqrt κ) z ρ δ
  have hAe (n i : ℕ) : A n i =ᵐ[P] stoppedCoeff 1 B T τ F n i :=
    rawCoeff_stoppedCoeff_ae hε hB 1 T hT (1-κ/8) (8/κ-1) (Real.sqrt κ) z ρ δ n i
  have hCe (n i : ℕ) : C n i =ᵐ[P] stoppedCoeff 2 B T τ F n i :=
    rawCoeff_stoppedCoeff_ae hε hB 2 T hT (1-κ/8) (8/κ-1) (Real.sqrt κ) z ρ δ n i
  have hAm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (A n i) :=
    rawCoeff_measurable_past hε 1 (Or.inl rfl) B T _ _ _ _ z ρ δ
  have hCm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (C n i) :=
    rawCoeff_measurable_past hε 2 (Or.inr rfl) B T _ _ _ _ z ρ δ
  have hA2 (n i : ℕ) : MemLp (A n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable hε hB 1 (Or.inl rfl) T _ _ _ _ z ρ δ).aestronglyMeasurable K₁
    filter_upwards [hAe n i, hsbound 1 K₁ hK₁ hb₁ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |A n i sample| ≤ K₁
    rw [he]
    exact hb
  have hC2 (n i : ℕ) : MemLp (C n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable hε hB 2 (Or.inr rfl) T _ _ _ _ z ρ δ).aestronglyMeasurable K₂
    filter_upwards [hCe n i, hsbound 2 K₂ hK₂ hb₂ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |C n i sample| ≤ K₂
    rw [he]
    exact hb
  have hi := stopped_field_ito_centered_ae hB T τ F V htau hreg A C hAe hCe hCm hC2
    K₂ hK₂ (hsbound 2 K₂ hK₂ hb₂) hAm hA2 K₁ hK₁ (hsbound 1 K₁ hK₁ hb₁)
  have he : (fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) -
      (∫ t in (0:ℝ)..(τ sample), V sample t (B t.toNNReal sample)) -
      (1/2:ℝ)*∫ t in (0:ℝ)..(τ sample), iteratedDeriv 2 (F sample t) (B t.toNNReal sample)) =ᵐ[P]
      (fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample)) := by
    filter_upwards [hB.cont] with sample hc
    have hcanc := integral_drift_cancel hε hT κ hκ.1 (U sample) z ρ δ
      (fun t => B t.toNNReal sample) (fun t ht => BrownianDriver.extend_eq B _ T sample hc ht)
    dsimp only [F,V,τ]
    linarith
  exact ⟨hi.1.congr he, (integral_congr_ae he).symm.trans hi.2⟩

end SLEExactGauge.LoewnerLocalized

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.LoewnerLocalized
open LoewnerCutoff LoewnerField LoewnerExit GreenPhysical
open scoped unitInterval

lemma field_initial {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (p a sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (hy : ε ≤ z.im) :
    field hε hT p a sdev U z 0 0 = green p a z.re z.im 0 := by
  simp only [field, height, position_initial, logDerivative_initial, mul_zero, sub_zero,
    max_eq_right hy]

theorem localized_expectation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (z : ℂ) (hy : ε ≤ z.im) (ρ δ : ℝ) :
    let U := BrownianDriver.path B (Real.sqrt κ) T
    let τ := fun sample => stop hε T.coe_nonneg (U sample) z ρ δ
    let M := fun sample => field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
      (τ sample) (B (τ sample).toNNReal sample)
    Integrable M P ∧ (∫ sample, M sample ∂P) = green (1-κ/8) (8/κ-1) z.re z.im 0 := by
  dsimp only
  let U := BrownianDriver.path B (Real.sqrt κ) T
  let τ := fun sample => stop hε T.coe_nonneg (U sample) z ρ δ
  let F := fun sample => field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
  let M := fun sample => F sample (τ sample) (B (τ sample).toNNReal sample)
  let G := green (1-κ/8) (8/κ-1) z.re z.im 0
  have hi := localized_centered hB κ hκ hε T hT z ρ δ
  have he : (fun sample => M sample - F sample 0 (B 0 sample)) =ᵐ[P]
      (fun sample => M sample - G) := by
    filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hb
    rw [hb]
    congr 1
    exact field_initial hε T.coe_nonneg _ _ _ _ z hy
  have hd : Integrable (fun sample => M sample-G) P := hi.1.congr he
  have hv : (∫ sample, M sample-G ∂P) = 0 := (integral_congr_ae he).symm.trans hi.2
  have hm : Integrable M P := by
    exact (hd.add (integrable_const G)).congr
      (Filter.Eventually.of_forall (fun sample => sub_add_cancel (M sample) G))
  refine ⟨hm, ?_⟩
  have hh := integral_sub hm (integrable_const (μ := P) G)
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hh
  rw [hh] at hv
  change (∫ sample, M sample ∂P) = G
  linarith

end SLEExactGauge.LoewnerLocalized

end

end

end

end

end

end

end

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
namespace SLEExactGauge.IsLoewnerTraceUsing
open LoewnerCutoff

lemma cutoff_solution_live {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing driver γ g f) {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    {H : ℝ → ℂ}
    (hH : ∀ t ∈ Icc 0 T,
      HasDerivWithinAt H (velocity ε (driver t) (H t)) (Icc 0 T) t)
    (hheight : ∀ t ∈ Icc 0 T, ε ≤ (H t).im) :
    H 0 ∈ localizationDomain γ T ∧ EqOn (fun t => g t (H 0)) H (Icc 0 T) := by
  have hp : H T ∈ halfPlane := hε.trans_le (hheight T ⟨hT, le_rfl⟩)
  let z' := f T (H T)
  have hz' : z' ∈ localizationDomain γ T := h.2.2.2.2.2.2.2.2.1 T hT hp
  have hfinal : g T z' = H T := h.2.2.2.2.2.2.2.2.2.2.1 T hT _ hp
  have hht (t : ℝ) (ht : t ∈ Icc 0 T) : ε ≤ (g t z').im := by
    have ha := h.height_antitone hT hz' ht ⟨hT, le_rfl⟩ ht.2
    dsimp only at ha
    rw [hfinal] at ha
    exact (hheight T ⟨hT, le_rfl⟩).trans ha
  have hd (t : ℝ) (ht : t ∈ Ioc 0 T) :
      HasDerivWithinAt (fun s => g s z')
        (velocity ε (driver t) (g t z')) (Iic t) t := by
    rw [velocity_eq (hht t ⟨ht.1.le, ht.2⟩)]
    exact (h.2.2.2.2.2.2.2.2.2.2.2.2.1 t ht.1 z'
      (survivingDomain_mono ht.2 hz')).hasDerivWithinAt
  have he : EqOn (fun t => g t z') H (Icc 0 T) :=
    ODE_solution_unique_of_mem_Icc_left
      (s := fun _ => univ) (fun t _ => (velocity_lipschitz hε (driver t)).lipschitzOnWith)
      (h.continuous_eval hT hz') hd (fun _ _ => mem_univ _)
      (HasDerivWithinAt.continuousOn hH) (fun _ ht => derivWithin_left hH ht)
      (fun _ _ => mem_univ _) hfinal
  have hz0 : z' = H 0 := by
    rw [← h.initial z' hz'.1.1]
    exact he ⟨le_rfl, hT⟩
  exact ⟨hz0 ▸ hz', hz0 ▸ he⟩

variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma hasDerivWithinAt_eval (h : IsLoewnerTraceUsing driver γ g f)
    {T : ℝ} (hT : 0 ≤ T) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun s => g s z)
      (2 / (g t z - (driver t : ℂ))) (Icc 0 T) t := by
  have hc := h.continuous_velocity hT hU hz
  have hi : IntervalIntegrable (fun s => 2 / (g s z - (driver s : ℂ))) volume 0 t :=
    (hc.intervalIntegrable_of_Icc hT).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
  have : Fact (t ∈ Icc 0 T) := ⟨ht⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s := Icc 0 T) (t := Icc 0 T)
    hi (hc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hc t ht)
  have he : EqOn (fun s => g 0 z + ∫ v in (0 : ℝ)..s, 2 / (g v z - (driver v : ℂ)))
      (fun s => g s z) (Icc 0 T) := by
    intro s hs
    dsimp only
    rw [h.integral_velocity hT hU hz ⟨le_rfl, hT⟩ hs hs.1]
    abel
  exact (hd.const_add (g 0 z)).congr (fun s hs => (he hs).symm) (he ht).symm

lemma eq_cutoff_solution (h : IsLoewnerTraceUsing driver γ g f)
    {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hU : ContinuousOn driver (Icc 0 T))
    {z : ℂ} (hz : z ∈ localizationDomain γ T) (hheight : ε ≤ (g T z).im)
    {H : ℝ → ℂ} (hH0 : H 0 = z)
    (hH : ∀ t ∈ Icc 0 T, HasDerivWithinAt H
      (velocity ε (driver t) (H t)) (Icc 0 T) t) :
    EqOn (fun t => g t z) H (Icc 0 T) := by
  apply solution_eq hε ?_ hH ((h.initial z hz.1.1).trans hH0.symm)
  intro t ht
  rw [velocity_eq (hheight.trans (h.height_antitone hT hz ht ⟨hT, le_rfl⟩ ht.2))]
  exact h.hasDerivWithinAt_eval hT hU hz ht

end SLEExactGauge.IsLoewnerTraceUsing

end

end

end

end

end

end

end

end

end

end OAI
