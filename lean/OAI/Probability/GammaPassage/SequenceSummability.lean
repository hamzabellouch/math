import OAI.Probability.GammaPassage.GlobalConcentration
import OAI.Probability.GammaPassage.MeanPositive
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace OAI

namespace GammaFPP
open MeasureTheory Real Filter Topology PlanarFPP

lemma exp_neg_sqrt_le (a m : ℝ) (ha : 0 < a) (hm : 0 < m) :
    exp (-(a*sqrt m)) ≤ (24/a^4)/m^2 := by
  have h := Real.pow_div_factorial_le_exp (a*sqrt m) (by positivity) 4
  have hs := sq_sqrt hm.le
  have he : (a*sqrt m)^4 = a^4*m^2 := by
    rw [mul_pow, show sqrt m^4 = (sqrt m^2)^2 by ring, hs]
  rw [he] at h
  norm_num at h
  rw [exp_neg, ← one_div, div_div]
  apply (div_le_div_iff₀ (exp_pos _) (by positivity)).mpr
  nlinarith

lemma summable_exp_neg_sqrt (a : ℝ) (ha : 0 < a) :
    Summable (fun n : ℕ => exp (-(a*sqrt (n+1)))) := by
  have h := ((summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
    (show Function.Injective (fun n : ℕ => n+1) from fun _ _ h => Nat.add_right_cancel h)).mul_left (24/a^4)
  apply h.of_nonneg_of_le (fun n => (exp_pos _).le)
  intro n
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_one_div] using
    exp_neg_sqrt_le a (n+1) ha (by positivity)

noncomputable def localizationDecay (shape rate : ℝ) : ℝ :=
  min (log 2) (rate*cheapSlope shape rate/8)

lemma localizationDecay_pos {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) :
    0 < localizationDecay shape rate := by
  exact lt_min (log_pos (by norm_num)) (by have := cheapSlope_pos hs hr; positivity)

lemma localizationErrorBound_exp {shape rate : ℝ} (hr : 0 < rate) (d R : ℕ)
    (hscale : 2*coordinateAllowance shape rate*(d : ℝ) ≤ cheapSlope shape rate*(R : ℝ)) :
    localizationErrorBound shape rate d R ≤ 3*exp (-localizationDecay shape rate*R) := by
  have hR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
  have hlog : localizationDecay shape rate ≤ log 2 := min_le_left _ _
  have hc : localizationDecay shape rate ≤ rate*cheapSlope shape rate/8 := min_le_right _ _
  have hp : (1/2 : ℝ)^R = exp (-(log 2)*(R : ℝ)) := by
    rw [show -(log 2)*(R : ℝ) = (R : ℝ)*(-log 2) by ring, exp_nat_mul, exp_neg,
      exp_log (by norm_num : (0 : ℝ) < 2)]
    simp only [one_div]
  have h₁ : (1/2 : ℝ)^R ≤ exp (-localizationDecay shape rate*R) := by
    rw [hp]
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hlog hR]
  have h₂ := localization_exponential_scale_separation hr hscale
  have h₃ : exp (-(rate*cheapSlope shape rate/8)*(R : ℝ)) ≤
      exp (-localizationDecay shape rate*R) := by
    apply exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hR]
  unfold localizationErrorBound
  linarith [h₂.trans h₃]

/-- Choose a natural length multiplier; it may depend on direction and law,
never on sample, time n, or deviation threshold. -/
lemma exists_ray_cutoff {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate) (d : ℕ) :
    ∃ L : ℕ, d < L ∧ 2*coordinateAllowance shape rate*(d : ℝ) ≤ cheapSlope shape rate*L := by
  obtain ⟨L,hL⟩ := exists_nat_gt (max (d : ℝ)
    (2*coordinateAllowance shape rate*d/cheapSlope shape rate))
  refine ⟨L, ?_, ?_⟩
  · exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hL)
  · have hc := cheapSlope_pos hs hr
    have hh := lt_of_le_of_lt (le_max_right _ _) hL
    exact ((div_lt_iff₀ hc).mp hh).le.trans_eq (mul_comm _ _)

lemma meanLocalizationAllowance_mul (shape rate : ℝ) (m d R : ℕ) :
    meanLocalizationAllowance shape rate (m*d) R =
      (m : ℝ)*sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2)*
        sqrt (localizationErrorBound shape rate (m*d) R) := by
  unfold meanLocalizationAllowance
  rw [Nat.cast_mul, show pathSecondMomentConstant shape rate*((m : ℝ)*(d : ℝ))^2 =
    (m : ℝ)^2*(pathSecondMomentConstant shape rate*(d : ℝ)^2) by ring,
    sqrt_mul (sq_nonneg _), sqrt_sq_eq_abs, abs_of_nonneg (Nat.cast_nonneg m)]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Absolute centered deviations at every positive lattice-ray index are
summable. Zero direction needs no special denominator or positive distance. -/
theorem GammaEnvironment.summable_ray_centered_deviations
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (ε : ℝ) (hε : 0 < ε) :
    Summable (fun n : ℕ => P.real {ω | ε*(n+1 : ℝ) ≤
      |passageTime (fun e => τ e ω) 0 ((n+1) • z) -
        meanPassageSequence P τ z (n+1)|}) := by
  let : IsProbabilityMeasure P := h.probability
  let d := latticeDistance 0 z
  obtain ⟨L,hLd,hLs⟩ := exists_ray_cutoff hs hr d
  have hL : 0 < L := lt_of_le_of_lt (Nat.zero_le d) hLd
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  let k := localizationDecay shape rate
  have hk : 0 < k := localizationDecay_pos hs hr
  let E : ℕ → ℝ := fun n => localizationErrorBound shape rate ((n+1)*d) (L*(n+1))
  have hEbound (n : ℕ) : E n ≤ 3*exp (-(k*L)*(n+1 : ℝ)) := by
    have hb := localizationErrorBound_exp hr ((n+1)*d) (L*(n+1)) (by
      push_cast
      have hh := mul_le_mul_of_nonneg_right hLs (show (0 : ℝ) ≤ n+1 by positivity)
      nlinarith)
    change localizationErrorBound shape rate ((n+1)*d) (L*(n+1)) ≤ _
    calc
      _ ≤ 3*exp (-localizationDecay shape rate*(L*(n+1) : ℕ)) := hb
      _ = _ := by
        dsimp [k]
        push_cast
        exact congrArg (fun x : ℝ => 3*exp x) (by ring)
  have hgeo : Summable (fun n : ℕ => exp (-(k*L)*(n+1 : ℝ))) := by
    have hh := (summable_nat_add_iff 1).mpr
      (Real.summable_exp_nat_mul_iff.mpr (show -(k*(L : ℝ)) < 0 from neg_neg_of_pos (mul_pos hk hLR)))
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hh
  have hEsum : Summable E := (hgeo.mul_left 3).of_nonneg_of_le
    (fun n => by dsimp [E, localizationErrorBound]; positivity) hEbound
  have hEzero : Tendsto E atTop (𝓝 0) := hEsum.tendsto_atTop_zero
  have hsmall : ∀ᶠ n : ℕ in atTop,
      sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2)*sqrt (E n) < ε/2 := by
    have ht := (hEzero.sqrt).const_mul (sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2))
    have ht' : Tendsto (fun n => sqrt (pathSecondMomentConstant shape rate*(d : ℝ)^2)*sqrt (E n))
        atTop (𝓝 0) := by simpa using ht
    exact ht'.eventually (gt_mem_nhds (by positivity))
  let a := FiniteLocal.concentrationKappa shape rate*ε/(2*sqrt (L : ℝ))
  have ha : 0 < a := by
    have := (FiniteLocal.concentrationKappa_bounds (shape := shape) hr).1
    dsimp [a]; positivity
  have hsum := ((summable_exp_neg_sqrt a ha).mul_left (2*exp 1)).add hEsum
  apply hsum.of_norm_bounded_eventually_nat
  filter_upwards [hsmall] with n hn
  have hm : (0 : ℝ) < n+1 := by positivity
  have hrad : latticeDistance 0 ((n+1) • z) < L*(n+1) := by
    rw [latticeDistance_zero_nsmul]
    dsimp [d] at hLd
    nlinarith
  have hal : meanLocalizationAllowance shape rate ((n+1)*d) (L*(n+1)) ≤ ε*(n+1 : ℝ)/2 := by
    rw [meanLocalizationAllowance_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    have hh := mul_le_mul_of_nonneg_left hn.le hm.le
    dsimp [E] at hh
    nlinarith
  let t : ℝ := ε*sqrt (n+1)/(2*sqrt (L : ℝ))
  have ht : t*sqrt (L*(n+1) : ℕ) = ε*(n+1 : ℝ)/2 := by
    dsimp [t]
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, sqrt_mul hLR.le]
    have hne : sqrt (L : ℝ) ≠ 0 := (sqrt_pos.mpr hLR).ne'
    calc
      ε*sqrt (n+1)/(2*sqrt (L : ℝ))*(sqrt (L : ℝ)*sqrt (n+1)) =
          ε*(sqrt (n+1))^2/2 := by field_simp [hne]
      _ = ε*(n+1 : ℝ)/2 := by rw [sq_sqrt hm.le]
  have hb := h.passageTime_centered_exponential hs hr 0 ((n+1) • z)
    (L*(n+1)) hrad t
  rw [latticeDistance_zero_nsmul] at hb
  have hsub : {ω | ε*(n+1 : ℝ) ≤ |passageTime (fun e => τ e ω) 0 ((n+1) • z) -
      meanPassageSequence P τ z (n+1)|} ⊆
      {ω | t*sqrt (L*(n+1) : ℕ)+meanLocalizationAllowance shape rate ((n+1)*d) (L*(n+1)) ≤
      |passageTime (fun e => τ e ω) 0 ((n+1) • z)-
        ∫ η, passageTime (fun e => τ e η) 0 ((n+1) • z) ∂P|} := by
    intro ω hω
    change ε*(n+1 : ℝ) ≤ _ at hω
    change t*sqrt (L*(n+1) : ℕ)+_ ≤ _
    rw [ht]
    change ε*(n+1 : ℝ) ≤ |passageTime (fun e => τ e ω) 0 ((n+1) • z)-
      ∫ η, passageTime (fun e => τ e η) 0 ((n+1) • z) ∂P| at hω
    linarith
  have hprob := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono hsub)
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  apply hprob.trans (hb.trans_eq ?_)
  dsimp [E, t, a]
  congr 1
  rw [show 1-FiniteLocal.concentrationKappa shape rate*
      (ε*sqrt (n+1)/(2*sqrt (L : ℝ))) =
      1 + -(FiniteLocal.concentrationKappa shape rate*ε/(2*sqrt (L : ℝ))*sqrt (n+1)) by ring,
    exp_add]
  ring

/-- Normalized centered deviations along a lattice ray have summable
probabilities at every positive tolerance. The event at `n = 0` is empty. -/
theorem GammaEnvironment.normalized_ray_deviations_tsum_ne_top
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex) (k : ℕ) :
    (∑' n : ℕ, P {ω | 1/((k : ℝ)+1) ≤
      |passageTime (fun e => τ e ω) 0 (n • z)/(n : ℝ) -
        meanPassageSequence P τ z n/(n : ℝ)|}) ≠ ⊤ := by
  let : IsProbabilityMeasure P := h.probability
  let ε : ℝ := 1/((k : ℝ)+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hh := h.summable_ray_centered_deviations hs hr z ε hε
  have he (n : ℕ) : {ω | ε ≤ |passageTime (fun e => τ e ω) 0 ((n+1) • z)/((n+1 : ℕ) : ℝ) -
      meanPassageSequence P τ z (n+1)/((n+1 : ℕ) : ℝ)|} =
      {ω | ε*(n+1 : ℝ) ≤ |passageTime (fun e => τ e ω) 0 ((n+1) • z)-
        meanPassageSequence P τ z (n+1)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, ← sub_div, abs_div, Nat.cast_add, Nat.cast_one,
      abs_of_pos (show (0 : ℝ) < n+1 by positivity), le_div_iff₀ (show (0 : ℝ) < n+1 by positivity)]
  have hn : Summable (fun n : ℕ => P.real {ω | ε ≤
      |passageTime (fun e => τ e ω) 0 (n • z)/(n : ℝ)-meanPassageSequence P τ z n/(n : ℝ)|}) := by
    apply (summable_nat_add_iff 1).mp
    simpa only [he] using hh
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hn.tsum_ofReal_ne_top

end GammaFPP

end OAI
