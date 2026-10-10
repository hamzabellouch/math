import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceGrowthBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceHistoryMoments

namespace OAI

section

/-! # Positive marked histories in a measurable two-beam medium -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

structure BeamCoefficients where
  plusPartner : ℝ × V → V
  minusPartner : ℝ × V → V
  plusDensity : ℝ × V → ℝ
  minusDensity : ℝ × V → ℝ
  plusPartner_measurable : Measurable plusPartner
  minusPartner_measurable : Measurable minusPartner
  plusDensity_measurable : Measurable plusDensity
  minusDensity_measurable : Measurable minusDensity

abbrev PhysicalFlightState := ℝ × (V × V)

def embedFlightState (p : TimeFlightState) : PhysicalFlightState := (p.1,(p.2.1,p.2.2.1))

def mediumPoint (endTime : ℝ) (p : PhysicalFlightState) (s : ℝ) : ℝ × V :=
  (endTime-p.1+s,p.2.1+s • p.2.2)

def mediumParameterState (b : BeamCoefficients) (endTime : ℝ) (p : PhysicalFlightState)
    (a : MarkedEventParameter) : PhysicalFlightState :=
  let x := mediumPoint endTime p a.2.1
  (p.1-a.2.1,(x.2,markedChild a.1 p.2.2 (b.plusPartner x) (b.minusPartner x) a.2.2.1))

def mediumParameterDensity (b : BeamCoefficients) (endTime : ℝ) (p : PhysicalFlightState)
    (a : MarkedEventParameter) : ℝ≥0∞ :=
  let x := mediumPoint endTime p a.2.1
  (Ioc 0 p.1).indicator 1 a.2.1 * clockSurvival referenceClock a.2.1 *
    ENNReal.ofReal (markedRate a.1 p.2.2 (b.plusPartner x) (b.minusPartner x)
      (b.plusDensity x) (b.minusDensity x))

theorem mediumPoint_measurable (endTime : ℝ) :
    Measurable (fun q : PhysicalFlightState × ℝ => mediumPoint endTime q.1 q.2) := by
  unfold mediumPoint
  fun_prop

theorem mediumParameterState_measurable (b : BeamCoefficients) (endTime : ℝ) :
    Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      mediumParameterState b endTime q.1 q.2) := by
  have hfixed (m : HistoryMark) : Measurable (fun q : PhysicalFlightState × EventParameter =>
      mediumParameterState b endTime q.1 (m,q.2)) := by
    have hx : Measurable (fun q : PhysicalFlightState × EventParameter =>
        mediumPoint endTime q.1 q.2.1) :=
      (mediumPoint_measurable endTime).comp
        (show Measurable (fun q : PhysicalFlightState × EventParameter => (q.1,q.2.1)) by fun_prop)
    have hplus : Measurable (fun q : PhysicalFlightState × EventParameter =>
        b.plusPartner (mediumPoint endTime q.1 q.2.1)) := by
      simpa only [Function.comp_def] using b.plusPartner_measurable.comp hx
    have hminus : Measurable (fun q : PhysicalFlightState × EventParameter =>
        b.minusPartner (mediumPoint endTime q.1 q.2.1)) := by
      simpa only [Function.comp_def] using b.minusPartner_measurable.comp hx
    have hv : Measurable (fun q : PhysicalFlightState × EventParameter => q.1.2.2) := by fun_prop
    have hn : Measurable (fun q : PhysicalFlightState × EventParameter => q.2.2) := by fun_prop
    have hu : Measurable (fun q : PhysicalFlightState × EventParameter =>
        markedChild m q.1.2.2 (b.plusPartner (mediumPoint endTime q.1 q.2.1))
          (b.minusPartner (mediumPoint endTime q.1 q.2.1)) q.2.2.1) := by
      unfold markedChild
      split
      · exact hv
      · split
        · simpa only [Function.comp_def] using child_measurable.comp ((hv.prodMk hplus).prodMk hn)
        · simpa only [Function.comp_def] using child_measurable.comp ((hv.prodMk hminus).prodMk hn)
    exact (show Measurable (fun q : PhysicalFlightState × EventParameter => q.1.1-q.2.1) by fun_prop).prodMk
      (hx.snd.prodMk hu)
  have hm : Measurable (fun q : HistoryMark × (PhysicalFlightState × EventParameter) =>
      mediumParameterState b endTime q.2.1 (q.1,q.2.2)) :=
    measurable_from_prod_countable_right hfixed
  simpa only [Function.comp_def] using hm.comp
    (show Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      (q.2.1,(q.1,q.2.2))) by fun_prop)

theorem mediumParameterDensity_measurable (b : BeamCoefficients) (endTime : ℝ) :
    Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      mediumParameterDensity b endTime q.1 q.2) := by
  have hfixed (m : HistoryMark) : Measurable (fun q : PhysicalFlightState × EventParameter =>
      mediumParameterDensity b endTime q.1 (m,q.2)) := by
    have hx : Measurable (fun q : PhysicalFlightState × EventParameter =>
        mediumPoint endTime q.1 q.2.1) :=
      (mediumPoint_measurable endTime).comp
        (show Measurable (fun q : PhysicalFlightState × EventParameter => (q.1,q.2.1)) by fun_prop)
    have hplus : Measurable (fun q : PhysicalFlightState × EventParameter =>
        b.plusPartner (mediumPoint endTime q.1 q.2.1)) := by
      simpa only [Function.comp_def] using b.plusPartner_measurable.comp hx
    have hminus : Measurable (fun q : PhysicalFlightState × EventParameter =>
        b.minusPartner (mediumPoint endTime q.1 q.2.1)) := by
      simpa only [Function.comp_def] using b.minusPartner_measurable.comp hx
    have hrplus : Measurable (fun q : PhysicalFlightState × EventParameter =>
        b.plusDensity (mediumPoint endTime q.1 q.2.1)) := by
      simpa only [Function.comp_def] using b.plusDensity_measurable.comp hx
    have hrminus : Measurable (fun q : PhysicalFlightState × EventParameter =>
        b.minusDensity (mediumPoint endTime q.1 q.2.1)) := by
      simpa only [Function.comp_def] using b.minusDensity_measurable.comp hx
    have hv : Measurable (fun q : PhysicalFlightState × EventParameter => q.1.2.2) := by fun_prop
    have hw : Measurable (fun q : PhysicalFlightState × EventParameter =>
        (Ioc 0 q.1.1).indicator (1 : ℝ → ℝ≥0∞) q.2.1) := by
      let A : Set (PhysicalFlightState × EventParameter) := {q | 0 < q.2.1 ∧ q.2.1 ≤ q.1.1}
      have hA : MeasurableSet A := by dsimp [A]; measurability
      exact measurable_const.indicator hA
    have hc : Measurable (fun q : PhysicalFlightState × EventParameter =>
        clockSurvival referenceClock q.2.1) := by unfold clockSurvival; fun_prop
    have hrate : Measurable (fun q : PhysicalFlightState × EventParameter =>
        markedRate m q.1.2.2 (b.plusPartner (mediumPoint endTime q.1 q.2.1))
          (b.minusPartner (mediumPoint endTime q.1 q.2.1))
          (b.plusDensity (mediumPoint endTime q.1 q.2.1))
          (b.minusDensity (mediumPoint endTime q.1 q.2.1))) := by
      unfold markedRate
      split
      · exact measurable_const.sub (measurable_const.mul
          ((hrplus.mul (hv.sub hplus).norm).add (hrminus.mul (hv.sub hminus).norm)))
      · split
        · exact (measurable_const.mul hrplus).mul (hv.sub hplus).norm
        · exact (measurable_const.mul hrminus).mul (hv.sub hminus).norm
    exact (hw.mul hc).mul hrate.ennreal_ofReal
  have hm : Measurable (fun q : HistoryMark × (PhysicalFlightState × EventParameter) =>
      mediumParameterDensity b endTime q.2.1 (q.1,q.2.2)) :=
    measurable_from_prod_countable_right hfixed
  simpa only [Function.comp_def] using hm.comp
    (show Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      (q.2.1,(q.1,q.2.2))) by fun_prop)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite parameter words in a measurable two-beam medium -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def mediumWordState (b : BeamCoefficients) (endTime : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → PhysicalFlightState
  | 0,p,_ => p
  | n+1,p,a => mediumWordState b endTime n (mediumParameterState b endTime p a.1) a.2

def mediumWordDensity (b : BeamCoefficients) (endTime : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → ℝ≥0∞
  | 0,_,_ => 1
  | n+1,p,a => mediumParameterDensity b endTime p a.1 *
      mediumWordDensity b endTime n (mediumParameterState b endTime p a.1) a.2

theorem mediumWordState_measurable (b : BeamCoefficients) (endTime : ℝ) (n : ℕ) :
    Measurable (fun q : PhysicalFlightState × ParameterWord n => mediumWordState b endTime n q.1 q.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hh : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by fun_prop
    have ht : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => q.2.2) := by fun_prop
    have hs : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) =>
        (mediumParameterState b endTime q.1 q.2.1,q.2.2)) :=
      ((mediumParameterState_measurable b endTime).comp hh).prodMk ht
    exact ih.comp hs

theorem mediumWordDensity_measurable (b : BeamCoefficients) (endTime : ℝ) (n : ℕ) :
    Measurable (fun q : PhysicalFlightState × ParameterWord n => mediumWordDensity b endTime n q.1 q.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hh : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by fun_prop
    have ht : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => q.2.2) := by fun_prop
    have hs : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) =>
        (mediumParameterState b endTime q.1 q.2.1,q.2.2)) :=
      ((mediumParameterState_measurable b endTime).comp hh).prodMk ht
    exact ((mediumParameterDensity_measurable b endTime).comp hh).mul (ih.comp hs)

def GoodReferenceWord : (n : ℕ) → TimeFlightState → ParameterWord n → Prop
  | 0,_,_ => True
  | n+1,p,a => a.1.2.1 ∈ Ioc 0 p.1 ∧
      markedChild a.1.1 p.2.2.1 beamAxis (-beamAxis) a.1.2.2.1 ∈ referenceRegion ∧
      GoodReferenceWord n (markedParameterState p a.1) a.2

theorem goodReferenceWord_of_density_ne_zero (n : ℕ) (p : TimeFlightState)
    (a : ParameterWord n) (h : parameterWordDensity n p a ≠ 0) : GoodReferenceWord n p a := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
    have hparts := mul_ne_zero_iff.mp h
    refine ⟨?_,?_,ih _ a.2 hparts.2⟩
    · by_contra ht
      exact hparts.1 (markedParameterDensity_zero p a.1 ht)
    · by_contra hc
      apply hparts.1
      simp [markedParameterDensity,referenceParameterDensity,markedReferenceWeight,hc]

def WordNearby (b : BeamCoefficients) (endTime ε : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → Prop
  | 0,_,_ => True
  | n+1,p,a =>
      ‖b.plusPartner (mediumPoint endTime p a.1.2.1)-beamAxis‖ ≤ ε ∧
      ‖b.minusPartner (mediumPoint endTime p a.1.2.1)-(-beamAxis)‖ ≤ ε ∧
      |b.plusDensity (mediumPoint endTime p a.1.2.1)-1| ≤ ε ∧
      |b.minusDensity (mediumPoint endTime p a.1.2.1)-1| ≤ ε ∧
      WordNearby b endTime ε n (mediumParameterState b endTime p a.1) a.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Geometric stability of finite marked words along the actual medium path -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem markedParameterState_velocity (p : TimeFlightState) (a : MarkedEventParameter)
    (ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion) :
    (markedParameterState p a).2.2.1 =
      markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 :=
  stateProjection_coe ha

theorem medium_parameter_velocity_error (b : BeamCoefficients) (endTime : ℝ)
    {p : TimeFlightState} {q : PhysicalFlightState} {a : MarkedEventParameter} {δ ε : ℝ}
    (ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion)
    (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (hp : ‖b.plusPartner (mediumPoint endTime q a.2.1)-beamAxis‖ ≤ ε)
    (hm : ‖b.minusPartner (mediumPoint endTime q a.2.1)-(-beamAxis)‖ ≤ ε) :
    ‖(mediumParameterState b endTime q a).2.2-(markedParameterState p a).2.2.1‖ ≤ δ+ε := by
  rw [markedParameterState_velocity p a ha]
  exact marked_child_error a.1 (mem_sphere_zero_iff_norm.mp a.2.2.2) hv hp hm

theorem medium_parameter_position_error (b : BeamCoefficients) (endTime : ℝ)
    {p : TimeFlightState} {q : PhysicalFlightState} {a : MarkedEventParameter} {X δ : ℝ}
    (hs : 0 ≤ a.2.1) (hx : ‖q.2.1-p.2.1‖ ≤ X) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ) :
    ‖(mediumParameterState b endTime q a).2.1-(markedParameterState p a).2.1‖ ≤ X+a.2.1*δ := by
  change ‖(q.2.1+a.2.1 • q.2.2)-(p.2.1+a.2.1 • p.2.2.1)‖ ≤ _
  rw [show (q.2.1+a.2.1 • q.2.2)-(p.2.1+a.2.1 • p.2.2.1) =
    (q.2.1-p.2.1)+a.2.1 • (q.2.2-p.2.2.1) by module]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs]
  exact add_le_add hx (mul_le_mul_of_nonneg_left hv hs)

theorem parameterWordState_time (n : ℕ) (p : TimeFlightState) (a : ParameterWord n)
    (hp : 0 ≤ p.1) (ha : GoodReferenceWord n p a) :
    (parameterWordState n p a).1 ∈ Icc 0 p.1 := by
  induction n generalizing p with
  | zero => exact ⟨hp,le_rfl⟩
  | succ n ih =>
    have hs := markedParameterState_time p a.1 ha.1
    exact ⟨(ih _ a.2 hs.1 ha.2.2).1,(ih _ a.2 hs.1 ha.2.2).2.trans hs.2⟩

theorem medium_word_geometry (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {X δ ε : ℝ} (hε : 0 ≤ ε) (hp : 0 ≤ p.1) (ht : q.1 = p.1)
    (hx : ‖q.2.1-p.2.1‖ ≤ X) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n q a) :
    (mediumWordState b endTime n q a).1 = (parameterWordState n p a).1 ∧
    ‖(mediumWordState b endTime n q a).2.1-(parameterWordState n p a).2.1‖ ≤
      X+p.1*(δ+(n:ℝ)*ε) ∧
    ‖(mediumWordState b endTime n q a).2.2-(parameterWordState n p a).2.2.1‖ ≤ δ+(n:ℝ)*ε := by
  induction n generalizing p q X δ with
  | zero =>
    have hδ : 0 ≤ δ := (norm_nonneg _).trans hv
    exact ⟨ht,by simpa only [mediumWordState,parameterWordState,Nat.cast_zero,zero_mul,add_zero]
      using hx.trans (le_add_of_nonneg_right (mul_nonneg hp hδ)),by simpa [mediumWordState,parameterWordState] using hv⟩
  | succ n ih =>
    have hs := markedParameterState_time p a.1 ha.1
    have ht' : (mediumParameterState b endTime q a.1).1 = (markedParameterState p a.1).1 := by
      change q.1-a.1.2.1 = p.1-a.1.2.1
      rw [ht]
    have hx' := medium_parameter_position_error b endTime ha.1.1.le hx hv
    have hv' := medium_parameter_velocity_error b endTime ha.2.1 hv hb.1 hb.2.1
    have H := ih a.2 hs.1 ht' hx' hv' ha.2.2 hb.2.2.2.2
    refine ⟨H.1,H.2.1.trans ?_,?_⟩
    · change X+a.1.2.1*δ+(p.1-a.1.2.1)*(δ+ε+(n:ℝ)*ε) ≤ _
      have hprod : 0 ≤ a.1.2.1*((n:ℝ)+1)*ε :=
        mul_nonneg (mul_nonneg ha.1.1.le (by positivity)) hε
      push_cast
      nlinarith
    · simpa only [mediumWordState,parameterWordState,Nat.cast_add,Nat.cast_one] using
        H.2.2.trans_eq (by ring)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform one-event bounds for nearby measurable beam coefficients -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem nearby_marked_rate_bounds (m : HistoryMark) {v : V} (u : RetainedState)
    {wp wm : V} {bp bm ε D : ℝ}
    (_hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hD : D ≤ 1)
    (hv : ‖v-u.1‖ ≤ D) (hp : ‖wp-beamAxis‖ ≤ ε) (hm : ‖wm-(-beamAxis)‖ ≤ ε)
    (hbp : |bp-1| ≤ ε) (hbm : |bm-1| ≤ ε) :
    (0 ≤ markedRate m v wp wm bp bm ∧ markedRate m v wp wm bp bm ≤ 48*Real.pi) ∧
    (0 ≤ markedRate m u.1 beamAxis (-beamAxis) 1 1 ∧
      markedRate m u.1 beamAxis (-beamAxis) 1 1 ≤ 48*Real.pi) ∧
    |markedRate m v wp wm bp bm-markedRate m u.1 beamAxis (-beamAxis) 1 1| ≤
      4*Real.pi*(2*D+8*ε) := by
  have hu := retainedState_norm u
  have hv6 : ‖v‖ ≤ 6 := by
    have hh := norm_add_le (v-u.1) u.1
    rw [sub_add_cancel] at hh
    linarith
  have hwp : ‖wp‖ ≤ 2 := by
    have hh := norm_add_le (wp-beamAxis) beamAxis
    rw [sub_add_cancel,axis_norms.2.2] at hh
    linarith
  have hwm : ‖wm‖ ≤ 2 := by
    have hh := norm_add_le (wm-(-beamAxis)) (-beamAxis)
    rw [sub_add_cancel,norm_neg,axis_norms.2.2] at hh
    linarith
  have hbpp := abs_le.mp hbp
  have hbmm := abs_le.mp hbm
  have hp0 : 0 ≤ bp := by linarith
  have hm0 : 0 ≤ bm := by linarith
  have hp1 : bp ≤ 5/4 := by linarith
  have hm1 : bm ≤ 5/4 := by linarith
  refine ⟨marked_rate_bounds m hv6 hwp hwm hp0 hm0 hp1 hm1,
    marked_rate_bounds m (by linarith) (by rw [axis_norms.2.2]; norm_num)
      (by rw [norm_neg,axis_norms.2.2]; norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num),?_⟩
  have hup : ‖u.1-beamAxis‖ ≤ 6 := (norm_sub_le _ _).trans (by rw [axis_norms.2.2]; linarith)
  have hum : ‖u.1-(-beamAxis)‖ ≤ 6 := (norm_sub_le _ _).trans (by rw [norm_neg,axis_norms.2.2]; linarith)
  have H := marked_rate_error m hp0 hm0 (by linarith) (by linarith) hbp hbm
    (add_le_add hv hp) (add_le_add hv hm) hup hum
  convert H using 1
  ring

theorem nearby_parameter_density_bounds (b : BeamCoefficients) (endTime : ℝ)
    {p : TimeFlightState} {q : PhysicalFlightState} {a : MarkedEventParameter} {ε D : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hD : D ≤ 1) (ht : q.1 = p.1)
    (hv : ‖q.2.2-p.2.2.1‖ ≤ D) (hs : a.2.1 ∈ Ioc 0 p.1)
    (ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion)
    (hp : ‖b.plusPartner (mediumPoint endTime q a.2.1)-beamAxis‖ ≤ ε)
    (hm : ‖b.minusPartner (mediumPoint endTime q a.2.1)-(-beamAxis)‖ ≤ ε)
    (hbp : |b.plusDensity (mediumPoint endTime q a.2.1)-1| ≤ ε)
    (hbm : |b.minusDensity (mediumPoint endTime q a.2.1)-1| ≤ ε) :
    markedParameterDensity p a ≤ ENNReal.ofReal (48*Real.pi) ∧
    mediumParameterDensity b endTime q a ≤ ENNReal.ofReal (48*Real.pi) ∧
    markedParameterDensity p a ≤ mediumParameterDensity b endTime q a +
      ENNReal.ofReal (4*Real.pi*(2*D+8*ε)) := by
  have H := nearby_marked_rate_bounds a.1 p.2.2 hε hε1 hD hv hp hm hbp hbm
  have hc := clockSurvival_le_one referenceClock hs.1.le
  have hδ : 0 ≤ 4*Real.pi*(2*D+8*ε) := by
    have : 0 ≤ D := (norm_nonneg _).trans hv
    positivity
  have hr : ENNReal.ofReal (markedRate a.1 p.2.2.1 beamAxis (-beamAxis) 1 1) ≤
      ENNReal.ofReal (markedRate a.1 q.2.2
        (b.plusPartner (mediumPoint endTime q a.2.1))
        (b.minusPartner (mediumPoint endTime q a.2.1))
        (b.plusDensity (mediumPoint endTime q a.2.1))
        (b.minusDensity (mediumPoint endTime q a.2.1))) +
      ENNReal.ofReal (4*Real.pi*(2*D+8*ε)) := by
    rw [← ENNReal.ofReal_add H.1.1 hδ]
    apply ENNReal.ofReal_le_ofReal
    have hdiff := H.2.2
    rw [abs_sub_comm] at hdiff
    linarith [le_abs_self (markedRate a.1 p.2.2.1 beamAxis (-beamAxis) 1 1 -
      markedRate a.1 q.2.2 (b.plusPartner (mediumPoint endTime q a.2.1))
        (b.minusPartner (mediumPoint endTime q a.2.1))
        (b.plusDensity (mediumPoint endTime q a.2.1))
        (b.minusDensity (mediumPoint endTime q a.2.1)))]
  simp only [markedParameterDensity,referenceParameterDensity,waitingDensity,
    markedReferenceWeight,mediumParameterDensity,ht,indicator_of_mem hs,indicator_of_mem ha,
    Pi.one_apply,one_mul,mul_one]
  refine ⟨(mul_le_of_le_one_left' hc).trans (ENNReal.ofReal_le_ofReal H.2.1.2),
    (mul_le_of_le_one_left' hc).trans (ENNReal.ofReal_le_ofReal H.1.2),?_⟩
  calc
    _ ≤ clockSurvival referenceClock a.2.1 * (_+_) := mul_le_mul' le_rfl hr
    _ = _ := mul_add _ _ _
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' hc)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite positive-history weights remain close under beam perturbations -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def wordWeightError (M : ℝ≥0∞) : ℕ → ℝ≥0∞
  | 0 => 0
  | n+1 => M^n+M*wordWeightError M n

theorem wordWeightError_ne_top {M : ℝ≥0∞} (hM : M ≠ ⊤) (n : ℕ) :
    wordWeightError M n ≠ ⊤ := by
  induction n with
  | zero => exact ENNReal.zero_ne_top
  | succ n ih =>
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top hM,ENNReal.mul_ne_top hM ih⟩

def WordCoefficientClose (b : BeamCoefficients) (endTime : ℝ) (M η : ℝ≥0∞) :
    (n : ℕ) → TimeFlightState → PhysicalFlightState → ParameterWord n → Prop
  | 0,_,_,_ => True
  | n+1,p,q,a =>
      markedParameterDensity p a.1 ≤ M ∧ mediumParameterDensity b endTime q a.1 ≤ M ∧
      markedParameterDensity p a.1 ≤ mediumParameterDensity b endTime q a.1+η ∧
      WordCoefficientClose b endTime M η n (markedParameterState p a.1)
        (mediumParameterState b endTime q a.1) a.2

theorem word_weight_comparison (b : BeamCoefficients) (endTime : ℝ) (M η : ℝ≥0∞)
    (n : ℕ) (p : TimeFlightState) (q : PhysicalFlightState) (a : ParameterWord n)
    (h : WordCoefficientClose b endTime M η n p q a) :
    parameterWordDensity n p a ≤ M^n ∧ mediumWordDensity b endTime n q a ≤ M^n ∧
    parameterWordDensity n p a ≤ mediumWordDensity b endTime n q a+wordWeightError M n*η := by
  induction n generalizing p q with
  | zero => simp [parameterWordDensity,mediumWordDensity,wordWeightError]
  | succ n ih =>
    obtain ⟨hR,hA,hRA⟩ := ih _ _ a.2 h.2.2.2
    refine ⟨?_,?_,?_⟩
    · exact (mul_le_mul' h.1 hR).trans_eq (pow_succ' M n).symm
    · exact (mul_le_mul' h.2.1 hA).trans_eq (pow_succ' M n).symm
    · change markedParameterDensity p a.1 *
          parameterWordDensity n (markedParameterState p a.1) a.2 ≤
        mediumParameterDensity b endTime q a.1 *
          mediumWordDensity b endTime n (mediumParameterState b endTime q a.1) a.2+_
      calc
        _ ≤ markedParameterDensity p a.1 *
            (mediumWordDensity b endTime n (mediumParameterState b endTime q a.1) a.2+
              wordWeightError M n*η) := mul_le_mul' le_rfl hRA
        _ = markedParameterDensity p a.1 *
              mediumWordDensity b endTime n (mediumParameterState b endTime q a.1) a.2+
              markedParameterDensity p a.1*(wordWeightError M n*η) := mul_add _ _ _
        _ ≤ (mediumParameterDensity b endTime q a.1+η)*
              mediumWordDensity b endTime n (mediumParameterState b endTime q a.1) a.2+
              M*(wordWeightError M n*η) :=
          add_le_add (mul_le_mul' h.2.2.1 le_rfl) (mul_le_mul' h.1 le_rfl)
        _ = mediumParameterDensity b endTime q a.1 *
              mediumWordDensity b endTime n (mediumParameterState b endTime q a.1) a.2+
              η*mediumWordDensity b endTime n (mediumParameterState b endTime q a.1) a.2+
              M*(wordWeightError M n*η) := by rw [add_mul]
        _ ≤ mediumParameterDensity b endTime q a.1 *
              mediumWordDensity b endTime n (mediumParameterState b endTime q a.1) a.2+
              η*M^n+M*(wordWeightError M n*η) :=
          add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hA)) le_rfl
        _ = _ := by simp only [wordWeightError]; ring

theorem word_coefficients_close (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {δ ε D : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hD : D ≤ 1)
    (hbudget : δ+(n:ℝ)*ε ≤ D) (ht : q.1 = p.1) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n q a) :
    WordCoefficientClose b endTime (ENNReal.ofReal (48*Real.pi))
      (ENNReal.ofReal (4*Real.pi*(2*D+8*ε))) n p q a := by
  induction n generalizing p q δ with
  | zero => trivial
  | succ n ih =>
    have hvD : ‖q.2.2-p.2.2.1‖ ≤ D := hv.trans (by nlinarith)
    have H := nearby_parameter_density_bounds b endTime hε hε1 hD ht hvD
      ha.1 ha.2.1 hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
    refine ⟨H.1,H.2.1,H.2.2,?_⟩
    apply ih a.2 (δ := δ+ε)
    · push_cast at hbudget ⊢
      linarith
    · change q.1-a.1.2.1 = p.1-a.1.2.1
      rw [ht]
    · exact medium_parameter_velocity_error b endTime ha.2.1 hv hb.1 hb.2.1
    · exact ha.2.2
    · exact hb.2.2.2.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Local coefficient control suffices along every retained finite word -/

noncomputable section

open Set

namespace BoltzmannNonuniqueness.ReferenceGeometry

def BeamNear (b : BeamCoefficients) (ε : ℝ) (p : ℝ × V) : Prop :=
  ‖b.plusPartner p-beamAxis‖ ≤ ε ∧ ‖b.minusPartner p-(-beamAxis)‖ ≤ ε ∧
    |b.plusDensity p-1| ≤ ε ∧ |b.minusDensity p-1| ≤ ε

theorem wordNearby_of_excursion (b : BeamCoefficients) (endTime A : ℝ) (x₀ : V)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hnear : ∀ y : ℝ × V, y.1 ∈ Icc (endTime-A) endTime → ‖y.2-x₀‖ ≤ 6*A → BeamNear b ε y)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {δ : ℝ} (hbudget : δ+(n:ℝ)*ε ≤ 1) (hp : p.1 ∈ Icc 0 A) (ht : q.1 = p.1)
    (hx : ‖q.2.1-x₀‖ ≤ 6*(A-p.1)) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) : WordNearby b endTime ε n q a := by
  induction n generalizing p q δ with
  | zero => trivial
  | succ n ih =>
    have hs : a.1.2.1 ∈ Ioc 0 p.1 := ha.1
    have hδ : δ ≤ 1 := by nlinarith
    have hv6 : ‖q.2.2‖ ≤ 6 := by
      have hh := norm_add_le (q.2.2-p.2.2.1) p.2.2.1
      rw [sub_add_cancel] at hh
      linarith [retainedState_norm p.2.2]
    have hytime : (mediumPoint endTime q a.1.2.1).1 ∈ Icc (endTime-A) endTime := by
      change endTime-q.1+a.1.2.1 ∈ Icc (endTime-A) endTime
      rw [ht]
      constructor <;> linarith [hp.1,hp.2,hs.1,hs.2]
    have hypos : ‖(mediumPoint endTime q a.1.2.1).2-x₀‖ ≤ 6*(A-(p.1-a.1.2.1)) := by
      change ‖q.2.1+a.1.2.1 • q.2.2-x₀‖ ≤ _
      rw [show q.2.1+a.1.2.1 • q.2.2-x₀ = (q.2.1-x₀)+a.1.2.1 • q.2.2 by module]
      have hnorm := norm_add_le (q.2.1-x₀) (a.1.2.1 • q.2.2)
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hs.1.le] at hnorm
      have hmul := mul_le_mul_of_nonneg_left hv6 hs.1.le
      linarith
    have hybound : ‖(mediumPoint endTime q a.1.2.1).2-x₀‖ ≤ 6*A := hypos.trans (by linarith [hs.2])
    have hb := hnear (mediumPoint endTime q a.1.2.1) hytime hybound
    refine ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2,?_⟩
    apply ih a.2 (p := markedParameterState p a.1) (δ := δ+ε)
    · push_cast at hbudget ⊢
      linarith
    · change p.1-a.1.2.1 ∈ Icc 0 A
      constructor <;> linarith [hp.2,hs.1,hs.2]
    · change q.1-a.1.2.1 = p.1-a.1.2.1
      rw [ht]
    · exact hypos
    · exact medium_parameter_velocity_error b endTime ha.2.1 hv hb.1 hb.2.1
    · exact ha.2.2

theorem wordNearby_from_start (b : BeamCoefficients) (endTime A : ℝ) (z : FlightState)
    {ε : ℝ} (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hnear : ∀ y : ℝ × V, y.1 ∈ Icc (endTime-A) endTime → ‖y.2-z.1‖ ≤ 6*A → BeamNear b ε y)
    (n : ℕ) (hn : (n:ℝ)*ε ≤ 1) (a : ParameterWord n) (ha : GoodReferenceWord n (A,z) a) :
    WordNearby b endTime ε n (embedFlightState (A,z)) a := by
  apply wordNearby_of_excursion b endTime A z.1 hε hnear n (p := (A,z)) a (δ := 0)
  · simpa using hn
  · exact ⟨hA,le_rfl⟩
  · rfl
  · simp [embedFlightState]
  · simp [embedFlightState]
  · exact ha

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Endpoint margins for the same finite marked parameters in the nearby medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def finishMediumFlight (p : PhysicalFlightState) : V × V :=
  (p.2.1+p.1 • p.2.2,p.2.2)

theorem finishMediumFlight_error {p : TimeFlightState} {q : PhysicalFlightState} {X δ : ℝ}
    (hp : 0 ≤ p.1) (ht : q.1 = p.1)
    (hx : ‖q.2.1-p.2.1‖ ≤ X) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ) :
    ‖(finishMediumFlight q).1-(finishFlight p).1‖ ≤ X+p.1*δ := by
  change ‖(q.2.1+q.1 • q.2.2)-(p.2.1+p.1 • p.2.2.1)‖ ≤ _
  rw [ht,show (q.2.1+p.1 • q.2.2)-(p.2.1+p.1 • p.2.2.1) =
    (q.2.1-p.2.1)+p.1 • (q.2.2-p.2.2.1) by module]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hp]
  exact add_le_add hx (mul_le_mul_of_nonneg_left hv hp)

theorem medium_word_endpoint_error (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε : ℝ}
    (hε : 0 ≤ ε) (hp : 0 ≤ p.1) (ha : GoodReferenceWord n p a)
    (hb : WordNearby b endTime ε n (embedFlightState p) a) :
    ‖(finishMediumFlight (mediumWordState b endTime n (embedFlightState p) a)).1-
      (finishFlight (parameterWordState n p a)).1‖ ≤ 2*p.1*((n:ℝ)*ε) ∧
    ‖(finishMediumFlight (mediumWordState b endTime n (embedFlightState p) a)).2-
      (finishFlight (parameterWordState n p a)).2.1‖ ≤ (n:ℝ)*ε := by
  have H := medium_word_geometry b endTime n a (X := 0) (δ := 0) hε hp rfl
    (by simp [embedFlightState]) (by simp [embedFlightState]) ha hb
  simp only [zero_add] at H
  have ht := parameterWordState_time n p a hp ha
  refine ⟨?_,H.2.2⟩
  have hh := finishMediumFlight_error ht.1 H.1 H.2.1 H.2.2
  refine hh.trans ?_
  calc
    p.1*((n:ℝ)*ε)+(parameterWordState n p a).1*((n:ℝ)*ε)
        ≤ p.1*((n:ℝ)*ε)+p.1*((n:ℝ)*ε) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right ht.2 (by positivity))
    _ = _ := by ring

theorem medium_word_target (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hp : 0 ≤ p.1) (hv : (n:ℝ)*ε ≤ 1)
    (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n (embedFlightState p) a)
    (hmem : finishFlight (parameterWordState n p a) ∈ blockTarget p.2.1 p.1 κ d) :
    finishMediumFlight (mediumWordState b endTime n (embedFlightState p) a) ∈
      physicalBlockTarget p.2.1 p.1 κ d := by
  have H := medium_word_endpoint_error b endTime n p a hε hp ha hb
  exact block_target_perturb hmem (H.1.trans hx) (H.2.trans hv)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower transfer of the finite reference histories to a nearby measurable medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def mediumBlockIntegrand (b : BeamCoefficients) (endTime : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (n : ℕ) (a : ParameterWord n) : ℝ≥0∞ :=
  let q := mediumWordState b endTime n (embedFlightState p) a
  mediumWordDensity b endTime n (embedFlightState p) a *
    (clockSurvival referenceClock q.1 *
      (physicalBlockTarget p.2.1 p.1 κ d).indicator 1 (finishMediumFlight q))

def historyPerturbationError (n : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  wordWeightError (ENNReal.ofReal (48*Real.pi)) n *
    ENNReal.ofReal (4*Real.pi*((2*(n:ℝ)+8)*ε))

theorem medium_word_integrand_bound (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hv : (n:ℝ)*ε ≤ 1)
    (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    parameterWordDensity n p a * flightSeed referenceClock
        ((blockTarget p.2.1 p.1 κ d).indicator 1) (parameterWordState n p a) ≤
      mediumBlockIntegrand b endTime p κ d n a+historyPerturbationError n ε := by
  by_cases hr : parameterWordDensity n p a = 0
  · rw [hr,zero_mul]
    exact bot_le
  have ha := goodReferenceWord_of_density_ne_zero n p a hr
  have hb := hnear ha
  by_cases hmem : finishFlight (parameterWordState n p a) ∈ blockTarget p.2.1 p.1 κ d
  · have hm := medium_word_target b endTime n p a hε hp hv hx ha hb hmem
    have ht := (medium_word_geometry b endTime n a (X := 0) (δ := 0) hε hp rfl
      (by simp [embedFlightState]) (by simp [embedFlightState]) ha hb).1
    have H := word_coefficients_close b endTime n a (δ := 0) (D := (n:ℝ)*ε)
      hε hε1 hv (by simp) rfl (by simp [embedFlightState]) ha hb
    have hweight := (word_weight_comparison b endTime _ _ n p (embedFlightState p) a H).2.2
    have he : ENNReal.ofReal (4*Real.pi*(2*((n:ℝ)*ε)+8*ε)) =
        ENNReal.ofReal (4*Real.pi*((2*(n:ℝ)+8)*ε)) := by congr 1; ring
    rw [he] at hweight
    have hc := clockSurvival_le_one referenceClock (parameterWordState_time n p a hp ha).1
    simp only [flightSeed,mediumBlockIntegrand,indicator_of_mem hmem,indicator_of_mem hm,
      Pi.one_apply,mul_one,ht]
    calc
      _ ≤ (mediumWordDensity b endTime n (embedFlightState p) a+
          historyPerturbationError n ε)*clockSurvival referenceClock (parameterWordState n p a).1 :=
        mul_le_mul' hweight le_rfl
      _ = _ := add_mul _ _ _
      _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hc)
  · simp only [flightSeed,indicator_of_notMem hmem,mul_zero]
    exact bot_le

theorem medium_word_integral_lower (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (T : ℝ) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hpT : p.1 ≤ T)
    (hv : (n:ℝ)*ε ≤ 1) (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : ∀ a, GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    eventHistory referenceClock branchingKernel
        (flightSeed referenceClock ((blockTarget p.2.1 p.1 κ d).indicator 1)) n p ≤
      (∫⁻ a, mediumBlockIntegrand b endTime p κ d n a ∂parameterWordMeasure T n)+
        historyPerturbationError n ε*(3*ENNReal.ofReal T)^n := by
  have hf : Measurable ((blockTarget p.2.1 p.1 κ d).indicator (1 : FlightState → ℝ≥0∞)) :=
    measurable_const.indicator (blockTarget_measurable _ _ _ _)
  rw [← parameterWord_integral (flightSeed_measurable referenceClock hf) T n p ⟨hp,hpT⟩]
  calc
    _ ≤ ∫⁻ a, mediumBlockIntegrand b endTime p κ d n a+historyPerturbationError n ε
        ∂parameterWordMeasure T n :=
      lintegral_mono (fun a => medium_word_integrand_bound b endTime n p a hε hε1 hp hv hx (hnear a))
    _ = _ := by rw [lintegral_add_right _ measurable_const,lintegral_const,parameterWordMeasure_mass]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniform smallness of the finite-history perturbation error -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem historyPerturbationError_continuous (n : ℕ) : Continuous (historyPerturbationError n) := by
  exact (ENNReal.continuous_const_mul (wordWeightError_ne_top ENNReal.ofReal_ne_top n)).comp
    (ENNReal.continuous_ofReal.comp (by fun_prop))

def finiteHistoryError (N : ℕ) (T ε : ℝ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, historyPerturbationError n ε*(3*ENNReal.ofReal T)^n

theorem finiteHistoryError_continuous (N : ℕ) (T : ℝ) : Continuous (finiteHistoryError N T) := by
  apply continuous_finsetSum
  intro n _hn
  exact (ENNReal.continuous_mul_const (ENNReal.pow_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))).comp
      (historyPerturbationError_continuous n)

theorem finiteHistoryError_zero (N : ℕ) (T : ℝ) : finiteHistoryError N T 0 = 0 := by
  simp [finiteHistoryError,historyPerturbationError]

theorem finiteHistoryError_small (N : ℕ) (T : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc 0 ε₀, finiteHistoryError N T ε < 1 := by
  have hh : ∀ᶠ ε in 𝓝 (0 : ℝ), finiteHistoryError N T ε < 1 :=
    (finiteHistoryError_continuous N T).continuousAt.eventually
      (gt_mem_nhds (by rw [finiteHistoryError_zero]; norm_num))
  obtain ⟨r,hr,hsmall⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨r/2,by positivity,fun ε hε => hsmall ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hε.1]
  exact hε.2.trans_lt (half_lt_self hr)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniformly positive finite branching blocks in a nearby measurable medium -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def mediumBlockMass (b : BeamCoefficients) (endTime T : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, ∫⁻ a, mediumBlockIntegrand b endTime p κ d n a ∂parameterWordMeasure T n

theorem finite_history_block_transfer (N : ℕ) (T : ℝ) {κ d : ℝ}
    (hκ : 0 < κ) (hd : 0 < d) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc 0 T, ∀ z : FlightState,
      (7 : ℝ≥0∞) < (∑ n ∈ Finset.range N, eventHistory referenceClock branchingKernel
        (flightSeed referenceClock ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) →
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < mediumBlockMass b endTime T (A,z) κ d N := by
  obtain ⟨r,hr,hrsmall⟩ := finiteHistoryError_small N T
  let L : ℝ := (N:ℝ)+1
  have hL : 0 < L := by dsimp [L]; positivity
  let ε₀ := min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r))
  have hε₀ : 0 < ε₀ := by
    dsimp [ε₀]
    simp only [lt_min_iff]
    exact ⟨by norm_num,one_div_pos.mpr hL,by positivity,hr⟩
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε A hA z href b endTime hnear
  have hcut : ε ≤ min (1/4:ℝ) (min (1/L) (min ((d*κ/8)/L) r)) := hε.2
  have hquarter := hcut.trans (min_le_left _ _)
  have htail := hcut.trans (min_le_right _ _)
  have hεL := htail.trans (min_le_left _ _)
  have htail' := htail.trans (min_le_right _ _)
  have hεd := htail'.trans (min_le_left _ _)
  have hεr := htail'.trans (min_le_right _ _)
  have hmass := hrsmall ε ⟨hε.1,hεr⟩
  have hsum : (∑ n ∈ Finset.range N, eventHistory referenceClock branchingKernel
      (flightSeed referenceClock ((blockTarget z.1 A κ d).indicator 1)) n (A,z)) ≤
      mediumBlockMass b endTime T (A,z) κ d N+finiteHistoryError N T ε := by
    calc
      _ ≤ ∑ n ∈ Finset.range N,
          ((∫⁻ a, mediumBlockIntegrand b endTime (A,z) κ d n a ∂parameterWordMeasure T n)+
            historyPerturbationError n ε*(3*ENNReal.ofReal T)^n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnN := (Finset.mem_range.mp hn).le
        have hnL : (n:ℝ) ≤ L :=
          (Nat.cast_le.mpr hnN).trans (le_add_of_nonneg_right (by norm_num))
        have hv : (n:ℝ)*ε ≤ 1 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεL)
        have hx' : (n:ℝ)*ε ≤ d*κ/8 :=
          (mul_le_mul_of_nonneg_right hnL hε.1).trans
            (by simpa only [mul_comm] using (le_div_iff₀ hL).mp hεd)
        have hx : 2*A*((n:ℝ)*ε) ≤ d*κ*A/4 := by
          convert mul_le_mul_of_nonneg_left hx' (show 0 ≤ (2:ℝ)*A from mul_nonneg (by norm_num) hA.1) using 1
          ring
        exact medium_word_integral_lower b endTime n (A,z) T hε.1 hquarter hA.1 hA.2
          hv hx (hnear n (Finset.mem_range.mp hn))
      _ = _ := by rw [Finset.sum_add_distrib]; rfl
  by_contra hbad
  have hupper := hsum.trans (add_le_add (le_of_not_gt hbad) hmass.le)
  norm_num at hupper
  exact (not_lt_of_ge hupper) href

theorem uniform_perturbed_block_growth {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∃ N : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε ∈ Icc 0 ε₀, ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
      ∀ (b : BeamCoefficients) (endTime : ℝ),
      (∀ n < N, ∀ a : ParameterWord n, GoodReferenceWord n (A,z) a →
        WordNearby b endTime ε n (embedFlightState (A,z)) a) →
      (6 : ℝ≥0∞) < mediumBlockMass b endTime T (A,z) κ d N := by
  obtain ⟨A₀,hA₀,hdepth⟩ := uniform_finite_branching_block_growth hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T hT
  obtain ⟨N,hN⟩ := hdepth T hT
  obtain ⟨ε₀,hε₀,htransfer⟩ := finite_history_block_transfer N T hκ hd
  refine ⟨N,ε₀,hε₀,?_⟩
  intro ε hε A hA z b endTime hnear
  exact htransfer ε hε A ⟨hA₀.le.trans hA.1,hA.2⟩ z (hN A hA z) b endTime hnear

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
