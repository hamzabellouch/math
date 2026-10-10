import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveIntegralFixedPoint
import OAI.MathematicalPhysics.Boltzmann.Branching.MediumStateCollision
import OAI.MathematicalPhysics.Boltzmann.Branching.PerturbedFiniteBlock
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceGrowthBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.SpacetimeFourierCoordinates
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityFourierMultiplier

namespace OAI

section

/-! # Time-uniform contraction estimates for the positive damped integral -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.PositiveIntegral

theorem exponential_integral {L : ℝ} (hL : 0 < L) (t : ℝ) :
    (∫ r in 0..t, Real.exp (-L*(t-r))) = (1-Real.exp (-L*t))/L := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => Real.exp (-L*(t-r))/L)
      (Real.exp (-L*(t-r))) r := by
    convert (((hasDerivAt_const r t).sub (hasDerivAt_id r)).const_mul (-L)).exp.div_const L using 1
    · rfl
    · dsimp only [Pi.sub_apply, id_eq]
      field_simp [hL.ne']
      ring
  have hi : IntervalIntegrable (fun r : ℝ => Real.exp (-L*(t-r))) volume 0 t :=
    (by fun_prop : Continuous (fun r : ℝ => Real.exp (-L*(t-r)))).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hd r) hi
  simpa only [sub_self,mul_zero,Real.exp_zero,sub_zero,div_sub_div_same] using h

variable {P : Type*} [MeasurableSpace P]

theorem value_damped_bound {T L R : ℝ} (hT : 0 ≤ T) (hL : 0 < L) (hR : 0 ≤ R)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ : P → ℝ} (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ R)
    {g : Domain P → ℝ} (hgm : Measurable g) (hg : ∀ z, 0 ≤ g z ∧ g z ≤ L*R)
    (z : Domain P) : 0 ≤ value T L flow f₀ g z ∧ value T L flow f₀ g z ≤ R := by
  have ht := time_bounds hT z.1
  have hgi := damped_integrable hT hL.le hflow hgm
    (fun z => (abs_of_nonneg (hg z).1).trans_le (hg z).2) z
  have hci : IntervalIntegrable (fun r : ℝ => Real.exp (-L*(time T z.1-r))*(L*R))
      volume 0 (time T z.1) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hb := intervalIntegral.integral_mono_on ht.1 hgi hci (fun r _ =>
    mul_le_mul_of_nonneg_left (hg _).2 (Real.exp_pos _).le)
  have he : (∫ r in 0..time T z.1, Real.exp (-L*(time T z.1-r))*(L*R)) =
      R*(1-Real.exp (-L*time T z.1)) := by
    rw [intervalIntegral.integral_mul_const,exponential_integral hL]
    field_simp [hL.ne']
  rw [he] at hb
  have hinit := mul_le_mul_of_nonneg_left (hf₀ (flow (-time T z.1) z.2)).2
    (Real.exp_pos (-L*time T z.1)).le
  exact ⟨(value_bounds hT hL.le hR (mul_nonneg hL.le hR) flow hf₀ hg z).1,by
    unfold value
    linarith⟩

theorem value_damped_difference {T L S D : ℝ} (hT : 0 ≤ T) (hL : 0 < L) (hD : 0 ≤ D)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    (f₀ : P → ℝ) {g h : Domain P → ℝ} (hgm : Measurable g) (hhm : Measurable h)
    (hg : ∀ z, |g z| ≤ S) (hh : ∀ z, |h z| ≤ S) (hgh : ∀ z, |g z-h z| ≤ D)
    (z : Domain P) : |value T L flow f₀ g z-value T L flow f₀ h z| ≤ D/L := by
  have ht := time_bounds hT z.1
  have hgi := damped_integrable hT hL.le hflow hgm hg z
  have hhi := damped_integrable hT hL.le hflow hhm hh z
  unfold value
  rw [add_sub_add_left_eq_sub,← intervalIntegral.integral_sub hgi hhi]
  have hci : IntervalIntegrable (fun r : ℝ => Real.exp (-L*(time T z.1-r))*D)
      volume 0 (time T z.1) := (by fun_prop : Continuous _).intervalIntegrable _ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le ht.1
    (f := fun r => Real.exp (-L*(time T z.1-r))*g (r,flow (r-time T z.1) z.2)-
      Real.exp (-L*(time T z.1-r))*h (r,flow (r-time T z.1) z.2))
    (g := fun r => Real.exp (-L*(time T z.1-r))*D) (by
      filter_upwards [] with r
      intro _hr
      rw [← mul_sub,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hgh _) (Real.exp_pos _).le) hci
  rw [Real.norm_eq_abs,intervalIntegral.integral_mul_const,exponential_integral hL] at hb
  have hn : 0 ≤ Real.exp (-L*time T z.1) := (Real.exp_pos _).le
  calc
    _ ≤ (1-Real.exp (-L*time T z.1))/L*D := hb
    _ ≤ 1/L*D := by gcongr; linarith
    _ = D/L := by ring

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Marked reference and medium weights with an additional holding intensity -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def holdingWeight (C : ℝ≥0) (m : HistoryMark) : ℝ≥0∞ :=
  if m = 0 then ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) else 0

def dampedReferenceWeight (C : ℝ≥0) (v : RetainedState) (m : HistoryMark) (n : Sphere) : ℝ≥0∞ :=
  markedReferenceWeight v m n+holdingWeight C m

def dampedParameterDensity (C : ℝ≥0) (p : TimeFlightState) (a : MarkedEventParameter) : ℝ≥0∞ :=
  waitingDensity p a.2.1*clockSurvival C a.2.1*dampedReferenceWeight C p.2.2 a.1 a.2.2

def dampedMediumParameterDensity (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (a : MarkedEventParameter) : ℝ≥0∞ :=
  let x := mediumPoint endTime p a.2.1
  (Ioc 0 p.1).indicator 1 a.2.1*clockSurvival C a.2.1*
    (ENNReal.ofReal (markedRate a.1 p.2.2 (b.plusPartner x) (b.minusPartner x)
      (b.plusDensity x) (b.minusDensity x))+holdingWeight C a.1)

theorem holdingWeight_measurable (C : ℝ≥0) : Measurable (holdingWeight C) :=
  measurable_of_countable _

theorem dampedParameterDensity_measurable (C : ℝ≥0) :
    Measurable (fun q : TimeFlightState × MarkedEventParameter => dampedParameterDensity C q.1 q.2) := by
  have hw : Measurable (fun q : TimeFlightState × MarkedEventParameter => waitingDensity q.1 q.2.2.1) :=
    waitingDensity_measurable.comp (show Measurable (fun q : TimeFlightState × MarkedEventParameter => (q.1,q.2.2.1)) by fun_prop)
  have hc : Measurable (fun q : TimeFlightState × MarkedEventParameter => clockSurvival C q.2.2.1) := by
    unfold clockSurvival
    fun_prop
  have hm : Measurable (fun q : TimeFlightState × MarkedEventParameter =>
      markedReferenceWeight q.1.2.2 q.2.1 q.2.2.2) := by
    have h : Measurable (fun q : HistoryMark × (RetainedState × Sphere) => markedReferenceWeight q.2.1 q.1 q.2.2) :=
      measurable_from_prod_countable_right (fun m : HistoryMark => markedReferenceWeight_measurable m)
    exact h.comp (show Measurable (fun q : TimeFlightState × MarkedEventParameter => (q.2.1,(q.1.2.2,q.2.2.2))) by fun_prop)
  exact (hw.mul hc).mul (hm.add ((holdingWeight_measurable C).comp (by fun_prop)))

theorem dampedMediumParameterDensity_measurable (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      dampedMediumParameterDensity C b endTime q.1 q.2) := by
  have hfixed (m : HistoryMark) : Measurable (fun q : PhysicalFlightState × EventParameter =>
      dampedMediumParameterDensity C b endTime q.1 (m,q.2)) := by
    have hx : Measurable (fun q : PhysicalFlightState × EventParameter => mediumPoint endTime q.1 q.2.1) :=
      (mediumPoint_measurable endTime).comp (show Measurable (fun q : PhysicalFlightState × EventParameter => (q.1,q.2.1)) by fun_prop)
    have hplus := b.plusPartner_measurable.comp hx
    have hminus := b.minusPartner_measurable.comp hx
    have hrplus := b.plusDensity_measurable.comp hx
    have hrminus := b.minusDensity_measurable.comp hx
    have hv : Measurable (fun q : PhysicalFlightState × EventParameter => q.1.2.2) := by fun_prop
    have hw : Measurable (fun q : PhysicalFlightState × EventParameter =>
        (Ioc 0 q.1.1).indicator (1 : ℝ → ℝ≥0∞) q.2.1) := by
      let A : Set (PhysicalFlightState × EventParameter) := {q | 0 < q.2.1 ∧ q.2.1 ≤ q.1.1}
      have hA : MeasurableSet A := by dsimp [A]; measurability
      exact measurable_const.indicator hA
    have hc : Measurable (fun q : PhysicalFlightState × EventParameter => clockSurvival C q.2.1) := by
      unfold clockSurvival
      fun_prop
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
    exact (hw.mul hc).mul (hrate.ennreal_ofReal.add (measurable_const : Measurable (fun _ : PhysicalFlightState × EventParameter => holdingWeight C m)))
  have hm : Measurable (fun q : HistoryMark × (PhysicalFlightState × EventParameter) =>
      dampedMediumParameterDensity C b endTime q.2.1 (q.1,q.2.2)) :=
    measurable_from_prod_countable_right hfixed
  exact hm.comp (show Measurable (fun q : PhysicalFlightState × MarkedEventParameter => (q.2.1,(q.1,q.2.2))) by fun_prop)

theorem holdingWeight_le {C : ℝ≥0} (m : HistoryMark) :
    holdingWeight C m ≤ ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) := by
  unfold holdingWeight
  split
  · exact le_rfl
  · exact bot_le

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The extra holding intensity preserves the local perturbation error -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem rate_add_holding_le {C : ℝ≥0} (hC : referenceClock ≤ C)
    {r : ℝ} (hr : r ≤ (referenceClock:ℝ)) (m : HistoryMark) :
    ENNReal.ofReal r+holdingWeight C m ≤ ENNReal.ofReal (C:ℝ) := by
  calc
    _ ≤ ENNReal.ofReal (referenceClock:ℝ)+ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) :=
      add_le_add (ENNReal.ofReal_le_ofReal hr) (holdingWeight_le m)
    _ = _ := by
      rw [← ENNReal.ofReal_add (show 0 ≤ (referenceClock:ℝ) from referenceClock.property)
        (show 0 ≤ (C:ℝ)-(referenceClock:ℝ) from sub_nonneg.mpr hC)]
      congr 1
      ring

theorem nearby_damped_parameter_bounds {C Cmax : ℝ≥0} (hC : referenceClock ≤ C) (hCmax : C ≤ Cmax)
    (b : BeamCoefficients) (endTime : ℝ)
    {p : TimeFlightState} {q : PhysicalFlightState} {a : MarkedEventParameter} {ε D : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hD : D ≤ 1) (ht : q.1 = p.1)
    (hv : ‖q.2.2-p.2.2.1‖ ≤ D) (hs : a.2.1 ∈ Ioc 0 p.1)
    (ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion)
    (hp : ‖b.plusPartner (mediumPoint endTime q a.2.1)-beamAxis‖ ≤ ε)
    (hm : ‖b.minusPartner (mediumPoint endTime q a.2.1)-(-beamAxis)‖ ≤ ε)
    (hbp : |b.plusDensity (mediumPoint endTime q a.2.1)-1| ≤ ε)
    (hbm : |b.minusDensity (mediumPoint endTime q a.2.1)-1| ≤ ε) :
    dampedParameterDensity C p a ≤ ENNReal.ofReal (Cmax:ℝ) ∧
    dampedMediumParameterDensity C b endTime q a ≤ ENNReal.ofReal (Cmax:ℝ) ∧
    dampedParameterDensity C p a ≤ dampedMediumParameterDensity C b endTime q a+
      ENNReal.ofReal (4*Real.pi*(2*D+8*ε)) := by
  have H := nearby_marked_rate_bounds a.1 p.2.2 hε hε1 hD hv hp hm hbp hbm
  have hc := clockSurvival_le_one C hs.1.le
  have hδ : 0 ≤ 4*Real.pi*(2*D+8*ε) := by
    have : 0 ≤ D := (norm_nonneg _).trans hv
    positivity
  have hr : ENNReal.ofReal (markedRate a.1 p.2.2.1 beamAxis (-beamAxis) 1 1) ≤
      ENNReal.ofReal (markedRate a.1 q.2.2
        (b.plusPartner (mediumPoint endTime q a.2.1))
        (b.minusPartner (mediumPoint endTime q a.2.1))
        (b.plusDensity (mediumPoint endTime q a.2.1))
        (b.minusDensity (mediumPoint endTime q a.2.1)))+
      ENNReal.ofReal (4*Real.pi*(2*D+8*ε)) := by
    rw [← ENNReal.ofReal_add H.1.1 hδ]
    apply ENNReal.ofReal_le_ofReal
    have hdiff := H.2.2
    rw [abs_sub_comm] at hdiff
    linarith [le_abs_self (markedRate a.1 p.2.2.1 beamAxis (-beamAxis) 1 1-
      markedRate a.1 q.2.2 (b.plusPartner (mediumPoint endTime q a.2.1))
        (b.minusPartner (mediumPoint endTime q a.2.1))
        (b.plusDensity (mediumPoint endTime q a.2.1))
        (b.minusDensity (mediumPoint endTime q a.2.1)))]
  have hR := (rate_add_holding_le hC H.2.1.2 a.1).trans (ENNReal.ofReal_le_ofReal hCmax)
  have hM := (rate_add_holding_le hC H.1.2 a.1).trans (ENNReal.ofReal_le_ofReal hCmax)
  simp only [dampedParameterDensity,dampedReferenceWeight,waitingDensity,
    markedReferenceWeight,dampedMediumParameterDensity,ht,indicator_of_mem hs,
    indicator_of_mem ha,Pi.one_apply,one_mul,mul_one]
  refine ⟨(mul_le_of_le_one_left' hc).trans hR,(mul_le_of_le_one_left' hc).trans hM,?_⟩
  calc
    _ ≤ clockSurvival C a.2.1*((_+ENNReal.ofReal (4*Real.pi*(2*D+8*ε)))+holdingWeight C a.1) :=
      mul_le_mul' le_rfl (add_le_add hr le_rfl)
    _ = clockSurvival C a.2.1*((_+holdingWeight C a.1)+ENNReal.ofReal (4*Real.pi*(2*D+8*ε))) := by
      congr 1
      ac_rfl
    _ = _ := mul_add _ _ _
    _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_left' hc)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive damped fixed points on arbitrary finite time intervals -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.PositiveIntegral
variable {P : Type*} [MeasurableSpace P]

theorem exists_damped_fixed_point {T L R K : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hR : 0 ≤ R) (hK : 0 ≤ K) (hsmall : K < L)
    {flow : ℝ → P → P} (hflow : Measurable (fun z : ℝ × P => flow z.1 z.2))
    {f₀ : P → ℝ} (hf₀m : Measurable f₀) (hf₀ : ∀ p, 0 ≤ f₀ p ∧ f₀ p ≤ R)
    (source : BoundedMeasurable.PositiveBall (Domain P) R → Domain P → ℝ)
    (hsm : ∀ f, Measurable (source f))
    (hsb : ∀ f z, 0 ≤ source f z ∧ source f z ≤ L*R)
    (hsl : ∀ f g z, |source f z-source g z| ≤ K*dist f g) :
    ∃ f : BoundedMeasurable.PositiveBall (Domain P) R,
      ∀ z, f.val z = value T L flow f₀ (source f) z := by
  let step : BoundedMeasurable.PositiveBall (Domain P) R →
      BoundedMeasurable.PositiveBall (Domain P) R := fun f =>
    ⟨BoundedMeasurable.ofBounded (Domain P) (value T L flow f₀ (source f))
      (measurable_value hT hflow hf₀m (hsm f)) R
      (fun z => by
        rw [abs_of_nonneg (value_damped_bound hT hL hR hflow hf₀ (hsm f) (hsb f) z).1]
        exact (value_damped_bound hT hL hR hflow hf₀ (hsm f) (hsb f) z).2),
      fun z => value_damped_bound hT hL hR hflow hf₀ (hsm f) (hsb f) z⟩
  have hc : ContractingWith ⟨K/L,div_nonneg hK hL.le⟩ step := by
    constructor
    · exact (div_lt_one hL).mpr hsmall
    · apply LipschitzWith.of_dist_le_mul
      intro f g
      change dist (step f).val (step g).val ≤ (K/L)*dist f g
      apply BoundedMeasurable.dist_le (Domain P) (by positivity)
      intro z
      have h := value_damped_difference hT hL (mul_nonneg hK dist_nonneg) hflow f₀
        (hsm f) (hsm g)
        (fun z => (abs_of_nonneg (hsb f z).1).trans_le (hsb f z).2)
        (fun z => (abs_of_nonneg (hsb g z).1).trans_le (hsb g z).2) (hsl f g) z
      change |value T L flow f₀ (source f) z-value T L flow f₀ (source g) z| ≤ _
      exact h.trans_eq (by ring)
  let zero : BoundedMeasurable.PositiveBall (Domain P) R :=
    ⟨BoundedMeasurable.ofBounded (Domain P) (fun _ => 0) measurable_const 0
      (fun _ => by simp),fun _ => ⟨le_rfl,hR⟩⟩
  let : Nonempty (BoundedMeasurable.PositiveBall (Domain P) R) := ⟨zero⟩
  refine ⟨hc.fixedPoint,?_⟩
  intro z
  have he := congrArg (fun f : BoundedMeasurable.PositiveBall (Domain P) R => f.val z)
    hc.fixedPoint_isFixedPt
  exact he.symm

end BoltzmannNonuniqueness.PositiveIntegral

end

end

section

/-! # Finite positive weights at a common enlarged damping rate -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedWordDensity (C : ℝ≥0) : (n : ℕ) → TimeFlightState → ParameterWord n → ℝ≥0∞
  | 0,_,_ => 1
  | n+1,p,a => dampedParameterDensity C p a.1 *
      dampedWordDensity C n (markedParameterState p a.1) a.2

def dampedMediumWordDensity (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → ℝ≥0∞
  | 0,_,_ => 1
  | n+1,p,a => dampedMediumParameterDensity C b endTime p a.1 *
      dampedMediumWordDensity C b endTime n (mediumParameterState b endTime p a.1) a.2

def DampedWordCoefficientClose (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (M η : ℝ≥0∞) :
    (n : ℕ) → TimeFlightState → PhysicalFlightState → ParameterWord n → Prop
  | 0,_,_,_ => True
  | n+1,p,q,a =>
      dampedParameterDensity C p a.1 ≤ M ∧ dampedMediumParameterDensity C b endTime q a.1 ≤ M ∧
      dampedParameterDensity C p a.1 ≤ dampedMediumParameterDensity C b endTime q a.1+η ∧
      DampedWordCoefficientClose C b endTime M η n (markedParameterState p a.1)
        (mediumParameterState b endTime q a.1) a.2

theorem damped_word_weight_comparison (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (M η : ℝ≥0∞)
    (n : ℕ) (p : TimeFlightState) (q : PhysicalFlightState) (a : ParameterWord n)
    (h : DampedWordCoefficientClose C b endTime M η n p q a) :
    dampedWordDensity C n p a ≤ M^n ∧ dampedMediumWordDensity C b endTime n q a ≤ M^n ∧
    dampedWordDensity C n p a ≤ dampedMediumWordDensity C b endTime n q a+wordWeightError M n*η := by
  induction n generalizing p q with
  | zero => simp [dampedWordDensity,dampedMediumWordDensity,wordWeightError]
  | succ n ih =>
    obtain ⟨hR,hA,hRA⟩ := ih _ _ a.2 h.2.2.2
    refine ⟨?_,?_,?_⟩
    · exact (mul_le_mul' h.1 hR).trans_eq (pow_succ' M n).symm
    · exact (mul_le_mul' h.2.1 hA).trans_eq (pow_succ' M n).symm
    · change dampedParameterDensity C p a.1 *
          dampedWordDensity C n (markedParameterState p a.1) a.2 ≤
        dampedMediumParameterDensity C b endTime q a.1 *
          dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+_
      calc
        _ ≤ dampedParameterDensity C p a.1 *
            (dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              wordWeightError M n*η) := mul_le_mul' le_rfl hRA
        _ = dampedParameterDensity C p a.1 *
              dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              dampedParameterDensity C p a.1*(wordWeightError M n*η) := mul_add _ _ _
        _ ≤ (dampedMediumParameterDensity C b endTime q a.1+η)*
              dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              M*(wordWeightError M n*η) :=
          add_le_add (mul_le_mul' h.2.2.1 le_rfl) (mul_le_mul' h.1 le_rfl)
        _ = dampedMediumParameterDensity C b endTime q a.1 *
              dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              η*dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              M*(wordWeightError M n*η) := by rw [add_mul]
        _ ≤ dampedMediumParameterDensity C b endTime q a.1 *
              dampedMediumWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2+
              η*M^n+M*(wordWeightError M n*η) :=
          add_le_add (add_le_add le_rfl (mul_le_mul' le_rfl hA)) le_rfl
        _ = _ := by simp only [wordWeightError]; ring

theorem damped_word_coefficients_close {C Cmax : ℝ≥0} (hC : referenceClock ≤ C) (hCmax : C ≤ Cmax) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {δ ε D : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hD : D ≤ 1)
    (hbudget : δ+(n:ℝ)*ε ≤ D) (ht : q.1 = p.1) (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n q a) :
    DampedWordCoefficientClose C b endTime (ENNReal.ofReal (Cmax:ℝ))
      (ENNReal.ofReal (4*Real.pi*(2*D+8*ε))) n p q a := by
  induction n generalizing p q δ with
  | zero => trivial
  | succ n ih =>
    have hvD : ‖q.2.2-p.2.2.1‖ ≤ D := hv.trans (by nlinarith)
    have H := nearby_damped_parameter_bounds hC hCmax b endTime hε hε1 hD ht hvD
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

/-! # The physical two-beam collision law with the additional holding mark -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedMediumCollision (C : ℝ≥0) (b : BeamCoefficients) : Kernel MediumState V :=
  mediumCollisionKernel b+(Kernel.deterministic Prod.snd measurable_snd).withDensity
    (fun _ _ => ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)))

instance dampedMediumCollision_sFinite (C : ℝ≥0) (b : BeamCoefficients) :
    IsSFiniteKernel (dampedMediumCollision C b) := by
  have : IsSFiniteKernel ((show Kernel MediumState V from Kernel.deterministic (fun z : MediumState => z.2) measurable_snd).withDensity
      (fun _ _ => ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)))) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro z v
    exact ENNReal.ofReal_ne_top
  unfold dampedMediumCollision
  infer_instance

theorem dampedMediumCollision_apply (C : ℝ≥0) (b : BeamCoefficients) (z : MediumState) :
    dampedMediumCollision C b z = mediumCollisionKernel b z+
      ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) • Measure.dirac z.2 := by
  rw [dampedMediumCollision,add_apply,Kernel.withDensity_apply _ (by fun_prop),
    withDensity_const,Kernel.deterministic_apply]

theorem dampedMediumCollision_lintegral (C : ℝ≥0) (b : BeamCoefficients) (z : MediumState)
    {F : V → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ v, F v ∂dampedMediumCollision C b z) =
      ∑ m : HistoryMark, (mediumMarkedRate b m z+holdingWeight C m) *
        ∫⁻ n : Sphere, F (markedChild m z.2 (b.plusPartner z.1) (b.minusPartner z.1) n.1)
          ∂sphereProbability := by
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib,← mediumCollisionKernel_lintegral b z hF,
    dampedMediumCollision_apply,lintegral_add_measure,lintegral_smul_measure,
    lintegral_dirac,smul_eq_mul]
  congr 1
  rw [Fin.sum_univ_three]
  simp [holdingWeight,markedChild]

theorem dampedMediumCollision_projection {C : ℝ≥0} (hC : referenceClock ≤ C)
    (b : BeamCoefficients) (z : MediumState)
    (hf : mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
      (b.plusDensity z.1) (b.minusDensity z.1) ≤ (referenceClock:ℝ)) :
    dampedMediumCollision C b z =
      ENNReal.ofReal (4*Real.pi*b.plusDensity z.1*‖z.2-b.plusPartner z.1‖) •
        outgoing (z.2,b.plusPartner z.1)+
      ENNReal.ofReal (4*Real.pi*b.minusDensity z.1*‖z.2-b.minusPartner z.1‖) •
        outgoing (z.2,b.minusPartner z.1)+
      ENNReal.ofReal ((C:ℝ)-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1)) • Measure.dirac z.2 := by
  have hf' : 0 ≤ 48*Real.pi-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
      (b.plusDensity z.1) (b.minusDensity z.1) := sub_nonneg.mpr hf
  have hδ : 0 ≤ (C:ℝ)-(referenceClock:ℝ) := sub_nonneg.mpr hC
  have he : ENNReal.ofReal (48*Real.pi-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1))+
      ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) =
      ENNReal.ofReal ((C:ℝ)-mediumFrequency z.2 (b.plusPartner z.1) (b.minusPartner z.1)
        (b.plusDensity z.1) (b.minusDensity z.1)) := by
    rw [← ENNReal.ofReal_add hf' hδ]
    congr 1
    change 48*Real.pi-_+((C:ℝ)-48*Real.pi) = (C:ℝ)-_
    ring
  rw [dampedMediumCollision_apply,mediumCollisionKernel_projection,add_assoc,← add_smul,he]

def dampedMediumStateCollision (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.id ×ₖ (dampedMediumCollision C b).comap
    (fun p => ((endTime-p.1,p.2.1),p.2.2)) (by fun_prop)).map
      (fun q => (q.1.1,(q.1.2.1,q.2)))

instance dampedMediumStateCollision_sFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    IsSFiniteKernel (dampedMediumStateCollision C b endTime) := by
  unfold dampedMediumStateCollision
  infer_instance

theorem dampedMediumStateCollision_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedMediumStateCollision C b endTime p) =
      ∫⁻ v, F (p.1,(p.2.1,v)) ∂dampedMediumCollision C b ((endTime-p.1,p.2.1),p.2.2) := by
  have hm : Measurable (fun q : PhysicalFlightState × V => (q.1.1,(q.1.2.1,q.2))) := by fun_prop
  rw [dampedMediumStateCollision,Kernel.lintegral_map _ hm p hF]
  have hc : Measurable (fun q : PhysicalFlightState × V => F (q.1.1,(q.1.2.1,q.2))) := hF.comp hm
  exact Kernel.lintegral_id_prod hc _ p

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact angular formula for the reference kernel with additional holding -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedReferenceWeight_measurable (C : ℝ≥0) (m : HistoryMark) :
    Measurable (fun p : RetainedState × Sphere => dampedReferenceWeight C p.1 m p.2) :=
  (markedReferenceWeight_measurable m).add measurable_const

theorem dampedReference_integral (C : ℝ≥0) (v : RetainedState) {F : RetainedState → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ u, F u ∂branchingAt C v) =
      ∑ m : HistoryMark, ∫⁻ n, dampedReferenceWeight C v m n*F (markedReferenceState v m n)
        ∂sphereProbability := by
  have he (m : HistoryMark) :
      (∫⁻ n, dampedReferenceWeight C v m n*F (markedReferenceState v m n) ∂sphereProbability) =
      (∫⁻ n, markedReferenceWeight v m n*F (markedReferenceState v m n) ∂sphereProbability)+
      ∫⁻ n, holdingWeight C m*F (markedReferenceState v m n) ∂sphereProbability := by
    simp only [dampedReferenceWeight,add_mul]
    have hmap : Measurable (fun n : Sphere => (v,n)) := measurable_const.prodMk measurable_id
    have hw : Measurable (fun n : Sphere => markedReferenceWeight v m n) :=
      by simpa only [Function.comp_def] using (markedReferenceWeight_measurable m).comp hmap
    have hs : Measurable (fun n : Sphere => markedReferenceState v m n) :=
      by simpa only [Function.comp_def] using (markedReferenceState_measurable m).comp hmap
    exact lintegral_add_left (hw.mul (hF.comp hs)) _
  simp_rw [he]
  rw [Finset.sum_add_distrib,← markedReference_integral v hF,branchingAt_apply,
    lintegral_add_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]
  congr 1
  rw [Fin.sum_univ_three]
  simp [holdingWeight,markedReferenceState,markedChild,stateProjection_apply]

theorem damped_eventHistory_marked_succ (C : ℝ≥0) {D : TimeFlightState → ℝ≥0∞}
    (hD : Measurable D) (n : ℕ) (p : TimeFlightState) :
    eventHistory C (branchingAt C) D (n+1) p =
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
        ∑ m : HistoryMark, ∫⁻ θ, dampedReferenceWeight C p.2.2 m θ *
          eventHistory C (branchingAt C) D n
            (advanceState p s (markedReferenceState p.2.2 m θ)) ∂sphereProbability := by
  have he : (eventStep C (branchingAt C))^(n+1) =
      ((eventStep C (branchingAt C))^n) ∘ₖ eventStep C (branchingAt C) := by
    simpa only [pow_one] using Kernel.pow_add (eventStep C (branchingAt C)) n 1
  rw [eventHistory,he,Kernel.lintegral_comp _ _ _ hD]
  change (∫⁻ q, eventHistory C (branchingAt C) D n q ∂eventStep C (branchingAt C) p) = _
  rw [eventStep_lintegral _ _ _ (eventHistory_measurable _ _ hD n)]
  apply lintegral_congr
  intro s
  have hm : Measurable (fun u : RetainedState => eventHistory C (branchingAt C) D n (advanceState p s u)) :=
    (eventHistory_measurable _ _ hD n).comp (by unfold advanceState; fun_prop)
  rw [dampedReference_integral C p.2.2 hm]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Fixed mark, time and angle integrals at the larger damping rate -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedReferenceParameterDensity (C : ℝ≥0) (p : TimeFlightState)
    (m : HistoryMark) (a : EventParameter) : ℝ≥0∞ := dampedParameterDensity C p (m,a)

theorem dampedReferenceParameterDensity_measurable (C : ℝ≥0) (m : HistoryMark) :
    Measurable (fun q : TimeFlightState × EventParameter => dampedReferenceParameterDensity C q.1 m q.2) :=
  (dampedParameterDensity_measurable C).comp
    (show Measurable (fun q : TimeFlightState × EventParameter => (q.1,(m,q.2))) by fun_prop)

theorem damped_reference_parameter_integral (C : ℝ≥0) {F : TimeFlightState → ℝ≥0∞} (hF : Measurable F)
    (p : TimeFlightState) (m : HistoryMark) {T : ℝ} (hT : p.1 ≤ T) :
    (∫⁻ a, dampedReferenceParameterDensity C p m a*F (referenceParameterState p m a) ∂eventParameterMeasure T) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
        ∫⁻ θ, dampedReferenceWeight C p.2.2 m θ *
          F (advanceState p s (markedReferenceState p.2.2 m θ)) ∂sphereProbability := by
  have hm : Measurable (fun a : EventParameter => dampedReferenceParameterDensity C p m a*
      F (referenceParameterState p m a)) :=
    ((dampedReferenceParameterDensity_measurable C m).comp (measurable_const.prodMk measurable_id)).mul
      (hF.comp ((referenceParameterState_measurable m).comp (measurable_const.prodMk measurable_id)))
  rw [eventParameterMeasure,lintegral_prod _ hm.aemeasurable]
  have he (s : ℝ) : (∫⁻ θ, dampedReferenceParameterDensity C p m (s,θ)*
      F (referenceParameterState p m (s,θ)) ∂sphereProbability) =
      (Ioc 0 p.1).indicator (fun r => clockSurvival C r*
        ∫⁻ θ, dampedReferenceWeight C p.2.2 m θ*
          F (advanceState p r (markedReferenceState p.2.2 m θ)) ∂sphereProbability) s := by
    by_cases hs : s ∈ Ioc 0 p.1
    · simp only [dampedReferenceParameterDensity,dampedParameterDensity,referenceParameterState,waitingDensity,
        indicator_of_mem hs,Pi.one_apply,one_mul,mul_assoc]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    · simp only [dampedReferenceParameterDensity,dampedParameterDensity,waitingDensity,indicator_of_notMem hs,zero_mul,lintegral_zero]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioc,Measure.restrict_restrict_of_subset]
  exact Ioc_subset_Ioc_right hT

theorem damped_eventHistory_parameter_succ (C : ℝ≥0) {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (n : ℕ) (p : TimeFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    eventHistory C (branchingAt C) D (n+1) p =
      ∑ m : HistoryMark, ∫⁻ a, dampedReferenceParameterDensity C p m a *
        eventHistory C (branchingAt C) D n (referenceParameterState p m a)
          ∂eventParameterMeasure T := by
  rw [damped_eventHistory_marked_succ C hD]
  have h (m : HistoryMark) := damped_reference_parameter_integral C
    (eventHistory_measurable C (branchingAt C) hD n) p m hT
  simp_rw [h]
  simp_rw [Finset.mul_sum]
  apply lintegral_finsetSum
  intro m _
  have hm : Measurable (fun a : EventParameter => dampedReferenceWeight C p.2.2 m a.2 *
      eventHistory C (branchingAt C) D n
        (advanceState p a.1 (markedReferenceState p.2.2 m a.2))) := by
    exact ((dampedReferenceWeight_measurable C m).comp (measurable_const.prodMk measurable_snd)).mul
      ((eventHistory_measurable C (branchingAt C) hD n).comp
        ((referenceParameterState_measurable m).comp (measurable_const.prodMk measurable_id)))
  exact (show Measurable (clockSurvival C) by unfold clockSurvival; fun_prop).mul
    hm.lintegral_prod_right'

theorem damped_eventHistory_marked_parameter_succ (C : ℝ≥0) {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (n : ℕ) (p : TimeFlightState) {T : ℝ} (hT : p.1 ≤ T) :
    eventHistory C (branchingAt C) D (n+1) p =
      ∫⁻ a, dampedParameterDensity C p a *
        eventHistory C (branchingAt C) D n (markedParameterState p a)
          ∂markedEventMeasure T := by
  have hm : Measurable (fun a : MarkedEventParameter => dampedParameterDensity C p a*
      eventHistory C (branchingAt C) D n (markedParameterState p a)) :=
    (((dampedParameterDensity_measurable C).comp (measurable_const.prodMk measurable_id)).mul
      ((eventHistory_measurable C (branchingAt C) hD n).comp
        (markedParameterState_measurable.comp (measurable_const.prodMk measurable_id))))
  rw [markedEventMeasure,lintegral_prod _ hm.aemeasurable,lintegral_fintype]
  simp only [Measure.count_singleton,mul_one]
  exact damped_eventHistory_parameter_succ C hD n p hT

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exact finite reference histories at the enlarged damping rate -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem holdingWeight_ne_top (C : ℝ≥0) (m : HistoryMark) : holdingWeight C m ≠ ⊤ := by
  unfold holdingWeight
  split
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

theorem dampedParameterDensity_ne_top (C : ℝ≥0) (p : TimeFlightState) (a : MarkedEventParameter) :
    dampedParameterDensity C p a ≠ ⊤ := by
  have hw : waitingDensity p a.2.1 ≠ ⊤ := by
    by_cases hs : a.2.1 ∈ Ioc 0 p.1 <;> simp [waitingDensity,hs]
  have hr : markedReferenceWeight p.2.2 a.1 a.2.2 ≠ ⊤ := by
    by_cases ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∈ referenceRegion
    · simp [markedReferenceWeight,ha]
    · simp [markedReferenceWeight,ha]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hw ENNReal.ofReal_ne_top)
    (ENNReal.add_ne_top.mpr ⟨hr,holdingWeight_ne_top C a.1⟩)

theorem dampedParameterDensity_zero (C : ℝ≥0) (p : TimeFlightState) (a : MarkedEventParameter)
    (ha : a.2.1 ∉ Ioc 0 p.1) : dampedParameterDensity C p a = 0 := by
  simp [dampedParameterDensity,waitingDensity,ha]

theorem dampedWordDensity_measurable (C : ℝ≥0) (n : ℕ) :
    Measurable (fun q : TimeFlightState × ParameterWord n => dampedWordDensity C n q.1 q.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hh : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by fun_prop
    have ht : Measurable (fun q : TimeFlightState × ParameterWord (n+1) => q.2.2) := by fun_prop
    have hs : Measurable (fun q : TimeFlightState × ParameterWord (n+1) =>
        (markedParameterState q.1 q.2.1,q.2.2)) :=
      (markedParameterState_measurable.comp hh).prodMk ht
    exact ((dampedParameterDensity_measurable C).comp hh).mul (ih.comp hs)

theorem dampedWord_integral (C : ℝ≥0) {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D)
    (T : ℝ) (n : ℕ) (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) :
    (∫⁻ a, dampedWordDensity C n p a * D (parameterWordState n p a)
      ∂parameterWordMeasure T n) = eventHistory C (branchingAt C) D n p := by
  induction n generalizing p with
  | zero =>
    rw [eventHistory_zero]
    change (∫⁻ _a : PUnit, 1*D p ∂Measure.dirac PUnit.unit) = D p
    rw [lintegral_const,Measure.dirac_apply_of_mem (mem_univ _),mul_one,one_mul]
  | succ n ih =>
    have hmap : Measurable (fun a : ParameterWord (n+1) => (p,a)) :=
      measurable_const.prodMk measurable_id
    have hd : Measurable (fun a : ParameterWord (n+1) => dampedWordDensity C (n+1) p a) := by
      simpa only [Function.comp_def] using (dampedWordDensity_measurable C (n+1)).comp hmap
    have hs : Measurable (fun a : ParameterWord (n+1) => parameterWordState (n+1) p a) := by
      simpa only [Function.comp_def] using (parameterWordState_measurable (n+1)).comp hmap
    have hm : Measurable (fun a : ParameterWord (n+1) =>
        dampedWordDensity C (n+1) p a * D (parameterWordState (n+1) p a)) := hd.mul (hD.comp hs)
    rw [parameterWordMeasure,lintegral_prod _ hm.aemeasurable,
      damped_eventHistory_marked_parameter_succ C hD n p hp.2]
    apply lintegral_congr
    intro a
    change (∫⁻ w, (dampedParameterDensity C p a *
      dampedWordDensity C n (markedParameterState p a) w) *
        D (parameterWordState n (markedParameterState p a) w) ∂parameterWordMeasure T n) = _
    simp_rw [mul_assoc]
    rw [lintegral_const_mul' _ _ (dampedParameterDensity_ne_top C p a)]
    by_cases ha : a.2.1 ∈ Ioc 0 p.1
    · have ht := markedParameterState_time p a ha
      rw [ih (markedParameterState p a) ⟨ht.1,ht.2.trans hp.2⟩]
    · rw [dampedParameterDensity_zero C p a ha,zero_mul,zero_mul]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Enlarged damping preserves the geometric support of reference words -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedParameterDensity_zero_of_outside (C : ℝ≥0) (p : TimeFlightState)
    (a : MarkedEventParameter)
    (ha : markedChild a.1 p.2.2.1 beamAxis (-beamAxis) a.2.2.1 ∉ referenceRegion) :
    dampedParameterDensity C p a = 0 := by
  by_cases hm : a.1 = 0
  · exact False.elim (ha (by simpa only [markedChild,hm,ite_eq_left] using p.2.2.2))
  · simp [dampedParameterDensity,dampedReferenceWeight,markedReferenceWeight,holdingWeight,ha,hm]

theorem goodReferenceWord_of_damped_density_ne_zero (C : ℝ≥0) (n : ℕ)
    (p : TimeFlightState) (a : ParameterWord n) (h : dampedWordDensity C n p a ≠ 0) :
    GoodReferenceWord n p a := by
  induction n generalizing p with
  | zero => trivial
  | succ n ih =>
    have hh := mul_ne_zero_iff.mp h
    refine ⟨?_,?_,ih _ a.2 hh.2⟩
    · by_contra ht
      exact hh.1 (dampedParameterDensity_zero C p a.1 ht)
    · by_contra hc
      exact hh.1 (dampedParameterDensity_zero_of_outside C p a.1 hc)

theorem dampedMediumWordDensity_measurable (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (n : ℕ) :
    Measurable (fun q : PhysicalFlightState × ParameterWord n =>
      dampedMediumWordDensity C b endTime n q.1 q.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hh : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by fun_prop
    have ht : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => q.2.2) := by fun_prop
    have hs : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) =>
        (mediumParameterState b endTime q.1 q.2.1,q.2.2)) :=
      ((mediumParameterState_measurable b endTime).comp hh).prodMk ht
    exact ((dampedMediumParameterDensity_measurable C b endTime).comp hh).mul (ih.comp hs)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Lower transfer at the same enlarged reference and physical damping -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedMediumBlockIntegrand (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (p : TimeFlightState)
    (κ d : ℝ) (n : ℕ) (a : ParameterWord n) : ℝ≥0∞ :=
  let q := mediumWordState b endTime n (embedFlightState p) a
  dampedMediumWordDensity C b endTime n (embedFlightState p) a *
    (clockSurvival C q.1 *
      (physicalBlockTarget p.2.1 p.1 κ d).indicator 1 (finishMediumFlight q))

def dampedHistoryPerturbationError (Cmax : ℝ≥0) (n : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  wordWeightError (ENNReal.ofReal (Cmax:ℝ)) n *
    ENNReal.ofReal (4*Real.pi*((2*(n:ℝ)+8)*ε))

theorem damped_medium_word_integrand_bound {C Cmax : ℝ≥0} (hC : referenceClock ≤ C)
    (hCmax : C ≤ Cmax) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (a : ParameterWord n) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hv : (n:ℝ)*ε ≤ 1)
    (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    dampedWordDensity C n p a * flightSeed C
        ((blockTarget p.2.1 p.1 κ d).indicator 1) (parameterWordState n p a) ≤
      dampedMediumBlockIntegrand C b endTime p κ d n a+dampedHistoryPerturbationError Cmax n ε := by
  by_cases hr : dampedWordDensity C n p a = 0
  · rw [hr,zero_mul]
    exact bot_le
  have ha := goodReferenceWord_of_damped_density_ne_zero C n p a hr
  have hb := hnear ha
  by_cases hmem : finishFlight (parameterWordState n p a) ∈ blockTarget p.2.1 p.1 κ d
  · have hm := medium_word_target b endTime n p a hε hp hv hx ha hb hmem
    have ht := (medium_word_geometry b endTime n a (X := 0) (δ := 0) hε hp rfl
      (by simp [embedFlightState]) (by simp [embedFlightState]) ha hb).1
    have H := damped_word_coefficients_close hC hCmax b endTime n a (δ := 0) (D := (n:ℝ)*ε)
      hε hε1 hv (by simp) rfl (by simp [embedFlightState]) ha hb
    have hweight := (damped_word_weight_comparison C b endTime _ _ n p (embedFlightState p) a H).2.2
    have he : ENNReal.ofReal (4*Real.pi*(2*((n:ℝ)*ε)+8*ε)) =
        ENNReal.ofReal (4*Real.pi*((2*(n:ℝ)+8)*ε)) := by congr 1; ring
    rw [he] at hweight
    have hc := clockSurvival_le_one C (parameterWordState_time n p a hp ha).1
    simp only [flightSeed,dampedMediumBlockIntegrand,indicator_of_mem hmem,indicator_of_mem hm,
      Pi.one_apply,mul_one,ht]
    calc
      _ ≤ (dampedMediumWordDensity C b endTime n (embedFlightState p) a+
          dampedHistoryPerturbationError Cmax n ε)*clockSurvival C (parameterWordState n p a).1 :=
        mul_le_mul' hweight le_rfl
      _ = _ := add_mul _ _ _
      _ ≤ _ := add_le_add le_rfl (mul_le_of_le_one_right' hc)
  · simp only [flightSeed,indicator_of_notMem hmem,mul_zero]
    exact bot_le

theorem damped_medium_word_integral_lower {C Cmax : ℝ≥0} (hC : referenceClock ≤ C)
    (hCmax : C ≤ Cmax) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) (p : TimeFlightState) (T : ℝ) {ε κ d : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/4) (hp : 0 ≤ p.1) (hpT : p.1 ≤ T)
    (hv : (n:ℝ)*ε ≤ 1) (hx : 2*p.1*((n:ℝ)*ε) ≤ d*κ*p.1/4)
    (hnear : ∀ a, GoodReferenceWord n p a → WordNearby b endTime ε n (embedFlightState p) a) :
    eventHistory C (branchingAt C)
        (flightSeed C ((blockTarget p.2.1 p.1 κ d).indicator 1)) n p ≤
      (∫⁻ a, dampedMediumBlockIntegrand C b endTime p κ d n a ∂parameterWordMeasure T n)+
        dampedHistoryPerturbationError Cmax n ε*(3*ENNReal.ofReal T)^n := by
  have hf : Measurable ((blockTarget p.2.1 p.1 κ d).indicator (1 : FlightState → ℝ≥0∞)) :=
    measurable_const.indicator (blockTarget_measurable _ _ _ _)
  rw [← dampedWord_integral C (flightSeed_measurable C hf) T n p ⟨hp,hpT⟩]
  calc
    _ ≤ ∫⁻ a, dampedMediumBlockIntegrand C b endTime p κ d n a+dampedHistoryPerturbationError Cmax n ε
        ∂parameterWordMeasure T n :=
      lintegral_mono (fun a => damped_medium_word_integrand_bound hC hCmax b endTime n p a hε hε1 hp hv hx (hnear a))
    _ = _ := by rw [lintegral_add_right _ measurable_const,lintegral_const,parameterWordMeasure_mass]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The damped one-event kernel for finite marked histories in a measurable medium -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedMediumParameterDensity_ne_top (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (a : MarkedEventParameter) :
    dampedMediumParameterDensity C b endTime p a ≠ ⊤ := by
  unfold dampedMediumParameterDensity
  by_cases ht : a.2.1 ∈ Ioc 0 p.1
  · rw [indicator_of_mem ht,Pi.one_apply,one_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,holdingWeight_ne_top C a.1⟩)
  · simp [ht]

def dampedMediumEventDensity (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (_ : PhysicalFlightState) (p : PhysicalFlightState × MarkedEventParameter) : ℝ≥0∞ :=
  dampedMediumParameterDensity C b endTime p.1 p.2

theorem dampedMediumEventDensity_measurable (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    Measurable (Function.uncurry (dampedMediumEventDensity C b endTime)) :=
  (dampedMediumParameterDensity_measurable C b endTime).comp measurable_snd

def dampedMediumEventKernel (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) :
    Kernel PhysicalFlightState PhysicalFlightState :=
  (Kernel.withDensity (Kernel.id ×ₖ Kernel.const PhysicalFlightState (markedEventMeasure T))
    (dampedMediumEventDensity C b endTime)).map (fun p => mediumParameterState b endTime p.1 p.2)

instance dampedMediumEventKernel_isSFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) :
    IsSFiniteKernel (dampedMediumEventKernel C b endTime T) := by
  have hd : IsSFiniteKernel (Kernel.withDensity
      (Kernel.id ×ₖ Kernel.const PhysicalFlightState (markedEventMeasure T))
      (dampedMediumEventDensity C b endTime)) := by
    apply Kernel.IsSFiniteKernel.withDensity
    intro p a
    exact dampedMediumParameterDensity_ne_top C b endTime a.1 a.2
  unfold dampedMediumEventKernel
  infer_instance

theorem dampedMediumEventKernel_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ)
    (p : PhysicalFlightState) {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedMediumEventKernel C b endTime T p) =
      ∫⁻ a, dampedMediumParameterDensity C b endTime p a * F (mediumParameterState b endTime p a)
        ∂markedEventMeasure T := by
  have hcomp : Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      F (mediumParameterState b endTime q.1 q.2)) := by
    simpa only [Function.comp_def] using hF.comp (mediumParameterState_measurable b endTime)
  have hm : Measurable (fun q : PhysicalFlightState × MarkedEventParameter =>
      dampedMediumParameterDensity C b endTime q.1 q.2 * F (mediumParameterState b endTime q.1 q.2)) :=
    (dampedMediumParameterDensity_measurable C b endTime).mul hcomp
  rw [dampedMediumEventKernel,Kernel.lintegral_map _ (mediumParameterState_measurable b endTime) p hF,
    Kernel.lintegral_withDensity _ (dampedMediumEventDensity_measurable C b endTime) p hcomp]
  simpa only [dampedMediumEventDensity,Function.comp_def,Kernel.const_apply] using!
    Kernel.lintegral_id_prod hm (Kernel.const PhysicalFlightState (markedEventMeasure T)) p

instance dampedMediumEventKernel_pow_isSFinite (C : ℝ≥0) (b : BeamCoefficients) (endTime T : ℝ) (n : ℕ) :
    IsSFiniteKernel ((dampedMediumEventKernel C b endTime T)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show (dampedMediumEventKernel C b endTime T)^(n+1) =
        ((dampedMediumEventKernel C b endTime T)^n) ∘ₖ dampedMediumEventKernel C b endTime T by
      simpa only [pow_one] using Kernel.pow_add (dampedMediumEventKernel C b endTime T) n 1]
    let _ := ih
    infer_instance

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Physical collision-time formula for the marked medium event kernel -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_medium_parameter_integral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) (m : HistoryMark) {T : ℝ} (hT : p.1 ≤ T)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ a, dampedMediumParameterDensity C b endTime p (m,a) *
      F (mediumParameterState b endTime p (m,a)) ∂eventParameterMeasure T) =
    ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
      ((mediumMarkedRate b m (mediumPoint endTime p s,p.2.2)+holdingWeight C m) *
        ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n)))
          ∂sphereProbability) := by
  have hpair : Measurable (fun a : EventParameter => (p,(m,a))) := by fun_prop
  have hm : Measurable (fun a : EventParameter =>
      dampedMediumParameterDensity C b endTime p (m,a) *
        F (mediumParameterState b endTime p (m,a))) :=
    ((dampedMediumParameterDensity_measurable C b endTime).comp hpair).mul
      (hF.comp ((mediumParameterState_measurable b endTime).comp hpair))
  rw [eventParameterMeasure,lintegral_prod _ hm.aemeasurable]
  have he (s : ℝ) : (∫⁻ n : Sphere, dampedMediumParameterDensity C b endTime p (m,(s,n)) *
      F (mediumParameterState b endTime p (m,(s,n))) ∂sphereProbability) =
      (Ioc 0 p.1).indicator (fun s => clockSurvival C s *
        ((mediumMarkedRate b m (mediumPoint endTime p s,p.2.2)+holdingWeight C m) *
          ∫⁻ n : Sphere, F (mediumParameterState b endTime p (m,(s,n)))
            ∂sphereProbability)) s := by
    by_cases hs : s ∈ Ioc 0 p.1
    · simp only [dampedMediumParameterDensity,indicator_of_mem hs,Pi.one_apply,one_mul,
        mediumMarkedRate,mul_assoc]
      unfold clockSurvival
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,holdingWeight_ne_top C m⟩)]
    · simp [dampedMediumParameterDensity,hs]
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Ioc,Measure.restrict_restrict_of_subset]
  exact Ioc_subset_Ioc_right hT

theorem dampedMediumEventKernel_physical_lintegral (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (p : PhysicalFlightState) {T : ℝ} (hT : p.1 ≤ T)
    {F : PhysicalFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂dampedMediumEventKernel C b endTime T p) =
    ∫⁻ s in Ioc 0 p.1, clockSurvival C s *
      ∫⁻ v, F (p.1-s,((mediumPoint endTime p s).2,v))
        ∂dampedMediumCollision C b (mediumPoint endTime p s,p.2.2) := by
  rw [dampedMediumEventKernel_lintegral C b endTime T p hF]
  have hpair : Measurable (fun a : MarkedEventParameter => (p,a)) := by fun_prop
  have hm : Measurable (fun a : MarkedEventParameter =>
      dampedMediumParameterDensity C b endTime p a * F (mediumParameterState b endTime p a)) :=
    ((dampedMediumParameterDensity_measurable C b endTime).comp hpair).mul
      (hF.comp ((mediumParameterState_measurable b endTime).comp hpair))
  rw [markedEventMeasure,lintegral_prod _ hm.aemeasurable,lintegral_fintype]
  simp only [Measure.count_singleton,mul_one]
  simp_rw [damped_medium_parameter_integral C b endTime p _ hT hF]
  rw [← lintegral_finsetSum]
  · apply lintegral_congr
    intro s
    rw [← Finset.mul_sum,dampedMediumCollision_lintegral C b _
      (F := fun v => F (p.1-s,((mediumPoint endTime p s).2,v)))
      (hF.comp (by fun_prop))]
    rfl
  · intro m _
    have hrate : Measurable (fun s : ℝ =>
        (mediumMarkedRate b m (mediumPoint endTime p s,p.2.2)+holdingWeight C m)) :=
      ((mediumMarkedRate_measurable b m).comp (show Measurable (fun s : ℝ => (mediumPoint endTime p s,p.2.2)) by unfold mediumPoint; fun_prop)).add measurable_const
    have hi : Measurable (fun a : EventParameter =>
        F (mediumParameterState b endTime p (m,a))) :=
      hF.comp ((mediumParameterState_measurable b endTime).comp
        (show Measurable (fun a : EventParameter => (p,(m,a))) by fun_prop))
    exact (show Measurable (clockSurvival C) by
      unfold clockSurvival; fun_prop).mul (hrate.mul hi.lintegral_prod_right')

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite medium words whose collision velocities stay in the physical box -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def dampedBoundedWordDensity (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) :
    (n : ℕ) → PhysicalFlightState → ParameterWord n → ℝ≥0∞
  | 0,_,_ => 1
  | n+1,p,a =>
      let q := mediumParameterState b endTime p a.1
      dampedMediumParameterDensity C b endTime p a.1 *
        ({q : PhysicalFlightState | ‖q.2.2‖ ≤ 6}.indicator 1 q *
          dampedBoundedWordDensity C b endTime n q a.2)

theorem dampedBoundedWordDensity_measurable (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ) (n : ℕ) :
    Measurable (fun q : PhysicalFlightState × ParameterWord n =>
      dampedBoundedWordDensity C b endTime n q.1 q.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hh : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => (q.1,q.2.1)) := by
      fun_prop
    have hs : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) =>
        mediumParameterState b endTime q.1 q.2.1) :=
      (mediumParameterState_measurable b endTime).comp hh
    have ht : Measurable (fun q : PhysicalFlightState × ParameterWord (n+1) => q.2.2) := by
      fun_prop
    have hbox : Measurable ({q : PhysicalFlightState | ‖q.2.2‖ ≤ 6}.indicator
        (1 : PhysicalFlightState → ℝ≥0∞)) :=
      measurable_const.indicator (measurableSet_le (by fun_prop) measurable_const)
    exact ((dampedMediumParameterDensity_measurable C b endTime).comp hh).mul
      ((hbox.comp hs).mul (ih.comp (hs.prodMk ht)))

theorem dampedBoundedWordDensity_eq (C : ℝ≥0) (b : BeamCoefficients) (endTime : ℝ)
    (n : ℕ) {p : TimeFlightState} {q : PhysicalFlightState} (a : ParameterWord n)
    {δ ε : ℝ} (hbudget : δ+(n:ℝ)*ε ≤ 1)
    (hv : ‖q.2.2-p.2.2.1‖ ≤ δ)
    (ha : GoodReferenceWord n p a) (hb : WordNearby b endTime ε n q a) :
    dampedBoundedWordDensity C b endTime n q a = dampedMediumWordDensity C b endTime n q a := by
  induction n generalizing p q δ with
  | zero => rfl
  | succ n ih =>
    have hv' := medium_parameter_velocity_error b endTime ha.2.1 hv hb.1 hb.2.1
    have hbud' : (δ+ε)+(n:ℝ)*ε ≤ 1 := by
      push_cast at hbudget
      linarith
    have hε : 0 ≤ ε := (norm_nonneg _).trans hb.1
    have hδε : δ+ε ≤ 1 := by nlinarith
    have hnorm : ‖(mediumParameterState b endTime q a.1).2.2‖ ≤ 6 := by
      have hh := norm_add_le
        ((mediumParameterState b endTime q a.1).2.2-(markedParameterState p a.1).2.2.1)
        (markedParameterState p a.1).2.2.1
      rw [sub_add_cancel] at hh
      linarith [retainedState_norm (markedParameterState p a.1).2.2]
    change dampedMediumParameterDensity C b endTime q a.1 *
        ({q : PhysicalFlightState | ‖q.2.2‖ ≤ 6}.indicator 1
          (mediumParameterState b endTime q a.1) *
            dampedBoundedWordDensity C b endTime n (mediumParameterState b endTime q a.1) a.2) = _
    have hmem : mediumParameterState b endTime q a.1 ∈
        {q : PhysicalFlightState | ‖q.2.2‖ ≤ 6} := hnorm
    rw [indicator_of_mem hmem,Pi.one_apply,one_mul,
      ih a.2 hbud' hv' ha.2.2 hb.2.2.2.2]
    rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The Fourier multiplier of the exponentially damped characteristic integral -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def dampedCharacter (β s : ℝ) : ℂ :=
  (Real.exp (-s) : ℂ)*Complex.exp (-Complex.I*(β*s))

theorem dampedCharacter_eq (β s : ℝ) :
    dampedCharacter β s = Complex.exp ((-(1+Complex.I*β))*s) := by
  rw [dampedCharacter,Complex.ofReal_exp,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem dampedCharacter_integrable (β : ℝ) : IntegrableOn (dampedCharacter β) (Ioi 0) := by
  rw [show dampedCharacter β = (fun s : ℝ => Complex.exp ((-(1+Complex.I*β))*(s : ℂ))) from
    funext (dampedCharacter_eq β)]
  apply integrableOn_exp_mul_complex_Ioi
  norm_num

theorem integral_dampedCharacter (β : ℝ) :
    (∫ s in Ioi (0 : ℝ), dampedCharacter β s) = (1+Complex.I*β)⁻¹ := by
  simp_rw [dampedCharacter_eq]
  rw [integral_exp_mul_complex_Ioi (by norm_num : (-(1+Complex.I*β)).re < 0)]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero,neg_div_neg_eq,one_div]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Uniform smallness of the finite-history perturbation error -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem dampedHistoryPerturbationError_continuous (Cmax : ℝ≥0) (n : ℕ) : Continuous (dampedHistoryPerturbationError Cmax n) := by
  exact (ENNReal.continuous_const_mul (wordWeightError_ne_top ENNReal.ofReal_ne_top n)).comp
    (ENNReal.continuous_ofReal.comp (by fun_prop))

def dampedFiniteHistoryError (Cmax : ℝ≥0) (N : ℕ) (T ε : ℝ) : ℝ≥0∞ :=
  ∑ n ∈ Finset.range N, dampedHistoryPerturbationError Cmax n ε*(3*ENNReal.ofReal T)^n

theorem dampedFiniteHistoryError_continuous (Cmax : ℝ≥0) (N : ℕ) (T : ℝ) : Continuous (dampedFiniteHistoryError Cmax N T) := by
  apply continuous_finsetSum
  intro n _hn
  exact (ENNReal.continuous_mul_const (ENNReal.pow_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top))).comp
      (dampedHistoryPerturbationError_continuous Cmax n)

theorem dampedFiniteHistoryError_zero (Cmax : ℝ≥0) (N : ℕ) (T : ℝ) : dampedFiniteHistoryError Cmax N T 0 = 0 := by
  simp [dampedFiniteHistoryError,dampedHistoryPerturbationError]

theorem dampedFiniteHistoryError_small (Cmax : ℝ≥0) (N : ℕ) (T : ℝ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε ∈ Icc 0 ε₀, dampedFiniteHistoryError Cmax N T ε < 1 := by
  have hh : ∀ᶠ ε in 𝓝 (0 : ℝ), dampedFiniteHistoryError Cmax N T ε < 1 :=
    (dampedFiniteHistoryError_continuous Cmax N T).continuousAt.eventually
      (gt_mem_nhds (by rw [dampedFiniteHistoryError_zero]; norm_num))
  obtain ⟨r,hr,hsmall⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨r/2,by positivity,fun ε hε => hsmall ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hε.1]
  exact hε.2.trans_lt (half_lt_self hr)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Integrability along the actual damped transport lines in Fourier coordinates -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def lineShear (w : FourierSpace) (p : ℝ × FourierSpace) : ℝ × FourierSpace :=
  (p.1,p.2-p.1 • w)

theorem lineShear_measurePreserving (w : FourierSpace) (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving (lineShear w) (μ.prod (volume : Measure FourierSpace)) (μ.prod volume) := by
  unfold lineShear
  apply (MeasurePreserving.id μ).skew_product (g := fun s x => x-s • w)
    (μc := (volume : Measure FourierSpace)) (μd := (volume : Measure FourierSpace))
  · fun_prop
  · exact ae_of_all _ (fun s => (measurePreserving_add_right volume (-(s • w))).map_eq)

def dampedLineResolvent (f : FourierSpace → ℂ) (w x : FourierSpace) : ℂ :=
  ∫ s in Ioi (0 : ℝ), Real.exp (-s) • f (x-s • w)

theorem dampedLine_integrable {f : FourierSpace → ℂ} (hf : Integrable f) (w : FourierSpace) :
    Integrable (fun p : ℝ × FourierSpace => Real.exp (-p.1) • f (p.2-p.1 • w))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  exact (lineShear_measurePreserving w _).integrable_comp_of_integrable
    ((integrableOn_exp_neg_Ioi 0).smul_prod hf)

theorem dampedLineResolvent_integrable {f : FourierSpace → ℂ}
    (hf : Integrable f) (w : FourierSpace) : Integrable (dampedLineResolvent f w) :=
  (dampedLine_integrable hf w).integral_prod_right

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Passing the Fourier integral through damped transport along a line -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

attribute [local irreducible] dampedLineResolvent

def fourierLineKernel (f : FourierSpace → ℂ) (w k : FourierSpace) (p : ℝ × FourierSpace) : ℂ :=
  𝐞 (-inner ℝ p.2 k) • (Real.exp (-p.1) • f (p.2-p.1 • w))

theorem fourierLineKernel_integrable {f : FourierSpace → ℂ} (hf : Integrable f)
    (w k : FourierSpace) : Integrable (fourierLineKernel f w k)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hb := dampedLine_integrable hf w
  apply hb.norm.mono'
  · have hc : Measurable (fun p : ℝ × FourierSpace => 𝐞 (-inner ℝ p.2 k)) := by
      fun_prop
    exact hc.aestronglyMeasurable.smul hb.aestronglyMeasurable
  · exact ae_of_all _ (fun p => by
      simp only [fourierLineKernel,Circle.norm_smul]
      exact le_rfl)

theorem fourier_dampedLine_integral {f : FourierSpace → ℂ} (hf : Integrable f)
    (w k : FourierSpace) :
    𝓕 (dampedLineResolvent f w) k =
      ∫ s in Ioi (0 : ℝ), Real.exp (-s) • 𝓕 (fun x => f (x-s • w)) k := by
  rw [Real.fourier_eq]
  calc
    _ = ∫ x : FourierSpace, ∫ s in Ioi (0 : ℝ), fourierLineKernel f w k (s,x) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        change 𝐞 (-inner ℝ x k) • dampedLineResolvent f w x = _
        unfold dampedLineResolvent
        change ((𝐞 (-inner ℝ x k) : ℂ) *
          ∫ s in Ioi (0 : ℝ), Real.exp (-s) • f (x-s • w)) = _
        rw [← integral_const_mul]
        rfl)
    _ = ∫ s in Ioi (0 : ℝ), ∫ x : FourierSpace, fourierLineKernel f w k (s,x) :=
      (integral_integral_swap (f := fun s x => fourierLineKernel f w k (s,x))
        (fourierLineKernel_integrable hf w k)).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun s => by
        change (∫ x : FourierSpace, fourierLineKernel f w k (s,x)) =
          Real.exp (-s) • 𝓕 (fun x => f (x-s • w)) k
        rw [Real.fourier_eq,← integral_smul]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by
          exact smul_comm (𝐞 (-inner ℝ x k)) (Real.exp (-s)) (f (x-s • w))))

end BoltzmannNonuniqueness.Published

end

end

end OAI
