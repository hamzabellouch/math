import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceMinorization
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceFlightLaws

namespace OAI

section

/-! # Splitting and translating the first-event time integral -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lintegral_time_split (f : ℝ → ℝ≥0∞) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫⁻ r in Ioc 0 (s+t), f r) =
      (∫⁻ r in Ioc 0 s, f r) + ∫⁻ r in Ioc s (s+t), f r := by
  rw [← Ioc_union_Ioc_eq_Ioc hs (by linarith)]
  apply lintegral_union
  · exact measurableSet_Ioc
  · apply disjoint_left.mpr
    intro r hr hs'
    exact (not_lt_of_ge hr.2) hs'.1

theorem lintegral_time_shift (f : ℝ → ℝ≥0∞) (s t : ℝ) :
    (∫⁻ r in Ioc s (s+t), f r) = ∫⁻ r in Ioc 0 t, f (s+r) := by
  classical
  rw [← lintegral_indicator measurableSet_Ioc,← lintegral_indicator measurableSet_Ioc]
  calc
    _ = ∫⁻ r : ℝ, (Ioc s (s+t)).indicator f (s+r) :=
      (lintegral_add_left_eq_self ((Ioc s (s+t)).indicator f) s).symm
    _ = _ := by
      apply lintegral_congr
      intro r
      have hh : s+r ∈ Ioc s (s+t) ↔ r ∈ Ioc 0 t := by
        constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
      simp only [indicator_apply,hh]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Cutting the first-event formula at an intermediate time -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def clockSurvival (rate : ℝ≥0) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(rate : ℝ)*s))
def clockDensity (rate : ℝ≥0) (s : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((rate : ℝ)*Real.exp (-(rate : ℝ)*s))

theorem clockSurvival_add (rate : ℝ≥0) (s t : ℝ) :
    clockSurvival rate (s+t) = clockSurvival rate s*clockSurvival rate t := by
  rw [clockSurvival,clockSurvival,clockSurvival,← ENNReal.ofReal_mul (by positivity),← Real.exp_add]
  congr 2
  ring

theorem clockDensity_add (rate : ℝ≥0) (s t : ℝ) :
    clockDensity rate (s+t) = clockSurvival rate s*clockDensity rate t := by
  rw [clockDensity,clockSurvival,clockDensity,← ENNReal.ofReal_mul (by positivity)]
  have he : Real.exp (-(rate : ℝ)*(s+t)) =
      Real.exp (-(rate : ℝ)*s)*Real.exp (-(rate : ℝ)*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  congr 1
  ring

theorem advanceState_time_cut (z : FlightState) (s t r : ℝ) (u : RetainedState) :
    advanceState (s+t,z) (s+r) u = advanceState (t,freeFlight s z) r u := by
  ext1
  · dsimp [advanceState]
    ring
  · ext1
    · simp only [advanceState,freeFlight]
      module
    · rfl

theorem finishFlight_time_cut (z : FlightState) (s t : ℝ) :
    finishFlight (s+t,z) = finishFlight (t,freeFlight s z) := by
  ext1
  · simp only [finishFlight,freeFlight]
    module
  · rfl

theorem first_event_tail (rate : ℝ≥0) (z : FlightState) (s t : ℝ)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    clockSurvival rate (s+t)*f (finishFlight (s+t,z)) +
      (∫⁻ r in Ioc s (s+t), clockDensity rate r *
        ∫⁻ u, ∫⁻ w, f w ∂flightFamily rate (advanceState (s+t,z) r u) ∂uniformizedKernel z.2) =
      clockSurvival rate s * ∫⁻ w, f w ∂flightFamily rate (t,freeFlight s z) := by
  rw [flightFamily_first_event rate (t,freeFlight s z) hf,mul_add]
  change _ = clockSurvival rate s*(clockSurvival rate t*f (finishFlight (t,freeFlight s z))) +
    clockSurvival rate s*(∫⁻ r in Ioc 0 t, clockDensity rate r *
      ∫⁻ u, ∫⁻ w, f w ∂flightFamily rate (advanceState (t,freeFlight s z) r u)
        ∂uniformizedKernel z.2)
  congr 1
  · rw [clockSurvival_add,finishFlight_time_cut,mul_assoc]
  · rw [lintegral_time_shift]
    simp_rw [clockDensity_add,advanceState_time_cut,mul_assoc]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem flightFamily_time_cut (rate : ℝ≥0) (z : FlightState) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) {f : FlightState → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ w, f w ∂flightFamily rate (s+t,z)) =
      clockSurvival rate s * (∫⁻ w, f w ∂flightFamily rate (t,freeFlight s z)) +
        ∫⁻ r in Ioc 0 s, clockDensity rate r *
          ∫⁻ u, ∫⁻ w, f w ∂flightFamily rate (advanceState (s+t,z) r u) ∂uniformizedKernel z.2 := by
  rw [flightFamily_first_event rate (s+t,z) hf]
  change clockSurvival rate (s+t)*f (finishFlight (s+t,z)) +
    (∫⁻ r in Ioc 0 (s+t), clockDensity rate r *
      ∫⁻ u, ∫⁻ w, f w ∂flightFamily rate (advanceState (s+t,z) r u) ∂uniformizedKernel z.2) = _
  rw [lintegral_time_split _ hs ht]
  rw [show ∀ a b c : ℝ≥0∞, a+(b+c) = (a+c)+b from fun a b c => by ac_rfl]
  rw [first_event_tail rate z s t hf]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive Fubini on the ordered two-event time triangle -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem lintegral_time_triangle {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) (T : ℝ) :
    (∫⁻ s in Ioc 0 T, ∫⁻ r in Ioc 0 s, f (s,r)) =
      ∫⁻ r in Ioc 0 T, ∫⁻ s in Icc r T, f (s,r) := by
  classical
  let D : Set (ℝ × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}
  have hD : MeasurableSet D := by
    exact (measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const))
  have hleft : (∫⁻ s in Ioc 0 T, ∫⁻ r in Ioc 0 s, f (s,r)) =
      ∫⁻ s : ℝ, ∫⁻ r : ℝ, D.indicator f (s,r) := by
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Ioc 0 T
    · rw [indicator_of_mem hs,← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr
      intro r
      have he : (s,r) ∈ D ↔ r ∈ Ioc 0 s := by
        simp only [D,mem_ofPred_eq,mem_Ioc]
        exact ⟨fun h => ⟨h.1,h.2.1⟩,fun h => ⟨h.1,h.2,hs.2⟩⟩
      simp only [indicator_apply,he]
    · rw [indicator_of_notMem hs]
      symm
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with r
      apply indicator_of_notMem
      intro hr
      exact hs ⟨hr.1.trans_le hr.2.1,hr.2.2⟩
  have hright : (∫⁻ r in Ioc 0 T, ∫⁻ s in Icc r T, f (s,r)) =
      ∫⁻ r : ℝ, ∫⁻ s : ℝ, D.indicator f (s,r) := by
    rw [← lintegral_indicator measurableSet_Ioc]
    apply lintegral_congr
    intro r
    by_cases hr : r ∈ Ioc 0 T
    · rw [indicator_of_mem hr,← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro s
      have he : (s,r) ∈ D ↔ s ∈ Icc r T := by
        simp only [D,mem_ofPred_eq,mem_Icc]
        exact ⟨fun h => h.2,fun h => ⟨hr.1,h⟩⟩
      simp only [indicator_apply,he]
    · rw [indicator_of_notMem hr]
      symm
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [] with s
      apply indicator_of_notMem
      intro hs
      exact hr ⟨hs.1,hs.2.1.trans hs.2.2⟩
  rw [hleft,hright]
  exact lintegral_lintegral_swap (hf.indicator hD).aemeasurable

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Uniqueness of bounded solutions of the reference first-event equation -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem renewal_solution_comparison (rate : ℝ≥0) {T B : ℝ} (hB : 0 ≤ B)
    {F G D : TimeFlightState → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (hFb : ∀ p, p.1 ∈ Icc 0 T → F p ≤ ENNReal.ofReal B)
    (hFeq : ∀ p, p.1 ∈ Icc 0 T → F p = D p + ∫⁻ q, F q ∂renewalStep rate p)
    (hGeq : ∀ p, p.1 ∈ Icc 0 T → G p = D p + ∫⁻ q, G q ∂renewalStep rate p)
    (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) : F p ≤ G p := by
  have hfinite (n : ℕ) : ∀ p : TimeFlightState, p.1 ∈ Icc 0 T →
      F p ≤ G p + ∫⁻ q, F q ∂((renewalStep rate)^n) p := by
    induction n with
    | zero =>
      intro q hq
      have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
      rw [pow_zero,hi,Kernel.id_apply,lintegral_dirac]
      exact le_add_left le_rfl
    | succ n ih =>
      intro q hq
      have hmon : (∫⁻ w, F w ∂renewalStep rate q) ≤
          ∫⁻ w, (G w + ∫⁻ v, F v ∂((renewalStep rate)^n) w) ∂renewalStep rate q := by
        apply lintegral_mono_ae
        filter_upwards [renewalStep_time_support rate q hq.1] with w hw
        exact ih w ⟨hw.1,hw.2.trans hq.2⟩
      have hpow : ((renewalStep rate)^(n+1)) = (((renewalStep rate)^n)) ∘ₖ renewalStep rate := by
        simpa only [pow_one] using Kernel.pow_add (renewalStep rate) n 1
      calc
        F q = D q + ∫⁻ w, F w ∂renewalStep rate q := hFeq q hq
        _ ≤ D q + ∫⁻ w, (G w + ∫⁻ v, F v ∂((renewalStep rate)^n) w) ∂renewalStep rate q :=
          add_le_add le_rfl hmon
        _ = G q + ∫⁻ v, F v ∂((renewalStep rate)^(n+1)) q := by
          rw [lintegral_add_left hG,hpow,Kernel.lintegral_comp _ _ _ hF,
            ← add_assoc,← hGeq q hq]
  have hr (n : ℕ) : (∫⁻ q, F q ∂((renewalStep rate)^n) p) ≤
      ENNReal.ofReal (B*(((rate : ℝ)*p.1)^n/(n.factorial : ℝ))) := by
    calc
      _ ≤ ∫⁻ _q, ENNReal.ofReal B ∂((renewalStep rate)^n) p := by
        apply lintegral_mono_ae
        filter_upwards [renewalStep_power_time_support rate n p hp.1] with q hq
        exact hFb q ⟨hq.1,hq.2.trans hp.2⟩
      _ = ENNReal.ofReal B * ((renewalStep rate)^n) p univ := lintegral_const _
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (((rate : ℝ)*p.1)^n/(n.factorial : ℝ)) := by
        gcongr
        exact renewalStep_power_mass_bound rate n p hp.1
      _ = _ := (ENNReal.ofReal_mul hB).symm
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (B*(((rate : ℝ)*p.1)^n/(n.factorial : ℝ))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((FloorSemiring.tendsto_pow_div_factorial_atTop ((rate : ℝ)*p.1)).const_mul B)
  have hlim : Tendsto (fun n : ℕ => G p +
      ENNReal.ofReal (B*(((rate : ℝ)*p.1)^n/(n.factorial : ℝ)))) atTop (𝓝 (G p)) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := G p)).add ht
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun n => (hfinite n p hp).trans (add_le_add le_rfl (hr n)))

theorem renewal_solution_unique (rate : ℝ≥0) {T B : ℝ} (hB : 0 ≤ B)
    {F G D : TimeFlightState → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G)
    (hFb : ∀ p, p.1 ∈ Icc 0 T → F p ≤ ENNReal.ofReal B)
    (hGb : ∀ p, p.1 ∈ Icc 0 T → G p ≤ ENNReal.ofReal B)
    (hFeq : ∀ p, p.1 ∈ Icc 0 T → F p = D p + ∫⁻ q, F q ∂renewalStep rate p)
    (hGeq : ∀ p, p.1 ∈ Icc 0 T → G p = D p + ∫⁻ q, G q ∂renewalStep rate p)
    (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) : F p = G p :=
  le_antisymm (renewal_solution_comparison rate hB hF hG hFb hFeq hGeq p hp)
    (renewal_solution_comparison rate hB hG hF hGb hGeq hFeq p hp)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Chapman–Kolmogorov for the actual space-and-velocity flight law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightFamily_average_bound (rate : ℝ≥0) (p : TimeFlightState) (hp : 0 ≤ p.1)
    {f : FlightState → ℝ≥0∞} {B : ℝ≥0∞} (hb : ∀ z, f z ≤ B) :
    (∫⁻ z, f z ∂flightFamily rate p) ≤ B := by
  have he : flightFamily rate p = flightKernel rate ⟨p.1,hp⟩ p.2 :=
    flightFamily_eq rate ⟨p.1,hp⟩ p.2
  rw [he]
  calc
    _ ≤ ∫⁻ _z, B ∂flightKernel rate ⟨p.1,hp⟩ p.2 := lintegral_mono hb
    _ = B := by
      have hm := (flightKernel_isMarkov rate ⟨p.1,hp⟩).isProbabilityMeasure p.2
      rw [lintegral_const,hm.measure_univ,mul_one]

theorem advanceState_add_remaining (p : TimeFlightState) (t r : ℝ) (u : RetainedState) :
    advanceState (p.1+t,p.2) r u =
      ((advanceState p r u).1+t,(advanceState p r u).2) := by
  ext1
  · simp only [advanceState]
    ring
  · rfl

theorem flightFamily_add_average (rate : ℝ≥0) {t : ℝ} (ht : 0 ≤ t)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) (hb : ∀ z, f z ≤ 1)
    (p : TimeFlightState) (hp : 0 ≤ p.1) :
    (∫⁻ w, f w ∂flightFamily rate (p.1+t,p.2)) =
      ∫⁻ z, ∫⁻ w, f w ∂flightFamily rate (t,z) ∂flightFamily rate p := by
  let F : TimeFlightState → ℝ≥0∞ := fun q => ∫⁻ w, f w ∂flightFamily rate (q.1+t,q.2)
  let g : FlightState → ℝ≥0∞ := fun z => ∫⁻ w, f w ∂flightFamily rate (t,z)
  let G : TimeFlightState → ℝ≥0∞ := fun q => ∫⁻ z, g z ∂flightFamily rate q
  let D : TimeFlightState → ℝ≥0∞ := fun q => clockSurvival rate q.1*g (finishFlight q)
  have hF : Measurable F := (hf.lintegral_kernel (κ := flightFamily rate)).comp (by fun_prop)
  have hg : Measurable g := (hf.lintegral_kernel (κ := flightFamily rate)).comp
    (measurable_const.prodMk measurable_id)
  have hG : Measurable G := hg.lintegral_kernel
  have hFb (q : TimeFlightState) (hq : q.1 ∈ Icc 0 p.1) : F q ≤ ENNReal.ofReal 1 := by
    simpa only [ENNReal.ofReal_one] using
      flightFamily_average_bound rate (q.1+t,q.2) (add_nonneg hq.1 ht) hb
  have hgb (z : FlightState) : g z ≤ 1 := flightFamily_average_bound rate (t,z) ht hb
  have hGb (q : TimeFlightState) (hq : q.1 ∈ Icc 0 p.1) : G q ≤ ENNReal.ofReal 1 := by
    simpa only [ENNReal.ofReal_one] using flightFamily_average_bound rate q hq.1 hgb
  have hFeq (q : TimeFlightState) (hq : q.1 ∈ Icc 0 p.1) :
      F q = D q + ∫⁻ w, F w ∂renewalStep rate q := by
    rw [renewalStep_lintegral rate q hF]
    have hc := flightFamily_time_cut rate q.2 hq.1 ht hf
    simp_rw [advanceState_add_remaining] at hc
    exact hc
  have hGeq (q : TimeFlightState) (_hq : q.1 ∈ Icc 0 p.1) :
      G q = D q + ∫⁻ w, G w ∂renewalStep rate q :=
    flightFamily_renewal rate q hg
  exact renewal_solution_unique rate (by norm_num : (0:ℝ) ≤ 1) hF hG hFb hGb hFeq hGeq p ⟨hp,le_rfl⟩

theorem flightKernel_add (rate s t : ℝ≥0) :
    flightKernel rate (s+t) = flightKernel rate t ∘ₖ flightKernel rate s := by
  ext z A hA
  have hi : Measurable (A.indicator (1 : FlightState → ℝ≥0∞)) := measurable_const.indicator hA
  have hb (w : FlightState) : A.indicator (1 : FlightState → ℝ≥0∞) w ≤ 1 := by
    by_cases h : w ∈ A <;> simp [h]
  have hh := flightFamily_add_average rate t.coe_nonneg hi hb ((s : ℝ),z) s.coe_nonneg
  simp only [flightFamily_eq,lintegral_indicator_one hA] at hh
  have he := flightFamily_eq rate (s+t) z
  simp only [NNReal.coe_add] at he
  rw [he] at hh
  rw [Kernel.comp_apply' _ _ _ hA]
  exact hh

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The scalar exponential factor in the reference branching equation -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

def growthWeight (c t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (c*t))
def growthDensity (c T s : ℝ) : ℝ≥0∞ := ENNReal.ofReal (c*Real.exp (c*(T-s)))

theorem growthWeight_measurable (c : ℝ) : Measurable (growthWeight c) := by
  unfold growthWeight
  fun_prop

theorem growthDensity_measurable (c T : ℝ) : Measurable (growthDensity c T) := by
  unfold growthDensity
  fun_prop

theorem growthWeight_add (c s t : ℝ) :
    growthWeight c (s+t) = growthWeight c s*growthWeight c t := by
  rw [growthWeight,growthWeight,growthWeight,← ENNReal.ofReal_mul (by positivity),← Real.exp_add]
  congr 2
  ring

theorem growthDensity_integral {c r T : ℝ} (hc : 0 ≤ c) (hr : r ≤ T) :
    (∫⁻ s in Icc r T, growthDensity c T s) = growthWeight c (T-r)-1 := by
  let f : ℝ → ℝ := fun s => c*Real.exp (c*(T-s))
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have hi : IntegrableOn f (Ioc r T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hr).mp (hcont.intervalIntegrable _ _)
  have hd (s : ℝ) : HasDerivAt (fun x : ℝ => -Real.exp (c*(T-x))) (f s) s := by
    convert (((hasDerivAt_const s T).sub (hasDerivAt_id s)).const_mul c).exp.neg using 1
    · rfl
    · dsimp [f]
      ring
  have he : (∫ s in r..T, f s) = Real.exp (c*(T-r))-1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) (hcont.intervalIntegrable _ _)]
    simp only [sub_self,mul_zero,Real.exp_zero]
    ring
  rw [← restrict_Ioc_eq_restrict_Icc]
  change (∫⁻ s in Ioc r T, ENNReal.ofReal (f s)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun s => mul_nonneg hc (Real.exp_pos _).le)),
    ← intervalIntegral.integral_of_le hr,he]
  simpa only [growthWeight,ENNReal.ofReal_one] using
    ENNReal.ofReal_sub (Real.exp (c*(T-r))) (by norm_num : (0:ℝ) ≤ 1)

theorem growthWeight_split {c r T : ℝ} (hc : 0 ≤ c) (hr : r ≤ T) :
    growthWeight c (T-r) = 1+∫⁻ s in Icc r T, growthDensity c T s := by
  rw [growthDensity_integral hc hr,add_comm,tsub_add_cancel_of_le]
  simpa only [growthWeight,ENNReal.ofReal_one] using
    ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hc (sub_nonneg.mpr hr)))

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exponential weighting of a positive first-event time-cut identity -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weighted_time_cut {c T : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T)
    {P D : ℝ≥0∞} {A B : ℝ → ℝ≥0∞} (hA : Measurable A) (hB : Measurable B)
    (hcut : ∀ s ∈ Ioc 0 T, P = A s + ∫⁻ r in Ioc 0 s, B r)
    (htop : P = D + ∫⁻ r in Ioc 0 T, B r) :
    growthWeight c T * P = D +
      (∫⁻ r in Ioc 0 T, growthWeight c (T-r)*B r) +
      ∫⁻ s in Ioc 0 T, growthDensity c T s*A s := by
  let J : ℝ≥0∞ := ∫⁻ s in Ioc 0 T, growthDensity c T s * ∫⁻ r in Ioc 0 s, B r
  have hJ : J = ∫⁻ r in Ioc 0 T,
      (∫⁻ s in Icc r T, growthDensity c T s)*B r := by
    unfold J
    have hp (s : ℝ) : growthDensity c T s * (∫⁻ r in Ioc 0 s, B r) =
        ∫⁻ r in Ioc 0 s, growthDensity c T s*B r :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    simp_rw [hp]
    have hm : Measurable (fun p : ℝ × ℝ => growthDensity c T p.1*B p.2) :=
      ((growthDensity_measurable c T).comp measurable_fst).mul (hB.comp measurable_snd)
    rw [lintegral_time_triangle hm T]
    apply lintegral_congr
    intro r
    simpa only using! lintegral_mul_const (μ := volume.restrict (Icc r T))
      (B r) (growthDensity_measurable c T)
  have hsum : (∫⁻ r in Ioc 0 T, B r) + J =
      ∫⁻ r in Ioc 0 T, growthWeight c (T-r)*B r := by
    rw [hJ,← lintegral_add_left hB]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [growthWeight_split hc hr.2,add_mul,one_mul]
  have hi : (∫⁻ s in Ioc 0 T, growthDensity c T s*P) =
      (∫⁻ s in Ioc 0 T, growthDensity c T s*A s) + J := by
    calc
      _ = ∫⁻ s in Ioc 0 T, growthDensity c T s*(A s+∫⁻ r in Ioc 0 s, B r) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        rw [← hcut s hs]
      _ = _ := by
        simp_rw [mul_add]
        exact lintegral_add_left ((growthDensity_measurable c T).mul hA) _
  have hscalar : growthWeight c T = 1+∫⁻ s in Ioc 0 T, growthDensity c T s := by
    simpa only [sub_zero,← restrict_Ioc_eq_restrict_Icc] using growthWeight_split hc hT
  calc
    growthWeight c T*P = P+∫⁻ s in Ioc 0 T, growthDensity c T s*P := by
      rw [hscalar,add_mul,one_mul,lintegral_mul_const _ (growthDensity_measurable c T)]
    _ = D+(∫⁻ r in Ioc 0 T, B r)+((∫⁻ s in Ioc 0 T, growthDensity c T s*A s)+J) := by
      rw [hi,htop]
    _ = D+((∫⁻ r in Ioc 0 T, B r)+J)+(∫⁻ s in Ioc 0 T, growthDensity c T s*A s) := by ac_rfl
    _ = _ := by rw [hsum]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The reference flight with a constant positive branching potential -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def weightedFlight (rate : ℝ≥0) (c : ℝ) (f : FlightState → ℝ≥0∞)
    (p : TimeFlightState) : ℝ≥0∞ :=
  growthWeight c p.1 * ∫⁻ z, f z ∂flightFamily rate p

theorem weightedFlight_measurable (rate : ℝ≥0) (c : ℝ)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) : Measurable (weightedFlight rate c f) :=
  ((growthWeight_measurable c).comp measurable_fst).mul (hf.lintegral_kernel)

theorem clockDensity_eq (rate : ℝ≥0) (s : ℝ) :
    clockDensity rate s = clockSurvival rate s * ENNReal.ofReal rate := by
  rw [clockDensity,clockSurvival,← ENNReal.ofReal_mul (by positivity),mul_comm]

theorem growthDensity_eq {c : ℝ} (hc : 0 ≤ c) (T s : ℝ) :
    growthDensity c T s = ENNReal.ofReal c * growthWeight c (T-s) :=
  ENNReal.ofReal_mul hc

theorem weightedFlight_first_event (rate : ℝ≥0) {c : ℝ} (hc : 0 ≤ c)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) (p : TimeFlightState) (hp : 0 ≤ p.1) :
    weightedFlight rate c f p = clockSurvival rate p.1*f (finishFlight p) +
      (∫⁻ s in Ioc 0 p.1, clockDensity rate s *
        ∫⁻ u, weightedFlight rate c f (advanceState p s u) ∂uniformizedKernel p.2.2) +
      ∫⁻ s in Ioc 0 p.1, clockSurvival rate s * ENNReal.ofReal c *
        weightedFlight rate c f (p.1-s,freeFlight s p.2) := by
  let A : ℝ → ℝ≥0∞ := fun s => clockSurvival rate s *
    ∫⁻ z, f z ∂flightFamily rate (p.1-s,freeFlight s p.2)
  let B : ℝ → ℝ≥0∞ := fun s => clockDensity rate s *
    ∫⁻ u, ∫⁻ z, f z ∂flightFamily rate (advanceState p s u) ∂uniformizedKernel p.2.2
  have hA : Measurable A := by
    apply Measurable.mul
    · unfold clockSurvival
      fun_prop
    · exact (hf.lintegral_kernel (κ := flightFamily rate)).comp (by
        unfold freeFlight
        fun_prop)
  have hB : Measurable B := by
    apply Measurable.mul
    · unfold clockDensity
      fun_prop
    · have hm : Measurable (fun q : ℝ × RetainedState =>
          ∫⁻ z, f z ∂flightFamily rate (advanceState p q.1 q.2)) :=
        (hf.lintegral_kernel (κ := flightFamily rate)).comp (by
          unfold advanceState freeFlight
          fun_prop)
      exact hm.lintegral_prod_right'
  have hcut (s : ℝ) (hs : s ∈ Ioc 0 p.1) :
      (∫⁻ z, f z ∂flightFamily rate p) = A s + ∫⁻ r in Ioc 0 s, B r := by
    have hh := flightFamily_time_cut rate p.2 hs.1.le (sub_nonneg.mpr hs.2) hf
    simpa only [add_sub_cancel,p.eta] using hh
  have htop : (∫⁻ z, f z ∂flightFamily rate p) =
      clockSurvival rate p.1*f (finishFlight p)+∫⁻ s in Ioc 0 p.1, B s :=
    flightFamily_first_event rate p hf
  have h := weighted_time_cut hc hp hA hB hcut htop
  change weightedFlight rate c f p = _ at h
  rw [h]
  congr 1
  · congr 1
    apply lintegral_congr
    intro s
    have hw : growthWeight c (p.1-s) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [show growthWeight c (p.1-s)*B s = clockDensity rate s *
        (growthWeight c (p.1-s) * ∫⁻ u, ∫⁻ z, f z ∂flightFamily rate (advanceState p s u)
          ∂uniformizedKernel p.2.2) by dsimp [B]; ac_rfl]
    rw [← lintegral_const_mul' _ _ hw]
    rfl
  · apply lintegral_congr
    intro s
    rw [growthDensity_eq hc]
    dsimp [A,weightedFlight]
    ac_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Damped finite collision histories for the positive reference gain -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def eventAfterWait (K : Kernel RetainedState RetainedState) :
    Kernel (TimeFlightState × ℝ) TimeFlightState :=
  (Kernel.id ×ₖ K.comap (fun q : TimeFlightState × ℝ => q.1.2.2)
    (by fun_prop)).map (fun q => advanceState q.1.1 q.1.2 q.2)

def rawEventStep (K : Kernel RetainedState RetainedState) : Kernel TimeFlightState TimeFlightState :=
  eventAfterWait K ∘ₖ (Kernel.id ×ₖ waitingTime)

instance eventAfterWait_isSFinite (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K] :
    IsSFiniteKernel (eventAfterWait K) := by unfold eventAfterWait; infer_instance

instance rawEventStep_isSFinite (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K] :
    IsSFiniteKernel (rawEventStep K) := by unfold rawEventStep; infer_instance

def eventDensity (rate : ℝ≥0) (p q : TimeFlightState) : ℝ≥0∞ :=
  clockSurvival rate (p.1-q.1)

theorem eventDensity_measurable (rate : ℝ≥0) : Measurable (Function.uncurry (eventDensity rate)) := by
  unfold eventDensity clockSurvival
  fun_prop

def eventStep (rate : ℝ≥0) (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K] :
    Kernel TimeFlightState TimeFlightState :=
  Kernel.withDensity (rawEventStep K) (eventDensity rate)

instance eventStep_isSFinite (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] : IsSFiniteKernel (eventStep rate K) := by
  unfold eventStep
  apply Kernel.IsSFiniteKernel.withDensity
  intro p q
  exact ENNReal.ofReal_ne_top

theorem rawEventStep_lintegral (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K]
    (p : TimeFlightState) {F : TimeFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂rawEventStep K p) =
      ∫⁻ s in Ioc 0 p.1, ∫⁻ u, F (advanceState p s u) ∂K p.2.2 := by
  have ha (q : TimeFlightState × ℝ) : (∫⁻ p, F p ∂eventAfterWait K q) =
      ∫⁻ u, F (advanceState q.1 q.2 u) ∂K q.1.2.2 := by
    rw [eventAfterWait,Kernel.lintegral_map _ advanceState_measurable q hF]
    simpa only [Function.comp_def,Kernel.comap_apply] using!
      Kernel.lintegral_id_prod (hF.comp advanceState_measurable)
        (K.comap (fun q : TimeFlightState × ℝ => q.1.2.2) (by fun_prop)) q
  rw [rawEventStep,Kernel.lintegral_comp _ _ _ hF,
    Kernel.lintegral_id_prod (hF.lintegral_kernel (κ := eventAfterWait K))]
  simp_rw [ha]
  rw [waitingTime_apply]

theorem eventStep_lintegral (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (p : TimeFlightState) {F : TimeFlightState → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂eventStep rate K p) =
      ∫⁻ s in Ioc 0 p.1, clockSurvival rate s * ∫⁻ u, F (advanceState p s u) ∂K p.2.2 := by
  rw [eventStep,Kernel.lintegral_withDensity _ (eventDensity_measurable rate) _ hF,
    rawEventStep_lintegral K p]
  · apply lintegral_congr
    intro s
    have he (u : RetainedState) : eventDensity rate p (advanceState p s u) =
        clockSurvival rate s := by simp only [eventDensity,advanceState,sub_sub_cancel]
    simp_rw [he]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · exact ((eventDensity_measurable rate).comp (measurable_const.prodMk measurable_id)).mul hF

instance eventStep_pow_isSFinite (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (n : ℕ) : IsSFiniteKernel ((eventStep rate K)^n) := by
  induction n with
  | zero => change IsSFiniteKernel Kernel.id; infer_instance
  | succ n ih =>
    rw [show (eventStep rate K)^(n+1) = ((eventStep rate K)^n) ∘ₖ eventStep rate K by
      simpa only [pow_one] using Kernel.pow_add (eventStep rate K) n 1]
    let _ := ih
    infer_instance

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Factorial bounds and time support of positive collision histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem clockSurvival_le_one (rate : ℝ≥0) {s : ℝ} (hs : 0 ≤ s) :
    clockSurvival rate s ≤ 1 := by
  simpa only [clockSurvival,ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
    (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr rate.coe_nonneg) hs))

theorem eventStep_power_mass_bound (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] {C : ℝ} (_hC : 0 ≤ C)
    (hK : ∀ v, K v univ ≤ ENNReal.ofReal C) (n : ℕ) (p : TimeFlightState) (hp : 0 ≤ p.1) :
    ((eventStep rate K)^n) p univ ≤ ENNReal.ofReal C^n * simplexTime n p.1 := by
  induction n generalizing p with
  | zero =>
    have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
    rw [pow_zero,hi,Kernel.id_apply,Measure.dirac_apply_of_mem (mem_univ p),
      simplexTime_zero,pow_zero,one_mul]
  | succ n ih =>
    rw [show (eventStep rate K)^(n+1) = ((eventStep rate K)^n) ∘ₖ eventStep rate K by
      simpa only [pow_one] using Kernel.pow_add (eventStep rate K) n 1,
      Kernel.comp_apply' _ _ _ MeasurableSet.univ,
      eventStep_lintegral rate K p (((eventStep rate K)^n).measurable_coe MeasurableSet.univ)]
    calc
      _ ≤ ∫⁻ s in Ioc 0 p.1, ENNReal.ofReal C^n*simplexTime n (p.1-s)*ENNReal.ofReal C := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        calc
          _ ≤ 1 * (∫⁻ _u, ENNReal.ofReal C^n*simplexTime n (p.1-s) ∂K p.2.2) := by
            apply mul_le_mul' (clockSurvival_le_one rate hs.1.le)
            apply lintegral_mono
            intro u
            exact ih _ (sub_nonneg.mpr hs.2)
          _ ≤ _ := by
            rw [one_mul,lintegral_const]
            exact mul_le_mul' le_rfl (hK _)
      _ = ENNReal.ofReal C^(n+1) * ∫⁻ s in Ioc 0 p.1, simplexTime n (p.1-s) := by
        have he (s : ℝ) : ENNReal.ofReal C^n*simplexTime n (p.1-s)*ENNReal.ofReal C =
            ENNReal.ofReal C^(n+1)*simplexTime n (p.1-s) := by rw [pow_succ]; ac_rfl
        simp_rw [he]
        exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      _ = _ := by rw [simplexTime_integral n hp]

theorem eventStep_time_support (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (p : TimeFlightState) :
    ∀ᵐ q ∂eventStep rate K p, q.1 ∈ Icc 0 p.1 := by
  let A : Set TimeFlightState := {q | q.1 ∉ Icc 0 p.1}
  have hA : MeasurableSet A := by dsimp [A]; measurability
  change eventStep rate K p A = 0
  rw [← lintegral_indicator_one hA,eventStep_lintegral rate K p
    (F := A.indicator 1) (measurable_const.indicator hA)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have he : (∫⁻ u, A.indicator 1 (advanceState p s u) ∂K p.2.2) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro u
    have hq : (advanceState p s u).1 ∈ Icc 0 p.1 :=
      ⟨sub_nonneg.mpr hs.2,sub_le_self _ hs.1.le⟩
    exact indicator_of_notMem (show advanceState p s u ∉ A from not_not.mpr hq) 1
  simp only [he,mul_zero,Pi.zero_apply]

theorem eventStep_power_time_support (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] (n : ℕ) (p : TimeFlightState) (hp : 0 ≤ p.1) :
    ∀ᵐ q ∂((eventStep rate K)^n) p, q.1 ∈ Icc 0 p.1 := by
  induction n generalizing p with
  | zero =>
    have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
    rw [pow_zero,hi,Kernel.id_apply,ae_dirac_iff (by measurability)]
    exact ⟨hp,le_rfl⟩
  | succ n ih =>
    rw [show (eventStep rate K)^(n+1) = ((eventStep rate K)^n) ∘ₖ eventStep rate K by
      simpa only [pow_one] using Kernel.pow_add (eventStep rate K) n 1]
    apply Kernel.ae_comp_of_ae_ae (by measurability)
    filter_upwards [eventStep_time_support rate K p] with q hq
    filter_upwards [ih q hq.1] with w hw
    exact ⟨hw.1,hw.2.trans hq.2⟩

theorem eventStep_bounded_remainder (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] {C M T : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hK : ∀ v, K v univ ≤ ENNReal.ofReal C) {F : TimeFlightState → ℝ≥0∞}
    (hF : ∀ q, q.1 ∈ Icc 0 T → F q ≤ ENNReal.ofReal M)
    (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) :
    Tendsto (fun n : ℕ => ∫⁻ q, F q ∂((eventStep rate K)^n) p) atTop (𝓝 0) := by
  have hb (n : ℕ) : (∫⁻ q, F q ∂((eventStep rate K)^n) p) ≤
      ENNReal.ofReal (M*((C*p.1)^n/(n.factorial : ℝ))) := by
    calc
      _ ≤ ∫⁻ _q, ENNReal.ofReal M ∂((eventStep rate K)^n) p := by
        apply lintegral_mono_ae
        filter_upwards [eventStep_power_time_support rate K n p hp.1] with q hq
        exact hF q ⟨hq.1,hq.2.trans hp.2⟩
      _ = ENNReal.ofReal M * ((eventStep rate K)^n) p univ := lintegral_const _
      _ ≤ ENNReal.ofReal M * (ENNReal.ofReal C^n*simplexTime n p.1) :=
        mul_le_mul' le_rfl (eventStep_power_mass_bound rate K hC hK n p hp.1)
      _ = _ := by
        rw [simplexTime,← ENNReal.ofReal_pow hC,← ENNReal.ofReal_mul (pow_nonneg hC _),
          ← ENNReal.ofReal_mul hM,mul_pow]
        congr 1
        ring
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal (M*((C*p.1)^n/(n.factorial : ℝ))))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((FloorSemiring.tendsto_pow_div_factorial_atTop (C*p.1)).const_mul M)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le) hb

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive finite-history exhaustion for a bounded reference subsolution -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

def eventHistory (rate : ℝ≥0) (K : Kernel RetainedState RetainedState) [IsSFiniteKernel K]
    (D : TimeFlightState → ℝ≥0∞) (n : ℕ) (p : TimeFlightState) : ℝ≥0∞ :=
  ∫⁻ q, D q ∂((eventStep rate K)^n) p

theorem eventHistory_measurable (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] {D : TimeFlightState → ℝ≥0∞} (hD : Measurable D) (n : ℕ) :
    Measurable (eventHistory rate K D n) := hD.lintegral_kernel

theorem event_finite_expansion (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] {F D : TimeFlightState → ℝ≥0∞} (hF : Measurable F) (hD : Measurable D)
    {T : ℝ} (hsub : ∀ q, q.1 ∈ Icc 0 T → F q ≤ D q + ∫⁻ w, F w ∂eventStep rate K q)
    (n : ℕ) (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) :
    F p ≤ (∑ j ∈ Finset.range n, eventHistory rate K D j p) +
      ∫⁻ q, F q ∂((eventStep rate K)^n) p := by
  induction n with
  | zero =>
    have hi : (1 : Kernel TimeFlightState TimeFlightState) = Kernel.id := rfl
    rw [Finset.range_zero,Finset.sum_empty,pow_zero,hi,Kernel.id_apply,lintegral_dirac,zero_add]
  | succ n ih =>
    have hr : (∫⁻ q, F q ∂((eventStep rate K)^n) p) ≤ eventHistory rate K D n p +
        ∫⁻ q, F q ∂((eventStep rate K)^(n+1)) p := by
      calc
        _ ≤ ∫⁻ q, (D q + ∫⁻ w, F w ∂eventStep rate K q) ∂((eventStep rate K)^n) p := by
          apply lintegral_mono_ae
          filter_upwards [eventStep_power_time_support rate K n p hp.1] with q hq
          exact hsub q ⟨hq.1,hq.2.trans hp.2⟩
        _ = _ := by
          rw [lintegral_add_left hD]
          have he : (eventStep rate K)^(n+1) = eventStep rate K ∘ₖ ((eventStep rate K)^n) := by
            simpa only [pow_one,Nat.add_comm] using Kernel.pow_add (eventStep rate K) 1 n
          rw [he,Kernel.lintegral_comp _ _ _ hF]
          rfl
    calc
      _ ≤ (∑ j ∈ Finset.range n, eventHistory rate K D j p) +
          (eventHistory rate K D n p + ∫⁻ q, F q ∂((eventStep rate K)^(n+1)) p) :=
        ih.trans (add_le_add le_rfl hr)
      _ = _ := by rw [Finset.sum_range_succ,add_assoc]

theorem event_subsolution_le_series (rate : ℝ≥0) (K : Kernel RetainedState RetainedState)
    [IsSFiniteKernel K] {C M T : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hK : ∀ v, K v univ ≤ ENNReal.ofReal C)
    {F D : TimeFlightState → ℝ≥0∞} (hF : Measurable F) (hD : Measurable D)
    (hbound : ∀ q, q.1 ∈ Icc 0 T → F q ≤ ENNReal.ofReal M)
    (hsub : ∀ q, q.1 ∈ Icc 0 T → F q ≤ D q + ∫⁻ w, F w ∂eventStep rate K q)
    (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) :
    F p ≤ ∑' n, eventHistory rate K D n p := by
  have hs := ENNReal.tendsto_nat_tsum (fun n => eventHistory rate K D n p)
  have hr := eventStep_bounded_remainder rate K hC hM hK hbound p hp
  have hlim := hs.add hr
  simp only [add_zero] at hlim
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim
    (fun n => event_finite_expansion rate K hF hD hsub n p hp)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Exponentially growing reference flight is dominated by actual positive histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def referenceClock : ℝ≥0 := ⟨48*Real.pi,by positivity⟩
def referenceGrowth : ℝ := 11*Real.pi/6

theorem branchingKernel_mass_bound (v : RetainedState) :
    branchingKernel v univ ≤ ENNReal.ofReal (96*Real.pi) := by
  have hs := (stateFrequency_bounds v).2
  have hr := stateRate_bounds v
  have hm := (inferInstance : IsMarkovKernel stateKernel).isProbabilityMeasure v
  rw [branchingKernel_apply,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    smul_eq_mul,smul_eq_mul,hm.measure_univ,Measure.dirac_apply_of_mem (mem_univ v),mul_one,mul_one]
  rw [← ENNReal.ofReal_add (by linarith [Real.pi_pos] : 0 ≤ stateRate v)
    (by linarith [Real.pi_pos] : 0 ≤ 48*Real.pi-stateFrequency v)]
  apply ENNReal.ofReal_le_ofReal
  have hf := (stateFrequency_bounds v).1
  linarith [Real.pi_pos]

def flightSeed (rate : ℝ≥0) (f : FlightState → ℝ≥0∞) (p : TimeFlightState) : ℝ≥0∞ :=
  clockSurvival rate p.1*f (finishFlight p)

theorem flightSeed_measurable (rate : ℝ≥0) {f : FlightState → ℝ≥0∞}
    (hf : Measurable f) : Measurable (flightSeed rate f) := by
  apply Measurable.mul
  · unfold clockSurvival
    fun_prop
  · exact hf.comp finishFlight_measurable

theorem weightedFlight_branching_subsolution {f : FlightState → ℝ≥0∞} (hf : Measurable f)
    (p : TimeFlightState) (hp : 0 ≤ p.1) :
    weightedFlight referenceClock referenceGrowth f p ≤ flightSeed referenceClock f p +
      ∫⁻ q, weightedFlight referenceClock referenceGrowth f q ∂eventStep referenceClock branchingKernel p := by
  let F := weightedFlight referenceClock referenceGrowth f
  have hF : Measurable F := weightedFlight_measurable _ _ hf
  have hgain : Measurable (fun s : ℝ => clockDensity referenceClock s *
      ∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2) := by
    have hm : Measurable (fun q : ℝ × RetainedState => F (advanceState p q.1 q.2)) :=
      hF.comp (by unfold advanceState freeFlight; fun_prop)
    exact (show Measurable (clockDensity referenceClock) by unfold clockDensity; fun_prop).mul
      hm.lintegral_prod_right'
  rw [weightedFlight_first_event referenceClock (by unfold referenceGrowth; positivity) hf p hp,
    eventStep_lintegral _ _ _ hF]
  change flightSeed referenceClock f p + _ + _ ≤ flightSeed referenceClock f p + _
  rw [add_assoc,← lintegral_add_left hgain]
  apply add_le_add le_rfl
  apply lintegral_mono
  intro s
  have hinner := lintegral_mono' (branchingKernel_lower p.2.2)
    (f := fun u => F (advanceState p s u)) le_rfl
  rw [lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure,
    lintegral_dirac,smul_eq_mul,smul_eq_mul] at hinner
  dsimp only
  rw [clockDensity_eq]
  change clockSurvival referenceClock s * ENNReal.ofReal (referenceClock : ℝ) *
      (∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2) +
    clockSurvival referenceClock s * ENNReal.ofReal referenceGrowth *
      F (advanceState p s p.2.2) ≤ _
  calc
    _ = clockSurvival referenceClock s * (ENNReal.ofReal (48*Real.pi)*
        (∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2) +
        ENNReal.ofReal (11*Real.pi/6)*F (advanceState p s p.2.2)) := by
      have hclock : (referenceClock : ℝ) = 48*Real.pi := rfl
      rw [hclock,mul_add]
      unfold referenceGrowth
      ac_rfl
    _ ≤ _ := mul_le_mul' le_rfl hinner

theorem weightedFlight_le_branching_series {f : FlightState → ℝ≥0∞} (hf : Measurable f)
    (hb : ∀ z, f z ≤ 1) (p : TimeFlightState) (hp : 0 ≤ p.1) :
    weightedFlight referenceClock referenceGrowth f p ≤
      ∑' n, eventHistory referenceClock branchingKernel (flightSeed referenceClock f) n p := by
  apply event_subsolution_le_series referenceClock branchingKernel
    (C := 96*Real.pi) (M := Real.exp (referenceGrowth*p.1)) (T := p.1)
    (by positivity) (Real.exp_pos _).le branchingKernel_mass_bound
    (weightedFlight_measurable _ _ hf) (flightSeed_measurable _ hf)
  · intro q hq
    calc
      _ ≤ growthWeight referenceGrowth q.1*1 :=
        mul_le_mul' le_rfl (flightFamily_average_bound _ q hq.1 hb)
      _ ≤ _ := by
        rw [mul_one]
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hq.2 (by unfold referenceGrowth; positivity)
  · intro q hq
    exact weightedFlight_branching_subsolution hf q hq.1
  · exact ⟨hp,le_rfl⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Unnormalized beam intensities behind the positive reference histories -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem referenceJump_intensity (e v : V) (he : ‖e‖ = 1) :
    ENNReal.ofReal (2*frequency v e) • referenceJump e v =
      ENNReal.ofReal (4*Real.pi*‖v-e‖) • outgoing (v,e) +
      ENNReal.ofReal (4*Real.pi*‖v+e‖) • outgoing (v,-e) := by
  have hd : ‖v-e‖+‖v+e‖ ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) (two_beam_distance_lower v e he))
  rw [referenceJump_measure,smul_add,smul_smul,smul_smul,
    ← ENNReal.ofReal_mul (by unfold frequency; positivity),
    ← ENNReal.ofReal_mul (by unfold frequency; positivity),minusProbability_eq e v he]
  have hp : 2*frequency v e*plusProbability e v = 4*Real.pi*‖v-e‖ := by
    unfold frequency plusProbability
    field_simp
    ring
  have hm : 2*frequency v e*(‖v+e‖/(‖v-e‖+‖v+e‖)) = 4*Real.pi*‖v+e‖ := by
    unfold frequency
    field_simp
    ring
  rw [hp,hm]

theorem branchingKernel_projection (v : RetainedState) :
    (branchingKernel v).map (Subtype.val : RetainedState → V) =
      ENNReal.ofReal (2*frequency v.1 beamAxis) •
        (referenceJump beamAxis v.1).restrict referenceRegion +
      ENNReal.ofReal (48*Real.pi-stateFrequency v) • Measure.dirac v.1 := by
  rw [branchingKernel_apply,Measure.map_add _ _ measurable_subtype_coe,
    Measure.map_smul,Measure.map_smul,
    stateKernel_map,Measure.map_dirac' measurable_subtype_coe]
  · congr 1
    exact retainedRate_measure_identity beamAxis v.1
      (retention_ne_zero_coarse beamAxis v.1 axis_norms.2.2 (retainedState_norm v))
  all_goals exact measurable_subtype_coe.aemeasurable

theorem branchingKernel_beam_projection (v : RetainedState) :
    (branchingKernel v).map (Subtype.val : RetainedState → V) =
      (ENNReal.ofReal (4*Real.pi*‖v.1-beamAxis‖) • outgoing (v.1,beamAxis) +
        ENNReal.ofReal (4*Real.pi*‖v.1+beamAxis‖) • outgoing (v.1,-beamAxis)).restrict referenceRegion +
      ENNReal.ofReal (48*Real.pi-stateFrequency v) • Measure.dirac v.1 := by
  rw [branchingKernel_projection]
  congr 1
  rw [← Measure.restrict_smul,referenceJump_intensity beamAxis v.1 axis_norms.2.2]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Pointwise collision-rate stability for merely measurable partner fields -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem relative_speed_lipschitz (v w u z : V) :
    |‖v-w‖-‖u-z‖| ≤ ‖v-u‖+‖w-z‖ := by
  apply (abs_norm_sub_norm_le (v-w) (u-z)).trans
  calc
    ‖(v-w)-(u-z)‖ = ‖(v-u)-(w-z)‖ := by congr 1; abel
    _ ≤ _ := norm_sub_le _ _

theorem weighted_speed_error {v w u z : V} {b ε δ R : ℝ}
    (hb : 0 ≤ b) (hb2 : b ≤ 2) (hberr : |b-1| ≤ ε)
    (herr : ‖v-u‖+‖w-z‖ ≤ δ) (hR : ‖u-z‖ ≤ R) :
    |b*‖v-w‖-‖u-z‖| ≤ 2*δ+ε*R := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans hberr
  have hδ : 0 ≤ δ := (add_nonneg (norm_nonneg _) (norm_nonneg _)).trans herr
  calc
    |b*‖v-w‖-‖u-z‖| = |b*(‖v-w‖-‖u-z‖)+(b-1)*‖u-z‖| := by congr 1; ring
    _ ≤ |b| * |‖v-w‖-‖u-z‖|+|b-1| * ‖u-z‖ := by
      simpa only [abs_mul,abs_norm] using abs_add_le (b*(‖v-w‖-‖u-z‖)) ((b-1)*‖u-z‖)
    _ ≤ 2*δ+ε*R := by
      apply add_le_add
      · rw [abs_of_nonneg hb]
        exact mul_le_mul hb2 ((relative_speed_lipschitz v w u z).trans herr)
          (abs_nonneg _) (by norm_num)
      · exact mul_le_mul hberr hR (norm_nonneg _) hε

theorem beam_gain_rate_error {v w u z : V} {b ε δ R : ℝ}
    (hb : 0 ≤ b) (hb2 : b ≤ 2) (hberr : |b-1| ≤ ε)
    (herr : ‖v-u‖+‖w-z‖ ≤ δ) (hR : ‖u-z‖ ≤ R) :
    |4*Real.pi*b*‖v-w‖-4*Real.pi*‖u-z‖| ≤ 4*Real.pi*(2*δ+ε*R) := by
  rw [show 4*Real.pi*b*‖v-w‖-4*Real.pi*‖u-z‖ =
    (4*Real.pi)*(b*‖v-w‖-‖u-z‖) by ring,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 4*Real.pi)]
  exact mul_le_mul_of_nonneg_left (weighted_speed_error hb hb2 hberr herr hR) (by positivity)

def mediumFrequency (v w_plus w_minus : V) (b_plus b_minus : ℝ) : ℝ :=
  2*Real.pi*(b_plus*‖v-w_plus‖+b_minus*‖v-w_minus‖)

theorem medium_frequency_error {v u w_plus w_minus e : V} {b_plus b_minus ε δ R : ℝ}
    (hb_plus : 0 ≤ b_plus) (hb_minus : 0 ≤ b_minus) (hb_plus2 : b_plus ≤ 2) (hb_minus2 : b_minus ≤ 2)
    (he_plus : |b_plus-1| ≤ ε) (he_minus : |b_minus-1| ≤ ε)
    (hv_plus : ‖v-u‖+‖w_plus-e‖ ≤ δ) (hv_minus : ‖v-u‖+‖w_minus-(-e)‖ ≤ δ)
    (hR_plus : ‖u-e‖ ≤ R) (hR_minus : ‖u-(-e)‖ ≤ R) :
    |mediumFrequency v w_plus w_minus b_plus b_minus-frequency u e| ≤ 4*Real.pi*(2*δ+ε*R) := by
  have h_plus := weighted_speed_error hb_plus hb_plus2 he_plus hv_plus hR_plus
  have h_minus := weighted_speed_error hb_minus hb_minus2 he_minus hv_minus hR_minus
  have hn : u-(-e) = u+e := sub_neg_eq_add _ _
  rw [hn] at h_minus
  have heq : mediumFrequency v w_plus w_minus b_plus b_minus-frequency u e =
      (2*Real.pi)*((b_plus*‖v-w_plus‖-‖u-e‖)+(b_minus*‖v-w_minus‖-‖u+e‖)) := by
    unfold mediumFrequency frequency
    ring
  rw [heq,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*Real.pi)]
  have hsum := (abs_add_le (b_plus*‖v-w_plus‖-‖u-e‖) (b_minus*‖v-w_minus‖-‖u+e‖)).trans (add_le_add h_plus h_minus)
  calc
    _ ≤ (2*Real.pi)*((2*δ+ε*R)+(2*δ+ε*R)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Summing the time-simplex second-moment factors -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightWeight_secondMoment_le (rate T : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    flightWeight rate T n * ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T) ≤
      ENNReal.ofReal ((T : ℝ)/rate) * poissonMeasure (rate*T) {n+1} := by
  have hr' : 0 < (rate : ℝ) := hr
  have hn : 0 < (n+2 : ℝ) := by positivity
  let R : ℝ := (T : ℝ)/rate *
    (Real.exp (-(rate : ℝ)*T) * ((rate : ℝ)*T)^(n+1)/(n+1).factorial)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have heq : (Real.exp (-(rate : ℝ)*T)*(rate : ℝ)^n)*
      ((n+1 : ℕ)*simplexVolume (n+2) T) = R*((n+1 : ℝ)/(n+2)) := by
    dsimp [R,simplexVolume]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_pow,pow_succ]
    field_simp
    ring
  rw [flightWeight,← ENNReal.ofReal_mul (by positivity),poissonMeasure_singleton,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simp only [NNReal.coe_mul,← neg_mul]
  change _ ≤ R
  rw [heq]
  exact mul_le_of_le_one_right hR ((div_le_one hn).mpr (by linarith))

theorem flightWeight_secondMoment_sum_le (rate T : ℝ≥0) (hr : 0 < rate) :
    (∑' n : ℕ, flightWeight rate T n *
      ENNReal.ofReal ((n+1 : ℕ)*simplexVolume (n+2) T)) ≤ ENNReal.ofReal ((T : ℝ)/rate) := by
  calc
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((T : ℝ)/rate)*poissonMeasure (rate*T) {n+1} :=
      ENNReal.tsum_le_tsum (flightWeight_secondMoment_le rate T hr)
    _ = ENNReal.ofReal ((T : ℝ)/rate) * ∑' n : ℕ, poissonMeasure (rate*T) {n+1} :=
      ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal ((T : ℝ)/rate) * ∑' n : ℕ, poissonMeasure (rate*T) {n} := by
      have hs := ENNReal.tsum_comp_le_tsum_of_injective Nat.succ_injective
        (fun n => poissonMeasure (rate*T) {n})
      exact mul_le_mul le_rfl hs zero_le zero_le
    _ = ENNReal.ofReal ((T : ℝ)/rate) := by
      have hh : (∑' n : ℕ, poissonMeasure (rate*T) {n}) = 1 := by
        simpa only [lintegral_const,one_mul,measure_univ] using
          (lintegral_countable' (μ := poissonMeasure (rate*T)) (fun _ => (1 : ℝ≥0∞))).symm
      rw [hh,mul_one]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Position and finite-product errors along coupled collision histories -/

noncomputable section

open scoped BigOperators

namespace BoltzmannNonuniqueness.ReferenceGeometry

def finitePosition (x : V) (t : ℕ → ℝ) (v : ℕ → V) (n : ℕ) : V :=
  x + ∑ j ∈ Finset.range n, t j • v j

theorem finite_position_error {x y : V} {t : ℕ → ℝ} {v u : ℕ → V} {n : ℕ} {B : ℝ}
    (ht : ∀ j < n, 0 ≤ t j) (hv : ∀ j < n, ‖v j-u j‖ ≤ B) :
    ‖finitePosition x t v n-finitePosition y t u n‖ ≤
      ‖x-y‖+(∑ j ∈ Finset.range n, t j)*B := by
  have he : finitePosition x t v n-finitePosition y t u n =
      (x-y)+∑ j ∈ Finset.range n, t j • (v j-u j) := by
    simp only [finitePosition,smul_sub,Finset.sum_sub_distrib]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add le_rfl
  calc
    _ ≤ ∑ j ∈ Finset.range n, ‖t j • (v j-u j)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range n, t j*B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn := Finset.mem_range.mp hj
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (ht j hjn)]
      exact mul_le_mul_of_nonneg_left (hv j hjn) (ht j hjn)
    _ = _ := (Finset.sum_mul _ _ _).symm

theorem product_error_bound {a b : ℕ → ℝ} {M δ : ℝ} (hM : 1 ≤ M) (hδ : 0 ≤ δ)
    (ha : ∀ j, |a j| ≤ M) (hb : ∀ j, |b j| ≤ M)
    (hab : ∀ j, |a j-b j| ≤ δ) (n : ℕ) :
    |(∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j)| ≤ (n:ℝ)*M^n*δ := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hp (n : ℕ) : |∏ j ∈ Finset.range n, b j| ≤ M^n := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _j ∈ Finset.range n, M := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => hb j)
      _ = _ := by simp
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ,Finset.prod_range_succ]
    have he : (∏ j ∈ Finset.range n, a j)*a n-(∏ j ∈ Finset.range n, b j)*b n =
        ((∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j))*a n +
          (∏ j ∈ Finset.range n, b j)*(a n-b n) := by ring
    rw [he]
    calc
      _ ≤ |(∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j)| * |a n| +
          |∏ j ∈ Finset.range n, b j| * |a n-b n| := by
        simpa only [abs_mul] using abs_add_le
          (((∏ j ∈ Finset.range n, a j)-(∏ j ∈ Finset.range n, b j))*a n)
          ((∏ j ∈ Finset.range n, b j)*(a n-b n))
      _ ≤ ((n:ℝ)*M^n*δ)*M+M^n*δ := by
        exact add_le_add (mul_le_mul ih (ha n) (abs_nonneg _) (by positivity))
          (mul_le_mul (hp n) (hab n) (abs_nonneg _) (pow_nonneg hM0 _))
      _ ≤ ((n+1:ℕ):ℝ)*M^(n+1)*δ := by
        rw [Nat.cast_add,Nat.cast_one,pow_succ]
        have hh := mul_le_mul_of_nonneg_right hM (mul_nonneg (pow_nonneg hM0 n) hδ)
        nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Coupled positive histories with two beam marks and self-retention marks -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

abbrev HistoryMark := Fin 3

def markedChild (m : HistoryMark) (v wp wm n : V) : V :=
  if m = 0 then v else child v (if m = 1 then wp else wm) n

def markedRate (m : HistoryMark) (v wp wm : V) (bp bm : ℝ) : ℝ :=
  if m = 0 then 48*Real.pi-mediumFrequency v wp wm bp bm
  else if m = 1 then 4*Real.pi*bp*‖v-wp‖ else 4*Real.pi*bm*‖v-wm‖

theorem marked_child_error (m : HistoryMark) {v u wp wm zp zm n : V} {δ ε : ℝ}
    (hn : ‖n‖ = 1) (hv : ‖v-u‖ ≤ δ) (hp : ‖wp-zp‖ ≤ ε) (hm : ‖wm-zm‖ ≤ ε) :
    ‖markedChild m v wp wm n-markedChild m u zp zm n‖ ≤ δ+ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hp
  unfold markedChild
  split
  · exact hv.trans (le_add_of_nonneg_right hε)
  · split
    · exact (child_lipschitz v wp u zp n hn).trans (add_le_add hv hp)
    · exact (child_lipschitz v wm u zm n hn).trans (add_le_add hv hm)

def markedVelocity (v₀ : V) (mark : ℕ → HistoryMark) (wp wm direction : ℕ → V) : ℕ → V
  | 0 => v₀
  | n+1 => markedChild (mark n) (markedVelocity v₀ mark wp wm direction n)
      (wp n) (wm n) (direction n)

theorem marked_velocity_error (v₀ : V) (mark : ℕ → HistoryMark)
    (wp wm zp zm direction : ℕ → V) {ε : ℝ}
    (hn : ∀ j, ‖direction j‖ = 1)
    (hp : ∀ j, ‖wp j-zp j‖ ≤ ε) (hm : ∀ j, ‖wm j-zm j‖ ≤ ε) (n : ℕ) :
    ‖markedVelocity v₀ mark wp wm direction n-markedVelocity v₀ mark zp zm direction n‖ ≤
      (n:ℝ)*ε := by
  induction n with
  | zero => simp [markedVelocity]
  | succ n ih =>
    rw [markedVelocity,markedVelocity]
    exact (marked_child_error (mark n) (hn n) ih (hp n) (hm n)).trans_eq (by push_cast; ring)

theorem marked_rate_error (m : HistoryMark) {v u wp wm e : V} {bp bm ε δ R : ℝ}
    (hp : 0 ≤ bp) (hm : 0 ≤ bm) (hp2 : bp ≤ 2) (hm2 : bm ≤ 2)
    (hep : |bp-1| ≤ ε) (hem : |bm-1| ≤ ε)
    (hvp : ‖v-u‖+‖wp-e‖ ≤ δ) (hvm : ‖v-u‖+‖wm-(-e)‖ ≤ δ)
    (hRp : ‖u-e‖ ≤ R) (hRm : ‖u-(-e)‖ ≤ R) :
    |markedRate m v wp wm bp bm-markedRate m u e (-e) 1 1| ≤
      4*Real.pi*(2*δ+ε*R) := by
  unfold markedRate
  split
  · have hf := medium_frequency_error hp hm hp2 hm2 hep hem hvp hvm hRp hRm
    have heq : mediumFrequency u e (-e) 1 1 = frequency u e := by
      simp only [mediumFrequency,frequency,one_mul,sub_neg_eq_add]
    rw [heq,show 48*Real.pi-mediumFrequency v wp wm bp bm-(48*Real.pi-frequency u e) =
      -(mediumFrequency v wp wm bp bm-frequency u e) by ring,abs_neg]
    exact hf
  · split
    · simpa only [mul_one] using beam_gain_rate_error hp hp2 hep hvp hRp
    · simpa only [mul_one] using beam_gain_rate_error hm hm2 hem hvm hRm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
