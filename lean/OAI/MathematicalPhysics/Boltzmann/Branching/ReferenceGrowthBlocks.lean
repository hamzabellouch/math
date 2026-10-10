import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceMinorization
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceBranchingHistories
import OAI.MathematicalPhysics.Boltzmann.Branching.ReferenceHistoryMoments

namespace OAI

section

/-! # Uniform transverse-velocity entry for the actual Poisson flight -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem poissonKernel_term_le (r : ℝ≥0) (n : ℕ) (v : RetainedState) :
    poissonMeasure r {n} • (uniformizedKernel^n) v ≤ poissonKernel r v := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [poissonKernel,Kernel.sum_apply,Measure.sum_apply _ hA,Measure.smul_apply,smul_eq_mul]
  have hh := ENNReal.le_tsum (f := fun k => (Kernel.withDensity (uniformizedKernel^k)
    (fun _ _ => poissonMeasure r {k})) v A) n
  have heq (k : ℕ) : (Kernel.withDensity (uniformizedKernel^k)
      (fun _ _ => poissonMeasure r {k})) v A = poissonMeasure r {k}*(uniformizedKernel^k) v A := by
    rw [Kernel.withDensity_apply _ (show Measurable
      (Function.uncurry (fun (_ : RetainedState) (_ : RetainedState) => poissonMeasure r {k}))
      from measurable_const),withDensity_const,Measure.smul_apply,smul_eq_mul]
  simpa only [heq] using hh

theorem state_two_transverse_entry {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ v : RetainedState,
      c ≤ (uniformizedKernel^2) v {u | (u : V) ∈ ball firstAxis ζ} := by
  obtain ⟨c,hc,hct,hbound⟩ := retained_two_transverse_entry hζ
  let q := (ENNReal.ofReal (1/12 : ℝ))^2
  have hq : q ≠ 0 := by dsimp [q]; positivity
  have hqt : q ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  refine ⟨q*c,mul_ne_zero hq hc,ENNReal.mul_ne_top hqt hct,?_⟩
  intro v
  have hm : ((stateKernel^2) v).map (Subtype.val : RetainedState → V) =
      (retainedJump beamAxis ∘ₖ retainedJump beamAxis) (v : V) := by
    rw [← Kernel.map_apply _ measurable_subtype_coe,stateKernel_pow_map,Kernel.comap_apply]
    congr 1
    simpa only [pow_one] using Kernel.pow_add (retainedJump beamAxis) 1 1
  have hb := hbound (v : V) (retainedState_norm v)
  rw [← hm,Measure.map_apply measurable_subtype_coe measurableSet_ball] at hb
  exact (mul_le_mul' le_rfl hb).trans
    (stateKernel_power_le_uniformized 2 v {u | (u : V) ∈ ball firstAxis ζ})

theorem poisson_transverse_entry (r : ℝ≥0) (hr : 0 < r) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ v : RetainedState,
      c ≤ poissonKernel r v {u | (u : V) ∈ ball firstAxis ζ} := by
  obtain ⟨c,hc,hct,hbound⟩ := state_two_transverse_entry hζ
  have hp : poissonMeasure r {2} ≠ 0 := by rw [poissonMeasure_singleton]; positivity
  have hpt : poissonMeasure r {2} ≠ ⊤ := measure_ne_top _ _
  refine ⟨poissonMeasure r {2}*c,mul_ne_zero hp hc,ENNReal.mul_ne_top hpt hct,?_⟩
  intro v
  exact (mul_le_mul' le_rfl (hbound v)).trans
    (poissonKernel_term_le r 2 v {u | (u : V) ∈ ball firstAxis ζ})

theorem flightKernel_displacement (rate T : ℝ≥0) (z : FlightState) :
    ∀ᵐ w ∂flightKernel rate T z, ‖w.1-z.1‖ ≤ 5*(T : ℝ) := by
  rw [flightKernel_apply,Measure.ae_sum_iff]
  intro n
  exact Measure.ae_smul_measure (historyKernel_displacement n ((T : ℝ),z) T.coe_nonneg) _

theorem flight_transverse_entry (rate : ℝ≥0) (hr : 0 < rate) {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ z : FlightState,
      c ≤ flightKernel rate 1 z {w | (w.2 : V) ∈ ball firstAxis ζ} := by
  obtain ⟨c,hc,hct,hbound⟩ := poisson_transverse_entry rate hr hζ
  refine ⟨c,hc,hct,?_⟩
  intro z
  have hm := congrArg (fun μ : Measure RetainedState => μ {u | (u : V) ∈ ball firstAxis ζ})
    (flightKernel_velocity_map rate 1 z)
  rw [Measure.map_apply measurable_snd (show MeasurableSet {u : RetainedState | (u : V) ∈ ball firstAxis ζ} from
    measurable_subtype_coe measurableSet_ball),mul_one] at hm
  exact hm.symm ▸ hbound z.2

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Displacement geometry for the three intervals of a branching block -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def blockTarget (x : V) (A κ d : ℝ) : Set FlightState :=
  {w | ‖w.1-(x+(κ*A) • firstAxis)‖ < 3*d*κ*A/4 ∧ ‖(w.2 : V)‖ < 2}

theorem blockTarget_measurable (x : V) (A κ d : ℝ) : MeasurableSet (blockTarget x A κ d) := by
  unfold blockTarget
  measurability

theorem flight_block_geometry {x : V} {A κ d : ℝ} (hA : 0 < A) (hκ : 0 < κ)
    (hd : d ≤ 1) (hlarge : 5 < d*κ*A/4) {z w : FlightState}
    (hz : ‖z.1-x‖ < d*κ*A/4) (hw : ‖w.1-z.1‖ ≤ 5)
    (hv : (w.2 : V) ∈ ball firstAxis (d/4)) :
    freeFlight (κ*A) w ∈ blockTarget x A κ d := by
  have hdist : ‖(w.2 : V)-firstAxis‖ < d/4 := hv
  have hvnorm : ‖(w.2 : V)‖ < 2 := by
    have hh := norm_add_le ((w.2 : V)-firstAxis) firstAxis
    rw [sub_add_cancel,axis_norms.1] at hh
    linarith
  constructor
  · have heq : (freeFlight (κ*A) w).1-(x+(κ*A) • firstAxis) =
        (z.1-x)+(w.1-z.1)+(κ*A) • ((w.2 : V)-firstAxis) := by
      unfold freeFlight
      module
    rw [heq]
    have hn := norm_add_le ((z.1-x)+(w.1-z.1)) ((κ*A) • ((w.2 : V)-firstAxis))
    have hn' := norm_add_le (z.1-x) (w.1-z.1)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (mul_pos hκ hA)] at hn
    have hm := mul_lt_mul_of_pos_left hdist (mul_pos hκ hA)
    nlinarith
  · exact hvnorm

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Cancellation of additional damping against positive retention weights -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem growth_damping_cancel (c δ T : ℝ) :
    growthWeight (c+δ) T * growthWeight (-δ) T = growthWeight c T := by
  unfold growthWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

theorem growth_damping_split (c δ T s : ℝ) :
    growthWeight (c+δ) (T-s) * growthWeight (-δ) T =
      growthWeight c (T-s) * growthWeight (-δ) s := by
  unfold growthWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

theorem growth_damping_clock (L C : ℝ≥0) (s : ℝ) :
    growthWeight ((L:ℝ)-(C:ℝ)) s * clockSurvival L s = clockSurvival C s := by
  unfold growthWeight clockSurvival
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add]
  congr 2
  ring

theorem time_cut_scale (k : ℝ≥0∞) (hk : k ≠ ⊤) {P D : ℝ≥0∞}
    {A B : ℝ → ℝ≥0∞} {T : ℝ}
    (hcut : ∀ s ∈ Ioc 0 T, P = A s+∫⁻ r in Ioc 0 s, B r)
    (htop : P = D+∫⁻ r in Ioc 0 T, B r) :
    (∀ s ∈ Ioc 0 T, k*P = k*A s+∫⁻ r in Ioc 0 s, k*B r) ∧
      k*P = k*D+∫⁻ r in Ioc 0 T, k*B r := by
  constructor
  · intro s hs
    rw [hcut s hs,mul_add,lintegral_const_mul' _ _ hk]
  · rw [htop,mul_add,lintegral_const_mul' _ _ hk]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The probability of a flight, a transverse refresh, and a straight final segment -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def terminalBlock (rate : ℝ≥0) (τ : ℝ) : Kernel FlightState FlightState :=
  freeFlightKernel τ ∘ₖ flightKernel rate 1

def driftBlock (rate T : ℝ≥0) (τ : ℝ) : Kernel FlightState FlightState :=
  terminalBlock rate τ ∘ₖ flightKernel rate T

theorem terminalBlock_apply (rate : ℝ≥0) (τ : ℝ) (z : FlightState) :
    terminalBlock rate τ z = (flightKernel rate 1 z).map (freeFlight τ) := by
  rw [terminalBlock,freeFlightKernel,Kernel.deterministic_comp_eq_map,Kernel.map_apply]
  exact freeFlight_measurable.comp (measurable_const.prodMk measurable_id)

theorem driftBlock_lower (rate : ℝ≥0) (hr : 0 < rate) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ (A κ : ℝ) (T : ℝ≥0) (z : FlightState),
      0 < A → 0 < κ → 5 < d*κ*A/4 →
      (1/2 : ℝ≥0∞) ≤ flightKernel rate T z {w | ‖w.1-z.1‖ < d*κ*A/4} →
      c ≤ driftBlock rate T (κ*A) z (blockTarget z.1 A κ d) := by
  obtain ⟨c,hc,hct,hentry⟩ := flight_transverse_entry rate hr (ζ := d/4) (by positivity)
  refine ⟨(1/2)*c,mul_ne_zero (by norm_num) hc,ENNReal.mul_ne_top (by norm_num) hct,?_⟩
  intro A κ T z hA hκ hlarge hsmall
  let S : Set FlightState := {w | ‖w.1-z.1‖ < d*κ*A/4}
  have hS : MeasurableSet S := by dsimp [S]; measurability
  have hlocal (w : FlightState) (hw : w ∈ S) :
      c ≤ terminalBlock rate (κ*A) w (blockTarget z.1 A κ d) := by
    rw [terminalBlock_apply,Measure.map_apply
      (show Measurable (freeFlight (κ*A)) from
        freeFlight_measurable.comp (measurable_const.prodMk measurable_id))
      (blockTarget_measurable z.1 A κ d)]
    apply (hentry w).trans
    apply measure_mono_ae
    filter_upwards [flightKernel_displacement rate 1 w] with y hy
    intro hv
    apply flight_block_geometry hA hκ hd1 hlarge hw
    · simpa using hy
    · exact hv
  rw [driftBlock,Kernel.comp_apply' _ _ _ (blockTarget_measurable z.1 A κ d)]
  calc
    (1/2 : ℝ≥0∞)*c ≤ flightKernel rate T z S*c := mul_le_mul' hsmall le_rfl
    _ = ∫⁻ _w in S, c ∂flightKernel rate T z := by
      rw [lintegral_const,Measure.restrict_apply_univ,mul_comm]
    _ ≤ ∫⁻ w in S, terminalBlock rate (κ*A) w (blockTarget z.1 A κ d)
        ∂flightKernel rate T z := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hS] with w hw
      exact hlocal w hw
    _ ≤ ∫⁻ w, terminalBlock rate (κ*A) w (blockTarget z.1 A κ d)
        ∂flightKernel rate T z := lintegral_mono' Measure.restrict_le_self le_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The reference flight admits any larger damping with positive self-retention -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weightedFlight_changed_damping (L C : ℝ≥0) (hLC : L ≤ C)
    {c : ℝ} (hc : 0 ≤ c) {f : FlightState → ℝ≥0∞} (hf : Measurable f)
    (p : TimeFlightState) (hp : 0 ≤ p.1) :
    weightedFlight L c f p = clockSurvival C p.1*f (finishFlight p) +
      (∫⁻ s in Ioc 0 p.1, clockSurvival C s * ENNReal.ofReal (L:ℝ) *
        ∫⁻ u, weightedFlight L c f (advanceState p s u) ∂uniformizedKernel p.2.2) +
      ∫⁻ s in Ioc 0 p.1, clockSurvival C s * ENNReal.ofReal (c+(C:ℝ)-(L:ℝ)) *
        weightedFlight L c f (p.1-s,freeFlight s p.2) := by
  let δ : ℝ := (C:ℝ)-(L:ℝ)
  let k := growthWeight (-δ) p.1
  let A : ℝ → ℝ≥0∞ := fun s => clockSurvival L s *
    ∫⁻ z, f z ∂flightFamily L (p.1-s,freeFlight s p.2)
  let B : ℝ → ℝ≥0∞ := fun s => clockDensity L s *
    ∫⁻ u, ∫⁻ z, f z ∂flightFamily L (advanceState p s u) ∂uniformizedKernel p.2.2
  have hA : Measurable A := (show Measurable (clockSurvival L) by unfold clockSurvival; fun_prop).mul
    ((hf.lintegral_kernel (κ := flightFamily L)).comp (by unfold freeFlight; fun_prop))
  have hB : Measurable B := by
    have hm : Measurable (fun q : ℝ × RetainedState =>
        ∫⁻ z, f z ∂flightFamily L (advanceState p q.1 q.2)) :=
      (hf.lintegral_kernel (κ := flightFamily L)).comp (by unfold advanceState freeFlight; fun_prop)
    exact (show Measurable (clockDensity L) by unfold clockDensity; fun_prop).mul hm.lintegral_prod_right'
  have hcut (s : ℝ) (hs : s ∈ Ioc 0 p.1) :
      (∫⁻ z, f z ∂flightFamily L p) = A s+∫⁻ r in Ioc 0 s, B r := by
    simpa only [add_sub_cancel,p.eta] using
      flightFamily_time_cut L p.2 hs.1.le (sub_nonneg.mpr hs.2) hf
  have htop : (∫⁻ z, f z ∂flightFamily L p) =
      clockSurvival L p.1*f (finishFlight p)+∫⁻ s in Ioc 0 p.1, B s :=
    flightFamily_first_event L p hf
  have hδ : 0 ≤ δ := sub_nonneg.mpr (show (L:ℝ) ≤ (C:ℝ) from hLC)
  have hcδ : 0 ≤ c+δ := add_nonneg hc hδ
  have hs := time_cut_scale k (show k ≠ ⊤ from ENNReal.ofReal_ne_top) hcut htop
  have H := weighted_time_cut hcδ hp (measurable_const.mul hA) (measurable_const.mul hB) hs.1 hs.2
  have hkclock (s : ℝ) : growthWeight (-δ) s*clockSurvival L s = clockSurvival C s := by
    convert growth_damping_clock L C s using 1
    dsimp [δ]
    congr 1
    ring_nf
  have hw (s : ℝ) : growthWeight (c+δ) (p.1-s)*k*clockSurvival L s =
      clockSurvival C s*growthWeight c (p.1-s) := by
    rw [show k = growthWeight (-δ) p.1 from rfl,growth_damping_split,mul_assoc,hkclock,mul_comm]
  rw [← mul_assoc,growth_damping_cancel] at H
  change weightedFlight L c f p = _ at H
  have hfirst : k*(clockSurvival L p.1*f (finishFlight p)) =
      clockSurvival C p.1*f (finishFlight p) := by
    rw [← mul_assoc,hkclock]
  rw [hfirst] at H
  rw [H]
  congr 1
  · congr 1
    apply lintegral_congr
    intro s
    dsimp only [Pi.mul_apply]
    rw [show growthWeight (c+δ) (p.1-s)*(k*B s) =
      (growthWeight (c+δ) (p.1-s)*k*clockSurvival L s)*ENNReal.ofReal (L:ℝ)*
        ∫⁻ u, ∫⁻ z, f z ∂flightFamily L (advanceState p s u) ∂uniformizedKernel p.2.2 by
          dsimp [B]; rw [clockDensity_eq]; ac_rfl,hw]
    have hg : growthWeight c (p.1-s) ≠ ⊤ := ENNReal.ofReal_ne_top
    rw [show (clockSurvival C s*growthWeight c (p.1-s))*ENNReal.ofReal (L:ℝ) =
      (clockSurvival C s*ENNReal.ofReal (L:ℝ))*growthWeight c (p.1-s) by ac_rfl,mul_assoc,
      ← lintegral_const_mul' _ _ hg]
    rfl
  · apply lintegral_congr
    intro s
    dsimp only [Pi.mul_apply]
    rw [growthDensity_eq hcδ]
    change ENNReal.ofReal (c+δ)*growthWeight (c+δ) (p.1-s)*(k*A s) = _
    rw [show ENNReal.ofReal (c+δ)*growthWeight (c+δ) (p.1-s)*(k*A s) =
      ENNReal.ofReal (c+δ)*(growthWeight (c+δ) (p.1-s)*k*clockSurvival L s)*
        ∫⁻ z, f z ∂flightFamily L (p.1-s,freeFlight s p.2) by dsimp [A]; ac_rfl,hw]
    have hcdef : c+δ = c+(C:ℝ)-(L:ℝ) := by dsimp [δ]; ring
    rw [hcdef]
    unfold weightedFlight
    ac_rfl

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The reference collision kernel at a larger constant damping -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def branchingAt (C : ℝ≥0) : Kernel RetainedState RetainedState :=
  branchingKernel + Kernel.id.withDensity (fun _ _ => ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)))

instance branchingAt_sFinite (C : ℝ≥0) : IsSFiniteKernel (branchingAt C) := by
  have : IsSFiniteKernel (Kernel.id.withDensity
      (fun (_ : RetainedState) (_ : RetainedState) => ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)))) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
  unfold branchingAt
  infer_instance

theorem branchingAt_apply (C : ℝ≥0) (v : RetainedState) :
    branchingAt C v = branchingKernel v +
      ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) • Measure.dirac v := by
  rw [branchingAt,add_apply,Kernel.withDensity_apply _ (by fun_prop),withDensity_const,Kernel.id_apply]

theorem branchingAt_physical {C : ℝ≥0} (hC : referenceClock ≤ C) (v : RetainedState) :
    branchingAt C v = ENNReal.ofReal (stateRate v) • stateKernel v +
      ENNReal.ofReal ((C:ℝ)-stateFrequency v) • Measure.dirac v := by
  have hδ : 0 ≤ (C:ℝ)-(referenceClock:ℝ) := sub_nonneg.mpr hC
  have hf : 0 ≤ 48*Real.pi-stateFrequency v := by
    linarith [(stateFrequency_bounds v).2,Real.pi_pos]
  rw [branchingAt_apply,branchingKernel_apply,add_assoc,← add_smul,← ENNReal.ofReal_add hf hδ]
  congr 2
  congr 1
  change 48*Real.pi-stateFrequency v+((C:ℝ)-48*Real.pi) = (C:ℝ)-stateFrequency v
  ring

theorem branchingAt_lower {C : ℝ≥0} (hC : referenceClock ≤ C) (v : RetainedState) :
    ENNReal.ofReal (referenceClock:ℝ) • uniformizedKernel v +
      ENNReal.ofReal (referenceGrowth+(C:ℝ)-(referenceClock:ℝ)) • Measure.dirac v ≤ branchingAt C v := by
  have hδ : 0 ≤ (C:ℝ)-(referenceClock:ℝ) := sub_nonneg.mpr hC
  have hg : 0 ≤ referenceGrowth := by unfold referenceGrowth; positivity
  have he : referenceGrowth+((C:ℝ)-(referenceClock:ℝ)) =
      referenceGrowth+(C:ℝ)-(referenceClock:ℝ) := by ring
  rw [branchingAt_apply]
  calc
    _ = (ENNReal.ofReal (referenceClock:ℝ) • uniformizedKernel v+
          ENNReal.ofReal referenceGrowth • Measure.dirac v)+
        ENNReal.ofReal ((C:ℝ)-(referenceClock:ℝ)) • Measure.dirac v := by
      rw [add_assoc,← add_smul,← ENNReal.ofReal_add hg hδ,he]
    _ ≤ _ := add_le_add (branchingKernel_lower v) le_rfl

theorem branchingAt_mass_bound {C : ℝ≥0} (hC : referenceClock ≤ C) (v : RetainedState) :
    branchingAt C v univ ≤ ENNReal.ofReal ((C:ℝ)+48*Real.pi) := by
  have hf := (stateFrequency_bounds v).1
  have hr := (stateRate_bounds v).2
  have hr0 : 0 ≤ stateRate v := by linarith [(stateRate_bounds v).1,Real.pi_pos]
  have hfreq : stateFrequency v ≤ (C:ℝ) :=
    (stateFrequency_bounds v).2.trans (by
      have hc : 48*Real.pi ≤ (C:ℝ) := hC
      linarith [Real.pi_pos])
  rw [branchingAt_physical hC,Measure.add_apply,Measure.smul_apply,Measure.smul_apply,
    measure_univ,Measure.dirac_apply_of_mem (Set.mem_univ v),smul_eq_mul,smul_eq_mul,mul_one,mul_one,
    ← ENNReal.ofReal_add hr0 (sub_nonneg.mpr hfreq)]
  apply ENNReal.ofReal_le_ofReal
  linarith [Real.pi_pos]

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The growing reference flight is dominated by histories at any larger damping -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weightedFlight_damped_subsolution {C : ℝ≥0} (hC : referenceClock ≤ C)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f)
    (p : TimeFlightState) (hp : 0 ≤ p.1) :
    weightedFlight referenceClock referenceGrowth f p ≤ flightSeed C f p +
      ∫⁻ q, weightedFlight referenceClock referenceGrowth f q ∂eventStep C (branchingAt C) p := by
  let F := weightedFlight referenceClock referenceGrowth f
  have hF : Measurable F := weightedFlight_measurable _ _ hf
  have hgain : Measurable (fun s : ℝ => clockSurvival C s * ENNReal.ofReal (referenceClock:ℝ) *
      ∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2) := by
    have hm : Measurable (fun q : ℝ × RetainedState => F (advanceState p q.1 q.2)) :=
      hF.comp (by unfold advanceState freeFlight; fun_prop)
    exact (show Measurable (fun s => clockSurvival C s * ENNReal.ofReal (referenceClock:ℝ)) by
      unfold clockSurvival; fun_prop).mul hm.lintegral_prod_right'
  rw [weightedFlight_changed_damping referenceClock C hC (by unfold referenceGrowth; positivity) hf p hp,
    eventStep_lintegral _ _ _ hF]
  change flightSeed C f p+_+_ ≤ flightSeed C f p+_
  rw [add_assoc,← lintegral_add_left hgain]
  apply add_le_add le_rfl
  apply lintegral_mono
  intro s
  have hi := lintegral_mono' (branchingAt_lower hC p.2.2)
    (f := fun u => F (advanceState p s u)) le_rfl
  rw [lintegral_add_measure,lintegral_smul_measure,lintegral_smul_measure,
    lintegral_dirac,smul_eq_mul,smul_eq_mul] at hi
  change clockSurvival C s * ENNReal.ofReal (referenceClock:ℝ) *
      (∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2) +
      clockSurvival C s * ENNReal.ofReal (referenceGrowth+(C:ℝ)-(referenceClock:ℝ)) *
        F (advanceState p s p.2.2) ≤ _
  calc
    _ = clockSurvival C s * (ENNReal.ofReal (referenceClock:ℝ) *
      (∫⁻ u, F (advanceState p s u) ∂uniformizedKernel p.2.2) +
      ENNReal.ofReal (referenceGrowth+(C:ℝ)-(referenceClock:ℝ))*F (advanceState p s p.2.2)) := by
        ring
    _ ≤ _ := mul_le_mul' le_rfl hi

theorem weightedFlight_le_damped_series {C : ℝ≥0} (hC : referenceClock ≤ C)
    {f : FlightState → ℝ≥0∞} (hf : Measurable f) (hb : ∀ z, f z ≤ 1)
    (p : TimeFlightState) (hp : 0 ≤ p.1) :
    weightedFlight referenceClock referenceGrowth f p ≤
      ∑' n, eventHistory C (branchingAt C) (flightSeed C f) n p := by
  apply event_subsolution_le_series C (branchingAt C)
    (C := (C:ℝ)+48*Real.pi) (M := Real.exp (referenceGrowth*p.1)) (T := p.1)
    (by positivity) (Real.exp_pos _).le (branchingAt_mass_bound hC)
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
    exact weightedFlight_damped_subsolution hC hf q hq.1
  · exact ⟨hp,le_rfl⟩

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A uniform positive displacement block at every sufficiently large duration -/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

def blockFirstTime (A κ : ℝ) : ℝ≥0 := Real.toNNReal ((1-κ)*A-1)

theorem large_driftBlock_lower (rate : ℝ≥0) (hr : 0 < rate) {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A₀ : ℝ) (c : ℝ≥0∞), 0 < A₀ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
      ∀ A : ℝ, A₀ ≤ A → ∀ z : FlightState,
        c ≤ driftBlock rate (blockFirstTime A κ) (κ*A) z (blockTarget z.1 A κ d) := by
  obtain ⟨T₀,hT₀,hsmall⟩ := flight_small_displacement rate hr (a := d*κ/4) (by positivity)
  obtain ⟨c,hc,hct,hblock⟩ := driftBlock_lower rate hr hd hd1
  let A₀ := max ((T₀+1)/(1-κ)) (20/(d*κ)+1)
  have hpos : 0 < 20/(d*κ)+1 := by positivity
  have hA₀ : 0 < A₀ := hpos.trans_le (le_max_right _ _)
  refine ⟨A₀,c,hA₀,hc,hct,?_⟩
  intro A hA z
  have hApos : 0 < A := hA₀.trans_le hA
  have htime : T₀ ≤ (1-κ)*A-1 := by
    have hh := (div_le_iff₀ (by linarith : 0 < 1-κ)).mp ((le_max_left _ _).trans hA)
    linarith
  have htime0 : 0 ≤ (1-κ)*A-1 := hT₀.le.trans htime
  have htime_coe : (blockFirstTime A κ : ℝ) = (1-κ)*A-1 := by
    exact Real.coe_toNNReal _ htime0
  have htimeA : (blockFirstTime A κ : ℝ) ≤ A := by
    rw [htime_coe]
    nlinarith [mul_pos hκ hApos]
  have hlarge : 5 < d*κ*A/4 := by
    have hh : 20/(d*κ)+1 ≤ A := (le_max_right _ _).trans hA
    have hi : 20/(d*κ) < A := by linarith
    have hj := (div_lt_iff₀ (mul_pos hd hκ)).mp hi
    nlinarith
  apply hblock A κ (blockFirstTime A κ) z hApos hκ hlarge
  apply (hsmall (blockFirstTime A κ) (by rwa [htime_coe]) z).trans
  apply measure_mono
  intro w hw
  change ‖w.1-z.1‖ < d*κ*A/4
  apply lt_of_lt_of_le hw
  have hh := mul_le_mul_of_nonneg_left htimeA (by positivity : 0 ≤ d*κ/4)
  nlinarith

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Positive potential overcomes the cost of the final straight segment -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weighted_driftBlock_growth (rate : ℝ≥0) (hr : 0 < rate) {d κ g : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (rate : ℝ)*κ < g) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ z : FlightState,
      (8 : ℝ≥0∞) < ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A)) *
        driftBlock rate (blockFirstTime A κ) (κ*A) z (blockTarget z.1 A κ d) := by
  obtain ⟨a,c,ha,hc,hct,hblock⟩ := large_driftBlock_lower rate hr hd hd1 hκ hκ1
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc hct
  have he : 0 < g-(rate : ℝ)*κ := sub_pos.mpr hg
  let A₀ := max a (Real.log (9/c.toReal)/(g-(rate : ℝ)*κ))
  refine ⟨A₀,ha.trans_le (le_max_left _ _),?_⟩
  intro A hA z
  have haA : a ≤ A := (le_max_left _ _).trans hA
  have hexp : 9/c.toReal ≤ Real.exp ((g-(rate : ℝ)*κ)*A) := by
    have hlog := (div_le_iff₀ he).mp ((le_max_right _ _).trans hA)
    calc
      9/c.toReal = Real.exp (Real.log (9/c.toReal)) := (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hnine : 9 ≤ Real.exp ((g-(rate : ℝ)*κ)*A)*c.toReal := by
    have hh := mul_le_mul_of_nonneg_right hexp hcpos.le
    rwa [div_mul_cancel₀ _ hcpos.ne'] at hh
  calc
    (8 : ℝ≥0∞) < 9 := by norm_num
    _ ≤ ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A)*c.toReal) := by
      simpa using ENNReal.ofReal_le_ofReal hnine
    _ = ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A))*c := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le,ENNReal.ofReal_toReal hct]
    _ ≤ _ := mul_le_mul' le_rfl (hblock A haA z)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # The constructed drift block occurs inside the full reference flight law -/

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem flightKernel_free_lower (rate T : ℝ≥0) (z : FlightState) :
    clockSurvival rate T • freeFlightKernel T z ≤ flightKernel rate T z := by
  apply Measure.le_iff.mpr
  intro A hA
  have hf : Measurable (A.indicator (1 : FlightState → ℝ≥0∞)) := measurable_const.indicator hA
  have h := flightFamily_first_event rate ((T : ℝ),z) hf
  rw [flightFamily_eq,lintegral_indicator_one hA] at h
  rw [Measure.smul_apply,smul_eq_mul,freeFlightKernel,Kernel.deterministic_apply,
    Measure.dirac_apply' _ hA]
  rw [h]
  change clockSurvival rate T * A.indicator 1 (finishFlight ((T : ℝ),z)) ≤ _
  exact le_add_right le_rfl

theorem driftBlock_le_flight (rate T τ : ℝ≥0) (z : FlightState) {A : Set FlightState}
    (hA : MeasurableSet A) :
    clockSurvival rate τ * driftBlock rate T τ z A ≤ flightKernel rate (T+1+τ) z A := by
  rw [driftBlock,terminalBlock,Kernel.comp_assoc,← flightKernel_add,
    Kernel.comp_apply' _ _ _ hA,flightKernel_add rate (T+1) τ,Kernel.comp_apply' _ _ _ hA,
    ← lintegral_const_mul' _ _ (show clockSurvival rate τ ≠ ⊤ from ENNReal.ofReal_ne_top)]
  apply lintegral_mono
  intro w
  exact flightKernel_free_lower rate τ w A

theorem blockFirstTime_sum {A κ : ℝ} (h : 0 ≤ (1-κ)*A-1) (hκA : 0 ≤ κ*A) :
    (blockFirstTime A κ : ℝ) + 1 + (Real.toNNReal (κ*A) : ℝ) = A := by
  rw [blockFirstTime,Real.coe_toNNReal _ h,Real.coe_toNNReal _ hκA]
  ring

theorem full_flight_block_growth (rate : ℝ≥0) (hr : 0 < rate) {d κ g : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (rate : ℝ)*κ < g) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∀ z : FlightState,
      (8 : ℝ≥0∞) < growthWeight g A *
        flightKernel rate (Real.toNNReal A) z (blockTarget z.1 A κ d) := by
  obtain ⟨a,ha,hgrowth⟩ := weighted_driftBlock_growth rate hr hd hd1 hκ hκ1 hg
  let A₀ := max a (1/(1-κ))
  refine ⟨A₀,ha.trans_le (le_max_left _ _),?_⟩
  intro A hA z
  have hAA : 0 < A := ha.trans_le ((le_max_left _ _).trans hA)
  have hκA : 0 ≤ κ*A := (mul_pos hκ hAA).le
  have htime : 0 ≤ (1-κ)*A-1 := by
    have hh := (div_le_iff₀ (by linarith : 0 < 1-κ)).mp ((le_max_right _ _).trans hA)
    linarith
  have hsum : blockFirstTime A κ+1+Real.toNNReal (κ*A) = Real.toNNReal A := by
    apply NNReal.eq
    simp only [NNReal.coe_add,NNReal.coe_one,Real.coe_toNNReal _ hAA.le]
    exact blockFirstTime_sum htime hκA
  have hlow := driftBlock_le_flight rate (blockFirstTime A κ) (Real.toNNReal (κ*A)) z
    (blockTarget_measurable z.1 A κ d)
  rw [hsum,Real.coe_toNNReal _ hκA] at hlow
  have he : ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A)) =
      growthWeight g A * clockSurvival rate (κ*A) := by
    rw [growthWeight,clockSurvival,← ENNReal.ofReal_mul (by positivity),← Real.exp_add]
    congr 2
    ring
  calc
    (8 : ℝ≥0∞) < ENNReal.ofReal (Real.exp ((g-(rate : ℝ)*κ)*A)) *
        driftBlock rate (blockFirstTime A κ) (κ*A) z (blockTarget z.1 A κ d) :=
      hgrowth A ((le_max_left _ _).trans hA) z
    _ = growthWeight g A * (clockSurvival rate (κ*A)*
        driftBlock rate (blockFirstTime A κ) (κ*A) z (blockTarget z.1 A κ d)) := by rw [he,mul_assoc]
    _ ≤ _ := mul_le_mul' le_rfl hlow

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A uniformly finite positive-history block with transverse displacement -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem weightedFlight_indicator (rate : ℝ≥0) (c : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (z : FlightState) {A : Set FlightState} (hA : MeasurableSet A) :
    weightedFlight rate c (A.indicator 1) (T,z) =
      growthWeight c T * flightKernel rate (Real.toNNReal T) z A := by
  have he : flightFamily rate (T,z) = flightKernel rate (Real.toNNReal T) z := by
    simpa only [Real.coe_toNNReal _ hT] using flightFamily_eq rate (Real.toNNReal T) z
  rw [weightedFlight,he,lintegral_indicator_one hA]

theorem weightedFlight_window_bound {f : FlightState → ℝ≥0∞} (hb : ∀ z, f z ≤ 1)
    {T : ℝ} (p : TimeFlightState) (hp : p.1 ∈ Icc 0 T) :
    weightedFlight referenceClock referenceGrowth f p ≤ ENNReal.ofReal (Real.exp (referenceGrowth*T)) := by
  calc
    _ ≤ growthWeight referenceGrowth p.1*1 :=
      mul_le_mul' le_rfl (flightFamily_average_bound _ p hp.1 hb)
    _ ≤ _ := by
      rw [mul_one]
      apply ENNReal.ofReal_le_ofReal
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp.2 (by unfold referenceGrowth; positivity))

theorem branching_remainder_uniform {T : ℝ} {f : FlightState → ℝ≥0∞}
    (hb : ∀ z, f z ≤ 1) (n : ℕ) (z : FlightState) (hT : 0 ≤ T) :
    (∫⁻ q, weightedFlight referenceClock referenceGrowth f q
      ∂((eventStep referenceClock branchingKernel)^n) (T,z)) ≤
      ENNReal.ofReal (Real.exp (referenceGrowth*T)*((96*Real.pi*T)^n/(n.factorial : ℝ))) := by
  calc
    _ ≤ ∫⁻ _q, ENNReal.ofReal (Real.exp (referenceGrowth*T))
        ∂((eventStep referenceClock branchingKernel)^n) (T,z) := by
      apply lintegral_mono_ae
      filter_upwards [eventStep_power_time_support referenceClock branchingKernel n (T,z) hT] with q hq
      exact weightedFlight_window_bound hb q hq
    _ = ENNReal.ofReal (Real.exp (referenceGrowth*T))*
        ((eventStep referenceClock branchingKernel)^n) (T,z) univ := lintegral_const _
    _ ≤ ENNReal.ofReal (Real.exp (referenceGrowth*T))*
        (ENNReal.ofReal (96*Real.pi)^n*simplexTime n T) :=
      mul_le_mul' le_rfl (eventStep_power_mass_bound referenceClock branchingKernel
        (by positivity) branchingKernel_mass_bound n (T,z) hT)
    _ = _ := by
      rw [simplexTime,← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),mul_pow]
      congr 1
      ring

theorem finite_branching_block_growth {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ A : ℝ, A₀ ≤ A → ∃ N : ℕ, ∀ z : FlightState,
      (7 : ℝ≥0∞) < ∑ j ∈ Finset.range N,
        eventHistory referenceClock branchingKernel
          (flightSeed referenceClock ((blockTarget z.1 A κ d).indicator 1)) j (A,z) := by
  have hr : 0 < referenceClock := by
    change (0 : ℝ) < 48*Real.pi
    positivity
  obtain ⟨A₀,hA₀,hgrowth⟩ := full_flight_block_growth referenceClock hr
    hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro A hA
  have hApos : 0 < A := hA₀.trans_le hA
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (referenceGrowth*A)*((96*Real.pi*A)^n/(n.factorial : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((FloorSemiring.tendsto_pow_div_factorial_atTop (96*Real.pi*A)).const_mul
          (Real.exp (referenceGrowth*A)))
  obtain ⟨N,hN⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ≥0∞) < 1))).exists
  refine ⟨N,?_⟩
  intro z
  let f : FlightState → ℝ≥0∞ := (blockTarget z.1 A κ d).indicator 1
  have hf : Measurable f := measurable_const.indicator (blockTarget_measurable z.1 A κ d)
  have hb (w : FlightState) : f w ≤ 1 := by
    dsimp [f]
    by_cases h : w ∈ blockTarget z.1 A κ d <;> simp [h]
  have hlower : (8 : ℝ≥0∞) < weightedFlight referenceClock referenceGrowth f (A,z) := by
    rw [weightedFlight_indicator _ _ hApos.le z (blockTarget_measurable z.1 A κ d)]
    exact hgrowth A hA z
  have hexpand := event_finite_expansion referenceClock branchingKernel
    (weightedFlight_measurable _ _ hf) (flightSeed_measurable _ hf)
    (fun q hq => weightedFlight_branching_subsolution hf q hq.1) N (A,z) ⟨hApos.le,le_rfl⟩
  have hrem := (branching_remainder_uniform hb N z hApos.le).trans hN.le
  by_contra hn
  have hsum : (∑ j ∈ Finset.range N, eventHistory referenceClock branchingKernel
      (flightSeed referenceClock f) j (A,z)) ≤ 7 := le_of_not_gt hn
  have hh := hexpand.trans (add_le_add hsum hrem)
  norm_num at hh
  exact (not_lt_of_ge hh) hlower

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Finite growing reference blocks with uniform larger damping -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem damped_branching_remainder {C : ℝ≥0} (hC : referenceClock ≤ C)
    {A : ℝ} {f : FlightState → ℝ≥0∞} (hb : ∀ z, f z ≤ 1)
    (n : ℕ) (z : FlightState) (hA : 0 ≤ A) :
    (∫⁻ q, weightedFlight referenceClock referenceGrowth f q
      ∂((eventStep C (branchingAt C))^n) (A,z)) ≤
      ENNReal.ofReal (Real.exp (referenceGrowth*A)*
        (((C:ℝ)+48*Real.pi)*A)^n/(n.factorial : ℝ)) := by
  calc
    _ ≤ ∫⁻ _q, ENNReal.ofReal (Real.exp (referenceGrowth*A))
        ∂((eventStep C (branchingAt C))^n) (A,z) := by
      apply lintegral_mono_ae
      filter_upwards [eventStep_power_time_support C (branchingAt C) n (A,z) hA] with q hq
      exact weightedFlight_window_bound hb q hq
    _ = ENNReal.ofReal (Real.exp (referenceGrowth*A))*
        ((eventStep C (branchingAt C))^n) (A,z) univ := lintegral_const _
    _ ≤ ENNReal.ofReal (Real.exp (referenceGrowth*A))*
        (ENNReal.ofReal ((C:ℝ)+48*Real.pi)^n*simplexTime n A) :=
      mul_le_mul' le_rfl (eventStep_power_mass_bound C (branchingAt C)
        (by positivity) (branchingAt_mass_bound hC) n (A,z) hA)
    _ = _ := by
      rw [simplexTime,← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),mul_pow]
      congr 1
      ring

theorem damped_branching_remainder_on_window {C Cmax : ℝ≥0}
    (hC : referenceClock ≤ C) (hCmax : C ≤ Cmax) {A T : ℝ}
    (hA : 0 ≤ A) (hAT : A ≤ T) {f : FlightState → ℝ≥0∞}
    (hb : ∀ z, f z ≤ 1) (n : ℕ) (z : FlightState) :
    (∫⁻ q, weightedFlight referenceClock referenceGrowth f q
      ∂((eventStep C (branchingAt C))^n) (A,z)) ≤
      ENNReal.ofReal (Real.exp (referenceGrowth*T)*
        (((Cmax:ℝ)+48*Real.pi)*T)^n/(n.factorial : ℝ)) := by
  apply (damped_branching_remainder hC hb n z hA).trans
  apply ENNReal.ofReal_le_ofReal
  have hg : 0 ≤ referenceGrowth := by unfold referenceGrowth; positivity
  have hCC : (C:ℝ) ≤ (Cmax:ℝ) := hCmax
  gcongr

theorem uniform_damped_finite_block_growth {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∀ Cmax : ℝ≥0, ∃ N : ℕ,
      ∀ C : ℝ≥0, referenceClock ≤ C → C ≤ Cmax →
      ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
        (7 : ℝ≥0∞) < ∑ j ∈ Finset.range N,
          eventHistory C (branchingAt C)
            (flightSeed C ((blockTarget z.1 A κ d).indicator 1)) j (A,z) := by
  have hr : 0 < referenceClock := by
    change (0 : ℝ) < 48*Real.pi
    positivity
  obtain ⟨A₀,hA₀,hgrowth⟩ := full_flight_block_growth referenceClock hr hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T _hT Cmax
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (referenceGrowth*T)*(((Cmax:ℝ)+48*Real.pi)*T)^n/(n.factorial : ℝ)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero,mul_div_assoc] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((FloorSemiring.tendsto_pow_div_factorial_atTop (((Cmax:ℝ)+48*Real.pi)*T)).const_mul
          (Real.exp (referenceGrowth*T)))
  obtain ⟨N,hN⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ≥0∞) < 1))).exists
  refine ⟨N,?_⟩
  intro C hC hCmax A hA z
  have hApos : 0 < A := hA₀.trans_le hA.1
  let f : FlightState → ℝ≥0∞ := (blockTarget z.1 A κ d).indicator 1
  have hf : Measurable f := measurable_const.indicator (blockTarget_measurable z.1 A κ d)
  have hb (w : FlightState) : f w ≤ 1 := by
    dsimp [f]
    by_cases h : w ∈ blockTarget z.1 A κ d <;> simp [h]
  have hlower : (8 : ℝ≥0∞) < weightedFlight referenceClock referenceGrowth f (A,z) := by
    rw [weightedFlight_indicator _ _ hApos.le z (blockTarget_measurable z.1 A κ d)]
    exact hgrowth A hA.1 z
  have hexpand := event_finite_expansion C (branchingAt C)
    (weightedFlight_measurable _ _ hf) (flightSeed_measurable _ hf)
    (T := A) (fun q hq => weightedFlight_damped_subsolution hC hf q hq.1)
    N (A,z) ⟨hApos.le,le_rfl⟩
  have hrem := (damped_branching_remainder_on_window hC hCmax hApos.le hA.2 hb N z).trans hN.le
  by_contra hn
  have hsum : (∑ j ∈ Finset.range N, eventHistory C (branchingAt C)
      (flightSeed C f) j (A,z)) ≤ 7 := le_of_not_gt hn
  have hh := hexpand.trans (add_le_add hsum hrem)
  norm_num at hh
  exact (not_lt_of_ge hh) hlower

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # A common collision-depth cutoff on the compact interval of block durations -/

noncomputable section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal NNReal ProbabilityTheory Topology

namespace BoltzmannNonuniqueness.ReferenceGeometry

theorem branching_remainder_on_window {A T : ℝ} (hA : 0 ≤ A) (hAT : A ≤ T)
    {f : FlightState → ℝ≥0∞} (hb : ∀ z, f z ≤ 1) (n : ℕ) (z : FlightState) :
    (∫⁻ q, weightedFlight referenceClock referenceGrowth f q
      ∂((eventStep referenceClock branchingKernel)^n) (A,z)) ≤
      ENNReal.ofReal (Real.exp (referenceGrowth*T)*((96*Real.pi*T)^n/(n.factorial : ℝ))) := by
  apply (branching_remainder_uniform hb n z hA).trans
  apply ENNReal.ofReal_le_ofReal
  have hg : 0 ≤ referenceGrowth := by unfold referenceGrowth; positivity
  gcongr

theorem uniform_finite_branching_block_growth {d κ : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : (referenceClock : ℝ)*κ < referenceGrowth) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ T : ℝ, A₀ ≤ T → ∃ N : ℕ,
      ∀ A ∈ Icc A₀ T, ∀ z : FlightState,
        (7 : ℝ≥0∞) < ∑ j ∈ Finset.range N,
          eventHistory referenceClock branchingKernel
            (flightSeed referenceClock ((blockTarget z.1 A κ d).indicator 1)) j (A,z) := by
  have hr : 0 < referenceClock := by
    change (0 : ℝ) < 48*Real.pi
    positivity
  obtain ⟨A₀,hA₀,hgrowth⟩ := full_flight_block_growth referenceClock hr hd hd1 hκ hκ1 hg
  refine ⟨A₀,hA₀,?_⟩
  intro T _hT
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (referenceGrowth*T)*((96*Real.pi*T)^n/(n.factorial : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((FloorSemiring.tendsto_pow_div_factorial_atTop (96*Real.pi*T)).const_mul
          (Real.exp (referenceGrowth*T)))
  obtain ⟨N,hN⟩ := (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ≥0∞) < 1))).exists
  refine ⟨N,?_⟩
  intro A hA z
  have hApos : 0 < A := hA₀.trans_le hA.1
  let f : FlightState → ℝ≥0∞ := (blockTarget z.1 A κ d).indicator 1
  have hf : Measurable f := measurable_const.indicator (blockTarget_measurable z.1 A κ d)
  have hb (w : FlightState) : f w ≤ 1 := by
    dsimp [f]
    by_cases h : w ∈ blockTarget z.1 A κ d <;> simp [h]
  have hlower : (8 : ℝ≥0∞) < weightedFlight referenceClock referenceGrowth f (A,z) := by
    rw [weightedFlight_indicator _ _ hApos.le z (blockTarget_measurable z.1 A κ d)]
    exact hgrowth A hA.1 z
  have hexpand := event_finite_expansion referenceClock branchingKernel
    (weightedFlight_measurable _ _ hf) (flightSeed_measurable _ hf)
    (T := A) (fun q hq => weightedFlight_branching_subsolution hf q hq.1) N (A,z) ⟨hApos.le,le_rfl⟩
  have hrem := (branching_remainder_on_window hApos.le hA.2 hb N z).trans hN.le
  by_contra hn
  have hsum : (∑ j ∈ Finset.range N, eventHistory referenceClock branchingKernel
      (flightSeed referenceClock f) j (A,z)) ≤ 7 := le_of_not_gt hn
  have hh := hexpand.trans (add_le_add hsum hrem)
  norm_num at hh
  exact (not_lt_of_ge hh) hlower

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

section

/-! # Strict endpoint margins survive finite-path perturbations -/

noncomputable section

namespace BoltzmannNonuniqueness.ReferenceGeometry

def physicalBlockTarget (x : V) (A κ d : ℝ) : Set (V × V) :=
  {w | ‖w.1-(x+(κ*A) • firstAxis)‖ < d*κ*A ∧ ‖w.2‖ < 5}

theorem block_target_perturb {x : V} {A κ d : ℝ} {r : FlightState} {w : V × V}
    (hr : r ∈ blockTarget x A κ d)
    (hx : ‖w.1-r.1‖ ≤ d*κ*A/4) (hv : ‖w.2-(r.2 : V)‖ ≤ 1) :
    w ∈ physicalBlockTarget x A κ d := by
  constructor
  · have hh := norm_sub_le_norm_sub_add_norm_sub w.1 r.1 (x+(κ*A) • firstAxis)
    have hgood := hr.1
    linarith
  · have hh := norm_add_le (w.2-(r.2 : V)) (r.2 : V)
    rw [sub_add_cancel] at hh
    have hgood := hr.2
    linarith

theorem finite_position_error_of_total {x : V} {t : ℕ → ℝ} {v u : ℕ → V}
    {n : ℕ} {A B : ℝ} (hB : 0 ≤ B) (ht : ∀ j < n, 0 ≤ t j)
    (hv : ∀ j < n, ‖v j-u j‖ ≤ B) (hA : (∑ j ∈ Finset.range n, t j) ≤ A) :
    ‖finitePosition x t v n-finitePosition x t u n‖ ≤ A*B := by
  have hh := finite_position_error (x := x) (y := x) ht hv
  simp only [sub_self,norm_zero,zero_add] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hA hB)

end BoltzmannNonuniqueness.ReferenceGeometry

end

end

end OAI
