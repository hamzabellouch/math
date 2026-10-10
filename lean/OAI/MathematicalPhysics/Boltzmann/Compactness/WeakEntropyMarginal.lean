import OAI.MathematicalPhysics.Boltzmann.Approximation.MildCurveContinuity
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.CumulativeIntervalBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseSourceMeasure
import OAI.MathematicalPhysics.Boltzmann.Branching.ProjectedTimeBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.RelativeEntropyMarginal
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyRegularizationLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeLocalization

namespace OAI

section

/-! # Relative entropy bounds pass to weak L¹ limits -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem WeakL1Converges.entropy_bound {f : ℕ → X → ℝ} {g m : X → ℝ}
    (h : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n) (hgn : 0 ≤ᵐ[μ] g)
    (hmm : Measurable m) (hmi : Integrable m μ) (hmp : ∀ᵐ x ∂μ, 0 < m x)
    (hHi : ∀ n, Integrable (fun x => scalarRelativeEntropy (m x) (f n x)) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hH : ∀ᶠ n in atTop, (∫ x, scalarRelativeEntropy (m x) (f n x) ∂μ) ≤ C) :
    Integrable (fun x => scalarRelativeEntropy (m x) (g x)) μ ∧
      (∫ x, scalarRelativeEntropy (m x) (g x) ∂μ) ≤ C := by
  let ψ : ℕ → X → ℝ := fun n x => boundedEntropyTest n (m x) (g x)
  let d : ℕ → X → ℝ := fun n x => entropyDual (m x) (g x) (ψ n x)
  have hψm n : Measurable (ψ n) := measurable_boundedEntropyTest n hmm h.1
  have hψb n x : |ψ n x| ≤ (n:ℝ) := boundedEntropyTest_bound n (m x) (g x)
  have hdi n : Integrable (d n) μ := integrable_entropyDual hmi h.2.1 (hψm n) (hψb n)
  have hdm n : Measurable (d n) := measurable_entropyDual hmm h.1 (hψm n)
  have hdn n : 0 ≤ᵐ[μ] d n := by
    filter_upwards [hmp,hgn] with x hmx hgx
    exact entropyDual_boundedEntropyTest_nonneg n hmx hgx
  have hdB n : (∫ x, d n x ∂μ) ≤ C := by
    have hcorr := hmi.bdd_mul ((hψm n).exp.sub measurable_const).aestronglyMeasurable
      (ae_of_all μ (fun x => show |Real.exp (ψ n x)-1| ≤ Real.exp (n:ℝ)+1 from by
        calc
          _ ≤ |Real.exp (ψ n x)|+|1| := abs_sub _ _
          _ = Real.exp (ψ n x)+1 := by rw [abs_of_pos (Real.exp_pos _),abs_one]
          _ ≤ _ := add_le_add (Real.exp_le_exp.mpr ((le_abs_self _).trans (hψb n x))) le_rfl))
    have hdki k := integrable_entropyDual hmi (hfi k) (hψm n) (hψb n)
    have he (u : X → ℝ) (hui : Integrable u μ) :
        (∫ x, entropyDual (m x) (u x) (ψ n x) ∂μ) =
          (∫ x, ψ n x*u x ∂μ)-(∫ x, (Real.exp (ψ n x)-1)*m x ∂μ) := by
      simpa only [entropyDual,mul_comm,Pi.sub_def,Pi.mul_def] using integral_sub
        (hui.bdd_mul (hψm n).aestronglyMeasurable (ae_of_all μ (hψb n))) hcorr
    have ht : Tendsto (fun k => ∫ x, entropyDual (m x) (f k x) (ψ n x) ∂μ)
        atTop (𝓝 (∫ x, d n x ∂μ)) := by
      simp only [he _ (hfi _),show (∫ x, d n x ∂μ) = _ from he g h.2.1]
      exact (h.2.2 (ψ n) (hψm n) ⟨n,hψb n⟩).sub_const _
    apply le_of_tendsto ht
    filter_upwards [hH] with k hk
    refine (integral_mono_ae (hdki k) (hHi k) ?_).trans hk
    filter_upwards [hmp,hfn k] with x hmx hfx
    exact entropyDual_le hmx hfx _
  have hHm : Measurable (fun x => scalarRelativeEntropy (m x) (g x)) :=
    ((h.1.mul h.1.log).sub (h.1.mul (measurable_const.add hmm.log))).add hmm
  have hHn : 0 ≤ᵐ[μ] (fun x => scalarRelativeEntropy (m x) (g x)) := by
    filter_upwards [hmp,hgn] with x hmx hgx
    exact scalarRelativeEntropy_nonneg hmx hgx
  have hfatou : (∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (g x)) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (d n x) ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (d n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hmp,hgn] with x hmx hgx
        exact (ENNReal.tendsto_ofReal (entropyDual_boundedEntropyTest_tendsto hmx hgx)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (fun n => (hdm n).ennreal_ofReal)
  have hbound : (∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (g x)) ∂μ) ≤
      ENNReal.ofReal C := by
    refine hfatou.trans (liminf_le_of_frequently_le ?_)
    exact (Eventually.of_forall (fun n => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hdi n) (hdn n)]
      exact ENNReal.ofReal_le_ofReal (hdB n))).frequently
  have hgi : Integrable (fun x => scalarRelativeEntropy (m x) (g x)) μ :=
    ⟨hHm.aestronglyMeasurable,(hasFiniteIntegral_iff_ofReal hHn).mpr
      (hbound.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hgi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hgi hHn] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hbound

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Every-time weak convergence of actual characteristic solutions -/

noncomputable section

open MeasureTheory Filter

namespace BoltzmannNonuniqueness.TorusFlight

theorem weak_eulerianProfile {μ : Measure ℝ} [IsFiniteMeasure μ]
    {r : ℕ → ℝ × Phase → ℝ} {R : ℝ × Phase → ℝ}
    {a : ℕ → Density} {a₀ : Density}
    (ha : Published.WeakL1Converges volume a a₀)
    (ham : ∀ n, Measurable (a n)) (hai : ∀ n, Integrable (a n))
    (hr : Published.WeakL1Converges (μ.prod volume) r R)
    (hrm : ∀ n, Measurable (r n)) (hri : ∀ n, Integrable (r n) (μ.prod volume)) (t : ℝ) :
    Published.WeakL1Converges volume (fun n => eulerianProfile μ (a n) (r n) t)
      (eulerianProfile μ a₀ R t) := by
  have hp := ha.mild_slice hai hr hrm hri t
  have hm n : Measurable (characteristicProfile μ (a n) (r n) t) :=
    (ham n).add ((Published.timePrimitive_measurable μ (hrm n)).comp
      (measurable_const.prodMk measurable_id))
  apply Published.WeakL1Converges.of_comp_measurePreserving (flight_measurePreserving t)
    (fun n => (hm n).comp (flight_measurePreserving (-t)).measurable)
    (hp.1.comp (flight_measurePreserving (-t)).measurable)
  simpa only [eulerianProfile,characteristicProfile,Function.comp_def,flight_neg] using hp

theorem weak_of_characteristic_slice {μ : Measure ℝ} [IsFiniteMeasure μ]
    {r : ℕ → ℝ × Phase → ℝ} {R : ℝ × Phase → ℝ}
    {a : ℕ → Density} {a₀ : Density} {u : ℕ → Density}
    (ha : Published.WeakL1Converges volume a a₀) (hai : ∀ n, Integrable (a n))
    (hr : Published.WeakL1Converges (μ.prod volume) r R)
    (hrm : ∀ n, Measurable (r n)) (hri : ∀ n, Integrable (r n) (μ.prod volume))
    (t : ℝ) (hum : ∀ n, Measurable (u n))
    (he : ∀ n, (fun p => u n (flight t p)) =ᵐ[volume]
      characteristicProfile μ (a n) (r n) t) :
    Published.WeakL1Converges volume u (eulerianProfile μ a₀ R t) := by
  have hp := ha.mild_slice hai hr hrm hri t
  have hh := hp.congr_sequence (fun n => (he n).symm)
  apply Published.WeakL1Converges.of_comp_measurePreserving (flight_measurePreserving t) hum
    (hp.1.comp (flight_measurePreserving (-t)).measurable)
  simpa only [eulerianProfile,characteristicProfile,Function.comp_def,flight_neg] using hh

end BoltzmannNonuniqueness.TorusFlight

end

end

section

/-! # A common almost-everywhere measure balance from smooth weak tests -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.Compactness

namespace BoltzmannNonuniqueness.WeakTime

theorem ae_measure_interval_balance {a b : ℝ} (hab : a < b)
    {F : ℝ × Phase → ℝ} (hi : Integrable F (volume : Measure (ℝ × Phase)))
    (hn : ∀ᵐ z ∂volume, 0 ≤ F z)
    (μ ν : Measure (ℝ × Phase)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hw : ∀ φ : Phase → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∀ p, 0 ≤ φ p) → ∀ θ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ →
      HasCompactSupport θ → tsupport θ ⊆ Ioo a b →
      (∫ z, (deriv θ z.1*φ z.2)*F z)+
        (∫ z, θ z.1*φ z.2 ∂μ)-(∫ z, θ z.1*φ z.2 ∂ν) = 0) :
    ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseSlice F t+phaseIncrement ν s t = phaseSlice F s+phaseIncrement μ s t := by
  have hscalar (j : ℕ) : ∀ᵐ s ∂volume, ∀ᵐ t ∂volume,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseProjection F (positivePhaseTest j) t+
        (timeSource ν (positivePhaseTest j)).real (Ioc s t) =
      phaseProjection F (positivePhaseTest j) s+
        (timeSource μ (positivePhaseTest j)).real (Ioc s t) := by
    have hj := positivePhaseTest_smooth j
    have hjc := positivePhaseTest_compact j
    have hjn := positivePhaseTest_nonneg j
    obtain ⟨B,hB⟩ := hj.continuous.bounded_above_of_compact_support hjc
    obtain ⟨c,hc⟩ := projected_cumulative_balance hab hi hj.continuous.measurable hjn hB
      μ ν (hw _ hj hjc hjn)
    let _ := timeSource_finite μ hj.continuous.measurable hjn hB
    let _ := timeSource_finite ν hj.continuous.measurable hjn hB
    filter_upwards [hc] with s hs
    filter_upwards [hc] with t ht
    intro hsa hta hst
    have hμ := cumulative_increment (timeSource μ (positivePhaseTest j)) hst
    have hν := cumulative_increment (timeSource ν (positivePhaseTest j)) hst
    linarith only [hs hsa,ht hta,hμ,hν]
  have hall : ∀ᵐ s ∂volume, ∀ᵐ t ∂volume, ∀ j,
      s ∈ Ioo a b → t ∈ Ioo a b → s ≤ t →
      phaseProjection F (positivePhaseTest j) t+
        (timeSource ν (positivePhaseTest j)).real (Ioc s t) =
      phaseProjection F (positivePhaseTest j) s+
        (timeSource μ (positivePhaseTest j)).real (Ioc s t) := by
    filter_upwards [ae_all_iff.mpr hscalar] with s hs
    exact ae_all_iff.mpr hs
  have hif : ∀ᵐ t ∂volume, Integrable (fun p => F (t,p)) := hi.prod_right_ae
  have hnf : ∀ᵐ t ∂volume, ∀ᵐ p ∂volume, 0 ≤ F (t,p) := Measure.ae_ae_of_ae_prod hn
  filter_upwards [hall,hif,hnf] with s hs his hns
  filter_upwards [hs,hif,hnf] with t ht hit hnt
  intro hsa hta hst
  let _ := phaseSlice_finite his hns
  let _ := phaseSlice_finite hit hnt
  apply finite_phase_measure_eq_of_countable_tests
  intro j
  have hj := positivePhaseTest_smooth j
  have hjc := positivePhaseTest_compact j
  have hi' (m : Measure Phase) [IsFiniteMeasure m] : Integrable (positivePhaseTest j) m :=
    hj.continuous.integrable_of_hasCompactSupport hjc
  rw [integral_add_measure (hi' _) (hi' _),integral_add_measure (hi' _) (hi' _),
    phaseSlice_integral hit.aemeasurable hnt,phaseSlice_integral his.aemeasurable hns,
    phaseIncrement_timeSource ν s t hj.continuous.measurable (positivePhaseTest_nonneg j),
    phaseIncrement_timeSource μ s t hj.continuous.measurable (positivePhaseTest_nonneg j)]
  exact ht j hsa hta hst

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # The relative entropy integral is lower semicontinuous in weak L¹ -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem WeakL1Converges.entropy_liminf {f : ℕ → X → ℝ} {g m : X → ℝ}
    (h : WeakL1Converges μ f g) (hfi : ∀ n, Integrable (f n) μ)
    (hfn : ∀ n, 0 ≤ᵐ[μ] f n) (hgn : 0 ≤ᵐ[μ] g)
    (hmm : Measurable m) (hmi : Integrable m μ) (hmp : ∀ᵐ x ∂μ, 0 < m x) :
    (∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (g x)) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (f n x)) ∂μ) atTop := by
  let s : ℕ → X → ℝ := fun n x => boundedEntropyTest n (m x) (g x)
  let d : ℕ → X → ℝ := fun n x => entropyDual (m x) (g x) (s n x)
  have hsm n : Measurable (s n) := measurable_boundedEntropyTest n hmm h.1
  have hsb n x : |s n x| ≤ (n:ℝ) := boundedEntropyTest_bound n (m x) (g x)
  have hdi n : Integrable (d n) μ := integrable_entropyDual hmi h.2.1 (hsm n) (hsb n)
  have hdm n : Measurable (d n) := measurable_entropyDual hmm h.1 (hsm n)
  have hdn n : 0 ≤ᵐ[μ] d n := by
    filter_upwards [hmp,hgn] with x hmx hgx
    exact entropyDual_boundedEntropyTest_nonneg n hmx hgx
  have hbound n : ENNReal.ofReal (∫ x, d n x ∂μ) ≤
      liminf (fun k => ∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (f k x)) ∂μ) atTop := by
    have hcorr := (integrable_entropyDual hmi h.2.1 (hsm n) (hsb n))
    have hc : Integrable (fun x => m x*(Real.exp (s n x)-1)) μ := by
      have hi := (h.2.1.bdd_mul (hsm n).aestronglyMeasurable (ae_of_all μ (hsb n))).sub hcorr
      convert hi using 1
      funext x
      dsimp [entropyDual]
      ring
    have he (u : X → ℝ) (hui : Integrable u μ) :
        (∫ x, entropyDual (m x) (u x) (s n x) ∂μ) =
          (∫ x, s n x*u x ∂μ)-(∫ x, m x*(Real.exp (s n x)-1) ∂μ) := by
      simpa only [entropyDual,mul_comm,Pi.sub_def] using integral_sub
        (hui.bdd_mul (hsm n).aestronglyMeasurable (ae_of_all μ (hsb n))) hc
    have ht : Tendsto (fun k => ∫ x, entropyDual (m x) (f k x) (s n x) ∂μ)
        atTop (𝓝 (∫ x, d n x ∂μ)) := by
      simp only [he _ (hfi _),show (∫ x, d n x ∂μ) = _ from he g h.2.1]
      exact (h.2.2 (s n) (hsm n) ⟨n,hsb n⟩).sub_const _
    rw [← (ENNReal.tendsto_ofReal ht).liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall (fun k =>
      (ofReal_integral_le_lintegral (integrable_entropyDual hmi (hfi k) (hsm n) (hsb n))).trans
        (lintegral_mono_ae (by
          filter_upwards [hmp,hfn k] with x hmx hfx
          exact ENNReal.ofReal_le_ofReal (entropyDual_le hmx hfx _)))))
  have hfatou : (∫⁻ x, ENNReal.ofReal (scalarRelativeEntropy (m x) (g x)) ∂μ) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (d n x) ∂μ) atTop := by
    calc
      _ = ∫⁻ x, liminf (fun n => ENNReal.ofReal (d n x)) atTop ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hmp,hgn] with x hmx hgx
        exact (ENNReal.tendsto_ofReal (entropyDual_boundedEntropyTest_tendsto hmx hgx)).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le (fun n => (hdm n).ennreal_ofReal)
  refine hfatou.trans ?_
  exact liminf_le_of_frequently_le ((Eventually.of_forall (fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hdi n) (hdn n)]
    exact hbound n)).frequently)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Weak lower semicontinuity of the time-integrated physical entropy marginal -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
variable {μ : Measure ℝ} [IsFiniteMeasure μ]

theorem entropyMarginal_liminf {F : ℕ → ℝ × Phase → ℝ} {G : ℝ × Phase → ℝ}
    (hw : Published.WeakL1Converges (μ.prod volume) F G)
    (hFm : ∀ n, Measurable (F n)) (hFi : ∀ n, Integrable (F n) (μ.prod volume))
    (hFn : ∀ n z, 0 ≤ F n z) (hGn : ∀ z, 0 ≤ G z) :
    (∫⁻ t, entropyMarginal G t ∂μ) ≤
      liminf (fun n => ∫⁻ t, entropyMarginal (F n) t ∂μ) atTop := by
  have h := hw.entropy_liminf hFi (fun n => ae_of_all _ (hFn n)) (ae_of_all _ hGn)
    (by unfold maxwellian; fun_prop) (integrable_maxwellian_phase.comp_snd μ)
    (ae_of_all _ (fun z => maxwellian_pos z.2.2))
  have he (f : ℝ × Phase → ℝ) (hfm : Measurable f) :
      (∫⁻ z, ENNReal.ofReal (scalarRelativeEntropy (maxwellian z.2.2) (f z)) ∂μ.prod volume) =
        ∫⁻ t, entropyMarginal f t ∂μ :=
    lintegral_prod _ (spacetimeRelativeEntropy_measurable hfm).ennreal_ofReal.aemeasurable
  simpa only [he G hw.1,he _ (hFm _)] using h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
