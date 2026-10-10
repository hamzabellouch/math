import OAI.MathematicalPhysics.Boltzmann.Approximation.DormantConstruction
import OAI.MathematicalPhysics.Boltzmann.Branching.SmallDilationGeometry
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrableCoordinates

namespace OAI

section

/-! # Uniform small-time bounds on bounded kinetic boxes away from the axis -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
namespace BoltzmannNonuniqueness.JetCopyDatum

def awayKineticBox (B R ε : ℝ) : Set Published.KineticPhase :=
  ((Icc (0:ℝ) B ×ˢ Metric.closedBall (0:Velocity) R) ×ˢ Metric.closedBall (0:Velocity) R) ∩
    {z | ε ≤ ‖transverse z.2‖}

theorem measurableSet_awayKineticBox (B R ε : ℝ) : MeasurableSet (awayKineticBox B R ε) :=
  ((measurableSet_Icc.prod measurableSet_closedBall).prod measurableSet_closedBall).inter
    (measurableSet_le measurable_const ((ChartKernel.measurable_transverse.comp measurable_snd).norm))

theorem awayKineticBox_measure_lt_top (B R ε : ℝ) :
    volume (awayKineticBox B R ε) < ⊤ :=
  (measure_mono inter_subset_left).trans_lt
    (((isCompact_Icc.prod (isCompact_closedBall (0:Velocity) R)).prod
      (isCompact_closedBall (0:Velocity) R)).measure_lt_top)

def dormantBoxBound (s₀ η K α d₀ q ε B R r : ℝ) : ℝ :=
  JetSupersolution.transverseDecayConstant K d₀ ε*r^8*R^9+
    (1+JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 2))*r*B^2*(1+ε^(-q))

theorem DormantLimit.scaled_box_bound {s₀ η K α γ d₀ q ε B R : ℝ}
    {A : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit A)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : 0 ≤ q) (hqmax : q < 2) (hε : 0 < ε) (_hB : 0 ≤ B) (_hR : 0 ≤ R)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hlim : Tendsto r atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ᵐ z ∂volume.restrict (awayKineticBox B R ε),
      |(r n)⁻¹*TorusKineticChart.liftDensity D.density (kineticDilation (r n) z)| ≤
        dormantBoxBound s₀ η K α d₀ q ε B R (r n) := by
  have hc := JetSupersolution.transverseDecayConstant_nonneg (ε := ε) hK hd₀.le
  have he := JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α (JetEscapedEnvelope.exponent 2)
  filter_upwards [eventually_dilation_in_window hr hlim A.time_pos B R] with n hn
  have hb := D.scaled_central_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hqmax hε (hr n)
  filter_upwards [ae_restrict_of_ae hb,ae_restrict_mem (measurableSet_awayKineticBox B R ε)] with z hz hbox
  have hx : ‖z.1.2‖ ≤ R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hbox.1.1.2
  obtain ⟨ht,hxc⟩ := hn z.1.1 hbox.1.1.1 z.1.2 hx
  have hpos : 0 ≤ (r n)⁻¹*TorusKineticChart.liftDensity D.density (kineticDilation (r n) z) :=
    mul_nonneg (inv_nonneg.mpr (hr n).le) (D.mild.nonnegative _)
  rw [abs_of_nonneg hpos]
  apply (hz ht hxc hbox.2).trans
  have htx : ‖transverse z.1.2‖ ≤ R := by
    have hn := norm_sq_split z.1.2
    nlinarith [norm_nonneg (transverse z.1.2),norm_nonneg z.1.2,sq_nonneg (axial z.1.2)]
  have hv := H_le_off_axis hq hε hbox.2
  unfold dormantBoxBound
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) htx 9)
      (mul_nonneg hc (pow_nonneg (hr n).le 8))
  · have htcoef : 0 ≤ (1+JetEscapedEnvelope.constant s₀ η α K d₀
        (JetEscapedEnvelope.exponent 2))*r n := mul_nonneg (by linarith) (hr n).le
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbox.1.1.1.1 hbox.1.1.1.2 2) htcoef)
      hv (H_nonneg q z.2) (mul_nonneg htcoef (sq_nonneg B))

end BoltzmannNonuniqueness.JetCopyDatum

end

end

section

/-! # Small-time L1 vanishing of the actual dormant solution away from the axis -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.JetCopyDatum

theorem DormantLimit.scaled_box_L1_tendsto {s₀ η K α γ d₀ q ε B R : ℝ}
    {A : DormantFamily s₀ η K α γ d₀ q} (D : DormantLimit A)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : 0 ≤ q) (hqmax : q < 2) (hε : 0 < ε) (hB : 0 ≤ B) (hR : 0 ≤ R)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hlim : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => ∫ z in awayKineticBox B R ε,
      |(r n)⁻¹*TorusKineticChart.liftDensity D.density (kineticDilation (r n) z)|)
      atTop (𝓝 0) := by
  let μ : Measure Published.KineticPhase := volume.restrict (awayKineticBox B R ε)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (awayKineticBox_measure_lt_top B R ε).ne
  have hm (n) : Measurable (fun z =>
      (r n)⁻¹*TorusKineticChart.liftDensity D.density (kineticDilation (r n) z)) :=
    ((TorusKineticChart.liftDensity_measurable D.mild.measurable).comp
      (kineticDilation_quasiMeasurePreserving (hr n)).measurable).const_mul _
  apply integral_abs_tendsto_of_uniform_bound (μ := μ) (fun n => (hm n).aestronglyMeasurable)
    (D.scaled_box_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
      hq hqmax hε hB hR hr hlim)
  have h1 := ((hlim.pow 8).const_mul (JetSupersolution.transverseDecayConstant K d₀ ε)).mul_const (R^9)
  have h2 := (((hlim.const_mul
    (1+JetEscapedEnvelope.constant s₀ η α K d₀ (JetEscapedEnvelope.exponent 2))).mul_const (B^2)).mul_const
      (1+ε^(-q)))
  simpa only [dormantBoxBound,zero_pow (by norm_num : 8 ≠ 0),mul_zero,zero_mul,zero_add] using h1.add h2

end BoltzmannNonuniqueness.JetCopyDatum

end

end

end OAI
