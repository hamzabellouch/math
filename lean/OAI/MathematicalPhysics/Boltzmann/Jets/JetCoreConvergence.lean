import OAI.MathematicalPhysics.Boltzmann.Collision.AxialJointAnalytic
import OAI.MathematicalPhysics.Boltzmann.Collision.AxialSecondMismatch
import OAI.MathematicalPhysics.Boltzmann.Collision.GaussianFrequency
import OAI.MathematicalPhysics.Boltzmann.Collision.SheetIntervals
import OAI.MathematicalPhysics.Boltzmann.Jets.JetEnvelopeTimeIntegral
import OAI.MathematicalPhysics.Boltzmann.Jets.JetSupersolutions
import OAI.MathematicalPhysics.Boltzmann.Jets.JetProfiles
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

section

/-! # Limits of the compressed axial amplitude in thermal coordinates -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetCoreMap

theorem axialMap_tendsto {s d : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) (σ z w : ℝ) :
    Tendsto (fun n => axialMap σ α γ (s n) (d n) t z w) atTop
      (𝓝 (AxialFlow.velocity σ α γ μ t z)) := by
  have hdiff : Tendsto (fun n => axialMap σ α γ (s n) (d n) t z w-
      AxialFlow.velocity σ α γ (s n) t z) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun n => by simpa only [Real.norm_eq_abs] using axialMap_error_le hα hγ (hs n) (hd n) ht σ z w)
    simpa only [zero_mul] using hdlim.mul_const |w|
  have h := hdiff.add (AxialFlow.velocity_scale_tendsto hα hγ hs hμ ht hslim σ z)
  simpa only [sub_add_cancel,zero_add] using h

theorem sourceFoot_tendsto {s d : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) (σ z w : ℝ) :
    Tendsto (fun n => sourceFoot σ α γ (s n) (d n) t z w) atTop
      (𝓝 (AxialFlow.foot σ α γ μ t z)) := by
  simp_rw [sourceFoot_eq]
  exact tendsto_const_nhds.sub ((axialMap_tendsto hα hγ hs hd hμ ht hslim hdlim σ z w).const_mul t)

end BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem compressed_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (K ζ : ℝ) :
    r*compressed K α γ (r*s) (r*t) (r*ζ) = compressed K α γ s t ζ := by
  have harg : γ*(r*ζ)/(r*s) = γ*ζ/s := by field_simp
  have hSp : 0 ≤ S (γ*ζ/s) := (S_pos _).le
  have hden : s+t*α*γ*S (γ*ζ/s) ≠ 0 := ne_of_gt (by positivity)
  unfold compressed
  rw [harg]
  field_simp

theorem compressed_tendsto {s ζ : ℕ → ℝ} {α γ μ t z : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hslim : Tendsto s atTop (𝓝 μ)) (hζlim : Tendsto ζ atTop (𝓝 z)) (K : ℝ) :
    Tendsto (fun n => compressed K α γ (s n) t (ζ n)) atTop (𝓝 (compressed K α γ μ t z)) := by
  have harg := (hζlim.const_mul γ).div hslim hμ.ne'
  have hS := continuous_S.continuousAt.tendsto.comp harg
  have hSp : 0 ≤ S (γ*z/μ) := (S_pos _).le
  have hden : μ+t*α*γ*S (γ*z/μ) ≠ 0 := ne_of_gt (by positivity)
  have h := (hS.const_mul K).div (hslim.add (hS.const_mul (t*α*γ)))
    (by simpa only [mul_assoc] using hden)
  change Tendsto (fun n => K*S (γ*ζ n/s n)/(s n+(t*α*γ)*S (γ*ζ n/s n)))
    atTop (𝓝 (K*S (γ*z/μ)/(μ+(t*α*γ)*S (γ*z/μ)))) at h
  simpa only [compressed,mul_assoc] using h

theorem compressed_sourceFoot_tendsto {s d : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) (σ K z w : ℝ) :
    Tendsto (fun n => compressed K α γ (s n) t (JetCoreMap.sourceFoot σ α γ (s n) (d n) t z w))
      atTop (𝓝 (compressed K α γ μ t (AxialFlow.foot σ α γ μ t z))) :=
  compressed_tendsto hα hγ hμ ht hslim
    (JetCoreMap.sourceFoot_tendsto hα hγ hs hd hμ ht hslim hdlim σ z w) K

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # The actual thermal coordinate map converges to the axial atom -/

noncomputable section

open Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.PlaneChart

theorem join_sub (y u : Transverse) (z v : ℝ) :
    join y z-join u v = join (y-u) (z-v) := by
  apply split.injective
  simp only [split_apply,transverse_sub,axial_sub,transverse_join,axial_join]

theorem join_tendsto {y : ℕ → Transverse} {z : ℕ → ℝ} {u : Transverse} {v : ℝ}
    (hy : Tendsto y atTop (𝓝 u)) (hz : Tendsto z atTop (𝓝 v)) :
    Tendsto (fun n => join (y n) (z n)) atTop (𝓝 (join u v)) := by
  have hyn : Tendsto (fun n => ‖y n-u‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (hy.sub (tendsto_const_nhds (x := u))).norm
  have hzn : Tendsto (fun n => z n-v) atTop (𝓝 0) := by
    simpa only [sub_self] using hz.sub (tendsto_const_nhds (x := v))
  have he (n) : ‖join (y n) (z n)-join u v‖ =
      Real.sqrt (‖y n-u‖^2+(z n-v)^2) := by
    rw [join_sub,← norm_join_sq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp_rw [he]
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp ((hyn.pow 2).add (hzn.pow 2))
  change Tendsto (fun n => Real.sqrt (‖y n-u‖^2+(z n-v)^2)) atTop
    (𝓝 (Real.sqrt ((0:ℝ)^2+0^2))) at h
  simpa only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,Real.sqrt_zero] using h

end BoltzmannNonuniqueness.PlaneChart

namespace BoltzmannNonuniqueness.JetCoreMeasure

theorem velocityMap_tendsto {s d : ℕ → ℝ} {α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) (σ z : ℝ) (w : Transverse × ℝ) :
    Tendsto (fun n => velocityMap σ α γ (s n) (d n) t z w) atTop
      (𝓝 (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))) := by
  apply PlaneChart.join_tendsto
  · simpa only [zero_smul] using hdlim.smul_const w.1
  · exact JetCoreMap.axialMap_tendsto hα hγ hs hd hμ ht hslim hdlim σ z w.2

end BoltzmannNonuniqueness.JetCoreMeasure

end

end

section

/-! # Convergence of the smooth factor of a cold core

The spatial stripe indicator is treated separately. This is the full thermal
integral of the compressed amplitude and a bounded continuous velocity test.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetAxialWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem continuous_compressed {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (K : ℝ) : Continuous (compressed K α γ s t) := by
  have hc : Continuous (fun ζ : ℝ => S (γ*ζ/s)) :=
    continuous_S.comp ((continuous_const.mul continuous_id).div_const s)
  apply (continuous_const.mul hc).div (continuous_const.add (continuous_const.mul hc))
  intro ζ
  change s+(t*α*γ)*S (γ*ζ/s) ≠ 0
  have := (S_pos (γ*ζ/s)).le
  exact ne_of_gt (by positivity)

theorem compressed_le_scale {K α γ s t a : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (ha : 0 < a) (hs : a ≤ s) (ht : 0 ≤ t) (ζ : ℝ) :
    compressed K α γ s t ζ ≤ K/a := by
  have hp := (S_pos (γ*ζ/s)).le
  have hden : a ≤ s+t*α*γ*S (γ*ζ/s) := le_add_of_le_of_nonneg hs (by positivity)
  calc
    compressed K α γ s t ζ ≤ K/(s+t*α*γ*S (γ*ζ/s)) :=
      div_le_div_of_nonneg_right (mul_le_of_le_one_right hK (S_le_one _))
        (ha.le.trans hden)
    _ ≤ K/a := div_le_div_of_nonneg_left hK ha hden

theorem sourceFoot_continuous {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (σ d z : ℝ) :
    Continuous (JetCoreMap.sourceFoot σ α γ s d t z) :=
  (AxialFlow.foot_lipschitzWith hα hγ hs ht).continuous.comp
    (continuous_const.sub (continuous_const.mul continuous_id))

theorem thermal_test_tendsto {s d : ℕ → ℝ} {K α γ μ t a B : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a)
    (hs : ∀ n, a ≤ s n) (hd : ∀ n, 0 < d n) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    {ψ : Velocity → ℝ} (hψ : Continuous ψ)
    (hψB : ∀ v, |ψ v| ≤ B) (σ z : ℝ) :
    Tendsto (fun n => ∫ w : Transverse × ℝ,
      compressed K α γ (s n) t (JetCoreMap.sourceFoot σ α γ (s n) (d n) t z w.2) *
        ψ (JetCoreMeasure.velocityMap σ α γ (s n) (d n) t z w) *
          JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume) atTop
      (𝓝 (compressed K α γ μ t (AxialFlow.foot σ α γ μ t z) *
        ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)))) := by
  have hsp (n) : 0 < s n := ha.trans_le (hs n)
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  have hJi : (∫ w : Transverse × ℝ, JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume) = 1 := by
    rw [HotRectangleDensity.join_measurePreserving.integral_comp
      SheetMeasures.join.measurableEmbedding, JetThermalKernel.J_integral]
  have hl := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Transverse).prod volume)
    (F := fun n w => compressed K α γ (s n) t
      (JetCoreMap.sourceFoot σ α γ (s n) (d n) t z w.2) *
      ψ (JetCoreMeasure.velocityMap σ α γ (s n) (d n) t z w) *
      JetThermalKernel.J (SheetMeasures.join w))
    (f := fun w => (compressed K α γ μ t (AxialFlow.foot σ α γ μ t z) *
      ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))) *
      JetThermalKernel.J (SheetMeasures.join w))
    (fun w => (K/a*B)*JetThermalKernel.J (SheetMeasures.join w)) ?_
    (hJ.const_mul _) ?_ ?_
  · simpa only [integral_const_mul,hJi,mul_one] using hl
  · intro n
    have hc : Continuous (fun w : Transverse × ℝ => compressed K α γ (s n) t
        (JetCoreMap.sourceFoot σ α γ (s n) (d n) t z w.2)) :=
      (continuous_compressed hα hγ (hsp n) ht K).comp
      ((sourceFoot_continuous hα hγ (hsp n) ht σ (d n) z).comp continuous_snd)
    have hv := (JetCoreMeasure.velocity_measurePreserving hα hγ (hsp n) (hd n) ht σ z).measurable
    exact ((hc.measurable.mul (hψ.measurable.comp hv)).mul
      (JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable)).aestronglyMeasurable
  · intro n
    filter_upwards [] with w
    rw [Real.norm_eq_abs,abs_mul,abs_mul,
      abs_of_nonneg (compressed_nonneg hK hα hγ (hsp n) ht _),
      abs_of_nonneg (JetThermalKernel.J_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (compressed_le_scale hK hα hγ ha (hs n) ht _) (hψB _)
        (abs_nonneg _) (div_nonneg hK ha.le)) (JetThermalKernel.J_nonneg _)
  · filter_upwards [] with w
    have hc := compressed_sourceFoot_tendsto hα hγ hsp (fun n => (hd n).le)
      hμ ht hslim hdlim σ K z w.2
    have hv := hψ.continuousAt.tendsto.comp
      (JetCoreMeasure.velocityMap_tendsto hα hγ hsp (fun n => (hd n).le)
        hμ ht hslim hdlim σ z w)
    exact (hc.mul hv).mul_const _

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # The physical axial cutoff disappears on the thermal support -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreMap

theorem sourceFoot_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ d z w : ℝ) :
    sourceFoot σ α γ (r*s) d (r*t) (r*z) w = r*sourceFoot σ α γ s d t z w := by
  rw [sourceFoot_eq,sourceFoot_eq,axialMap_dilation hr hα hγ hs ht]
  ring

theorem sourceFoot_abs_le {α d t : ℝ} (hα : 0 ≤ α) (hd : 0 ≤ d) (ht : 0 ≤ t)
    (σ γ s z w : ℝ) (hw : |w| ≤ 1) :
    |sourceFoot σ α γ s d t z w| ≤ |z|+t*(|σ|+α+d) := by
  have hv : |axialMap σ α γ s d t z w| ≤ |σ|+α+d := by
    calc
      |axialMap σ α γ s d t z w| ≤ |d*w|+|AxialFlow.velocity σ α γ s t (z-t*d*w)| :=
        abs_add_le _ _
      _ ≤ d+(|σ|+α) := by
        rw [abs_mul,abs_of_nonneg hd]
        exact add_le_add (by nlinarith) (AxialTransport.velocity_abs_le hα)
      _ = _ := by ring
  rw [sourceFoot_eq]
  calc
    |z-t*axialMap σ α γ s d t z w| ≤ |z|+|t*axialMap σ α γ s d t z w| := abs_sub z _
    _ ≤ _ := by rw [abs_mul,abs_of_nonneg ht]; gcongr

end BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem thermal_parameter_axial_le_one {w : Transverse × ℝ}
    (hw : JetThermalKernel.J (SheetMeasures.join w) ≠ 0) : |w.2| ≤ 1 := by
  have hj : ‖SheetMeasures.join w‖ < 1 := by
    by_contra hn
    exact hw (JetThermalKernel.J_zero (le_of_not_gt hn))
  have he : ‖SheetMeasures.join w‖^2 = ‖w.1‖^2+w.2^2 := PlaneChart.norm_join_sq w.1 w.2
  nlinarith [sq_nonneg ‖w.1‖,norm_nonneg (SheetMeasures.join w),sq_abs w.2,abs_nonneg w.2]

theorem eventually_axial_cutoff {r s d : ℕ → ℝ} {α t : ℝ}
    (hα : 0 ≤ α) (hd : ∀ n, 0 ≤ d n) (ht : 0 ≤ t)
    (hrlim : Tendsto r atTop (𝓝 0)) (hdlim : Tendsto d atTop (𝓝 0)) (σ γ z : ℝ) :
    ∀ᶠ n in atTop, ∀ w : Transverse × ℝ,
      JetThermalKernel.J (SheetMeasures.join w) ≠ 0 →
      r n*JetCoreMap.sourceFoot σ α γ (s n) (d n) t z w.2 ∈
        Ioo (-(1/8:ℝ)) (1/8) := by
  have hsmall : ∀ᶠ n in atTop, |r n| * (|z|+t*(|σ|+α+1)) < (1/8:ℝ) := by
    have h := hrlim.abs.mul_const (|z|+t*(|σ|+α+1))
    have he := h.eventually (gt_mem_nhds (by norm_num : |(0:ℝ)| * (|z|+t*(|σ|+α+1)) < 1/8))
    exact he
  have hdsmall : ∀ᶠ n in atTop, d n < 1 := hdlim.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hsmall,hdsmall] with n hn hdn w hw
  apply abs_lt.mp
  rw [abs_mul]
  apply lt_of_le_of_lt _ hn
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact (JetCoreMap.sourceFoot_abs_le hα (hd n) ht σ γ (s n) z w.2
    (thermal_parameter_axial_le_one hw)).trans (by gcongr)

theorem axial_cutoff_test_tendsto {r s d : ℕ → ℝ} {K α γ μ t a B : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a)
    (hs : ∀ n, a ≤ s n) (hd : ∀ n, 0 < d n) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hrlim : Tendsto r atTop (𝓝 0)) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) {ψ : Velocity → ℝ}
    (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) (σ z : ℝ) :
    Tendsto (fun n => ∫ w : Transverse × ℝ,
      (Ioo (-(1/8:ℝ)) (1/8)).indicator (fun _ => (1:ℝ))
        (r n*JetCoreMap.sourceFoot σ α γ (s n) (d n) t z w.2) *
      compressed K α γ (s n) t (JetCoreMap.sourceFoot σ α γ (s n) (d n) t z w.2) *
      ψ (JetCoreMeasure.velocityMap σ α γ (s n) (d n) t z w) *
      JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume) atTop
      (𝓝 (compressed K α γ μ t (AxialFlow.foot σ α γ μ t z) *
        ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)))) := by
  apply (thermal_test_tendsto hK hα hγ ha hs hd hμ ht hslim hdlim hψ hψB σ z).congr'
  filter_upwards [eventually_axial_cutoff (s := s) hα (fun n => (hd n).le) ht hrlim hdlim σ γ z]
    with n hn
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : JetThermalKernel.J (SheetMeasures.join w) = 0
  · simp only [hw,mul_zero]
  · rw [indicator_of_mem (hn w hw),one_mul]

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Thermal L1 convergence before spatial stripe averaging -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

def testCoefficient (K α γ s d t σ z : ℝ) (ψ : Velocity → ℝ) (w : Transverse × ℝ) : ℝ :=
  compressed K α γ s t (JetCoreMap.sourceFoot σ α γ s d t z w.2) *
    ψ (JetCoreMeasure.velocityMap σ α γ s d t z w)

theorem testCoefficient_measurable {α γ s d t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (K σ z : ℝ) {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    Measurable (testCoefficient K α γ s d t σ z ψ) := by
  have hc : Continuous (fun w : Transverse × ℝ =>
      compressed K α γ s t (JetCoreMap.sourceFoot σ α γ s d t z w.2)) :=
    (continuous_compressed hα hγ hs ht K).comp
      ((sourceFoot_continuous hα hγ hs ht σ d z).comp continuous_snd)
  exact hc.measurable.mul (hψ.measurable.comp
    (JetCoreMeasure.velocity_measurePreserving hα hγ hs hd ht σ z).measurable)

theorem testCoefficient_abs_le {K α γ s t a B : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a)
    (hs : a ≤ s) (ht : 0 ≤ t) {ψ : Velocity → ℝ} (hψB : ∀ v, |ψ v| ≤ B)
    (d σ z : ℝ) (w : Transverse × ℝ) :
    |testCoefficient K α γ s d t σ z ψ w| ≤ K/a*B := by
  rw [testCoefficient,abs_mul,abs_of_nonneg (compressed_nonneg hK hα hγ (ha.trans_le hs) ht _)]
  exact mul_le_mul (compressed_le_scale hK hα hγ ha hs ht _) (hψB _)
    (abs_nonneg _) (div_nonneg hK ha.le)

theorem testCoefficient_tendsto {s d : ℕ → ℝ} {K α γ μ t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : ∀ n, 0 < s n) (hd : ∀ n, 0 ≤ d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hslim : Tendsto s atTop (𝓝 μ))
    (hdlim : Tendsto d atTop (𝓝 0)) {ψ : Velocity → ℝ} (hψ : Continuous ψ)
    (σ z : ℝ) (w : Transverse × ℝ) :
    Tendsto (fun n => testCoefficient K α γ (s n) (d n) t σ z ψ w) atTop
      (𝓝 (compressed K α γ μ t (AxialFlow.foot σ α γ μ t z) *
        ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z)))) :=
  (compressed_sourceFoot_tendsto hα hγ hs hd hμ ht hslim hdlim σ K z w.2).mul
    (hψ.continuousAt.tendsto.comp
      (JetCoreMeasure.velocityMap_tendsto hα hγ hs hd hμ ht hslim hdlim σ z w))

theorem thermal_coefficient_error_tendsto {s d : ℕ → ℝ} {K α γ μ t a B : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a)
    (hs : ∀ n, a ≤ s n) (hd : ∀ n, 0 < d n) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B) (σ z : ℝ) :
    Tendsto (fun n => ∫ w : Transverse × ℝ,
      |testCoefficient K α γ (s n) (d n) t σ z ψ w -
        compressed K α γ μ t (AxialFlow.foot σ α γ μ t z) *
          ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))| *
        JetThermalKernel.J (SheetMeasures.join w)
      ∂(volume : Measure Transverse).prod volume) atTop (𝓝 0) := by
  let c := compressed K α γ μ t (AxialFlow.foot σ α γ μ t z) *
    ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))
  have hsp (n) : 0 < s n := ha.trans_le (hs n)
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  have hmJ := JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable
  have hl := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure Transverse).prod volume)
    (F := fun n w => |testCoefficient K α γ (s n) (d n) t σ z ψ w-c| *
      JetThermalKernel.J (SheetMeasures.join w)) (f := fun _ => (0:ℝ))
    (fun w => (K/a*B+|c|)*JetThermalKernel.J (SheetMeasures.join w))
    (fun n => (((testCoefficient_measurable hα hγ (hsp n) (hd n) ht K σ z hψ).sub
      measurable_const).abs.mul hmJ).aestronglyMeasurable) (hJ.const_mul _) ?_ ?_
  · simpa only [integral_zero] using hl
  · intro n
    filter_upwards [] with w
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (JetThermalKernel.J_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
    exact (abs_sub _ _).trans (add_le_add
      (testCoefficient_abs_le hK hα hγ ha (hs n) ht hψB (d n) σ z w) le_rfl)
  · filter_upwards [] with w
    have hc := testCoefficient_tendsto (K := K) hα hγ hsp (fun n => (hd n).le)
      hμ ht hslim hdlim hψ σ z w
    have h := ((hc.sub (tendsto_const_nhds (x := c))).abs).mul_const
      (JetThermalKernel.J (SheetMeasures.join w))
    simpa only [c,sub_self,abs_zero,zero_mul] using h

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Replacing the thermal coefficient inside arbitrary bounded masks -/

noncomputable section

open MeasureTheory Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreDensity

private theorem masked_error_le {f χ : Transverse × ℝ → ℝ} {S c : ℝ}
    (hf : Measurable f) (hχ : Measurable χ) (hfS : ∀ w, |f w| ≤ S)
    (hχ1 : ∀ w, |χ w| ≤ 1) :
    |(∫ w, χ w*f w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)-
      c*(∫ w, χ w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)| ≤
      ∫ w, |f w-c| *JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume := by
  have hJ := HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable
  have hmJ := JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable
  have hiχ : Integrable (fun w => χ w*JetThermalKernel.J (SheetMeasures.join w))
      ((volume : Measure Transverse).prod volume) := by
    apply hJ.mono' (hχ.mul hmJ).aestronglyMeasurable
    filter_upwards [] with w
    change ‖χ w*JetThermalKernel.J (SheetMeasures.join w)‖ ≤ JetThermalKernel.J (SheetMeasures.join w)
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχ1 w) (JetThermalKernel.J_nonneg _)
  have hif : Integrable (fun w => χ w*f w*JetThermalKernel.J (SheetMeasures.join w))
      ((volume : Measure Transverse).prod volume) := by
    apply (hJ.const_mul S).mono' ((hχ.mul hf).mul hmJ).aestronglyMeasurable
    filter_upwards [] with w
    change ‖χ w*f w*JetThermalKernel.J (SheetMeasures.join w)‖ ≤ S*JetThermalKernel.J (SheetMeasures.join w)
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
    apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
    exact (mul_le_mul_of_nonneg_right (hχ1 w) (abs_nonneg _)).trans (by simpa using hfS w)
  have hierr : Integrable (fun w => |f w-c| *JetThermalKernel.J (SheetMeasures.join w))
      ((volume : Measure Transverse).prod volume) := by
    apply (hJ.const_mul (S+|c|)).mono' (((hf.sub measurable_const).abs).mul hmJ).aestronglyMeasurable
    filter_upwards [] with w
    change ‖|f w-c| *JetThermalKernel.J (SheetMeasures.join w)‖ ≤ (S+|c|)*JetThermalKernel.J (SheetMeasures.join w)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (JetThermalKernel.J_nonneg _))]
    exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (add_le_add (hfS w) le_rfl))
      (JetThermalKernel.J_nonneg _)
  have hidiff := hif.sub (hiχ.const_mul c)
  have he : (∫ w, χ w*f w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)-
      c*(∫ w, χ w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume) =
      ∫ w, χ w*f w*JetThermalKernel.J (SheetMeasures.join w)-
        c*(χ w*JetThermalKernel.J (SheetMeasures.join w))
        ∂(volume : Measure Transverse).prod volume := by
    rw [integral_sub hif (hiχ.const_mul c),integral_const_mul]
  rw [he]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono hidiff.norm hierr
  intro w
  change ‖χ w*f w*JetThermalKernel.J (SheetMeasures.join w)-
    c*(χ w*JetThermalKernel.J (SheetMeasures.join w))‖ ≤
    |f w-c| *JetThermalKernel.J (SheetMeasures.join w)
  rw [show χ w*f w*JetThermalKernel.J (SheetMeasures.join w)-
      c*(χ w*JetThermalKernel.J (SheetMeasures.join w)) =
      χ w*(f w-c)*JetThermalKernel.J (SheetMeasures.join w) by ring,
    Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (JetThermalKernel.J_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχ1 w) (abs_nonneg (f w-c)))
    (JetThermalKernel.J_nonneg _)

theorem thermal_masked_error_tendsto {s d : ℕ → ℝ} {K α γ μ t a B : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (ha : 0 < a)
    (hs : ∀ n, a ≤ s n) (hd : ∀ n, 0 < d n) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    {χ : ℕ → Transverse × ℝ → ℝ} (hχ : ∀ n, Measurable (χ n))
    (hχ1 : ∀ n w, |χ n w| ≤ 1) (σ z : ℝ) :
    Tendsto (fun n =>
      (∫ w, χ n w*testCoefficient K α γ (s n) (d n) t σ z ψ w *
        JetThermalKernel.J (SheetMeasures.join w) ∂(volume : Measure Transverse).prod volume)-
      (compressed K α γ μ t (AxialFlow.foot σ α γ μ t z)*
        ψ (PlaneChart.join 0 (AxialFlow.velocity σ α γ μ t z))) *
      (∫ w, χ n w*JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (thermal_coefficient_error_tendsto hK hα hγ ha hs hd hμ ht hslim hdlim hψ hψB σ z)
  rw [Real.norm_eq_abs]
  exact masked_error_le
    (testCoefficient_measurable hα hγ (ha.trans_le (hs n)) (hd n) ht K σ z hψ) (hχ n)
    (testCoefficient_abs_le hK hα hγ ha (hs n) ht hψB (d n) σ z) (hχ1 n)

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # The exact thermal-coordinate integral of the physical free core -/

noncomputable section

open MeasureTheory Set Filter
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCoreMeasure

theorem velocityMap_dilation {r α γ s t : ℝ} (hr : 0 < r) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t) (σ d z : ℝ) (w : Transverse × ℝ) :
    velocityMap σ α γ (r*s) d (r*t) (r*z) w = velocityMap σ α γ s d t z w := by
  unfold velocityMap
  rw [JetCoreMap.axialMap_dilation hr hα hγ hs ht]

end BoltzmannNonuniqueness.JetCoreMeasure

namespace BoltzmannNonuniqueness.JetCoreDensity

theorem weight_measurable {α γ s t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (ht : 0 ≤ t) (η K d : ℝ) (a : Bool) (x : Space) :
    Measurable (weight η K α γ s d t a x) := by
  have hm : Measurable (fun w : Transverse × ℝ =>
      (JetGeometry.mask η s a).indicator (fun _ => (1:ℝ)) (x.1-t • (d • w.1))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η s a)).comp (by fun_prop)
  have hf := ((sourceFoot_continuous hα hγ hs ht (sign a) d x.2).comp
    (continuous_snd : Continuous (Prod.snd : Transverse × ℝ → ℝ))).measurable
  have hc := ((continuous_compressed hα hγ hs ht K).measurable.indicator
    (measurableSet_Ioo : MeasurableSet (Ioo (-(1/8:ℝ)) (1/8)))).comp hf
  exact (hm.mul hc).mul (JetThermalKernel.J_smooth.continuous.measurable.comp
    SheetMeasures.join.measurable)

theorem weight_nonneg {K α γ s t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η d : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    0 ≤ weight η K α γ s d t a x w := by
  unfold weight
  apply mul_nonneg _ (JetThermalKernel.J_nonneg _)
  apply mul_nonneg
  · exact indicator_nonneg (fun _ _ => zero_le_one) _
  · exact indicator_nonneg (fun ζ _ => compressed_nonneg hK hα hγ hs ht ζ) _

theorem free_test_integral {K α γ s d t : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η : ℝ) (a : Bool) (x : Space) {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    (∫ v, JetFreeTransport.free η K α γ s d t a (x,v)*ψ v) =
      ∫ w : Transverse × ℝ, weight η K α γ s d t a x w *
        ψ (JetCoreMeasure.velocityMap (sign a) α γ s d t x.2 w)
        ∂(volume : Measure Transverse).prod volume := by
  have hfm : Measurable (fun v => JetFreeTransport.free η K α γ s d t a (x,v)) :=
    (JetFreeTransport.measurable_free η K α γ s d t a).comp
      (measurable_const.prodMk measurable_id)
  have hwm := weight_measurable hα hγ hs ht η K d a x
  have hi := measure_identity hα hγ hs hd ht η K a x
  have hvm := (JetCoreMeasure.velocity_measurePreserving hα hγ hs hd ht (sign a) x.2).measurable
  calc
    _ = ∫ v, ψ v ∂volume.withDensity
        (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x,v))) := by
      rw [integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (JetFreeTransport.free_nonneg hK hs.le hd.le η α γ t a _),
        smul_eq_mul]
    _ = ∫ w, ψ (JetCoreMeasure.velocityMap (sign a) α γ s d t x.2 w)
        ∂((volume : Measure Transverse).prod volume).withDensity
          (fun w => ENNReal.ofReal (weight η K α γ s d t a x w)) := by
      rw [← hi,integral_map hvm.aemeasurable hψ.measurable.aestronglyMeasurable]
    _ = _ := by
      rw [integral_withDensity_eq_integral_toReal_smul hwm.ennreal_ofReal
        (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
      simp only [ENNReal.toReal_ofReal (weight_nonneg hK hα hγ hs ht η d a x _),smul_eq_mul]

theorem weight_dilation {r α γ s t : ℝ} (hr : 0 < r) (hα : 0 ≤ α)
    (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (η K d : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    r*weight η K α γ (r*s) d (r*t) a (r • x) w =
      (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • x.1-(r*t) • (d • w.1)) *
      (Ioo (-(1/8:ℝ)) (1/8)).indicator (fun _ => (1:ℝ))
        (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
      compressed K α γ s t (JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
      JetThermalKernel.J (SheetMeasures.join w) := by
  unfold weight
  change r * (_ * (Ioo (-(1/8:ℝ)) (1/8)).indicator (compressed K α γ (r*s) (r*t))
    (JetCoreMap.sourceFoot (sign a) α γ (r*s) d (r*t) (r*x.2) w.2) * _) = _
  rw [JetCoreMap.sourceFoot_dilation hr hα hγ hs ht]
  by_cases hz : r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2 ∈ Ioo (-(1/8:ℝ)) (1/8)
  · simp only [indicator_of_mem hz,mul_one]
    change r * ((JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • x.1-(r*t) • (d • w.1)) * compressed K α γ (r*s) (r*t)
        (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
        JetThermalKernel.J (SheetMeasures.join w)) = _
    rw [show r * ((JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • x.1-(r*t) • (d • w.1)) * compressed K α γ (r*s) (r*t)
        (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
        JetThermalKernel.J (SheetMeasures.join w)) =
      (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
        (r • x.1-(r*t) • (d • w.1)) * (r*compressed K α γ (r*s) (r*t)
        (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2)) *
        JetThermalKernel.J (SheetMeasures.join w) by ring]
    rw [compressed_dilation hr hα hγ hs ht]
  · simp only [indicator_of_notMem hz,mul_zero,zero_mul]

theorem dilated_free_test_integral {r K α γ s d t : ℝ} (hr : 0 < r)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 ≤ t) (η : ℝ) (a : Bool) (x : Space)
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) :
    (∫ v, r*JetFreeTransport.free η K α γ (r*s) d (r*t) a (r • x,v)*ψ v) =
      ∫ w : Transverse × ℝ,
        (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
          (r • x.1-(r*t) • (d • w.1)) *
        (Ioo (-(1/8:ℝ)) (1/8)).indicator (fun _ => (1:ℝ))
          (r*JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
        compressed K α γ s t (JetCoreMap.sourceFoot (sign a) α γ s d t x.2 w.2) *
        ψ (JetCoreMeasure.velocityMap (sign a) α γ s d t x.2 w) *
        JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume := by
  have hi := free_test_integral hK hα hγ (mul_pos hr hs) hd (mul_nonneg hr.le ht) η a (r • x) hψ
  calc
    _ = r * (∫ v, JetFreeTransport.free η K α γ (r*s) d (r*t) a (r • x,v)*ψ v) := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    _ = r * (∫ w : Transverse × ℝ, weight η K α γ (r*s) d (r*t) a (r • x) w *
        ψ (JetCoreMeasure.velocityMap (sign a) α γ (r*s) d (r*t) (r • x).2 w)
        ∂(volume : Measure Transverse).prod volume) := by rw [hi]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      rw [← mul_assoc,weight_dilation hr hα hγ hs ht]
      change _ * ψ (JetCoreMeasure.velocityMap (sign a) α γ (r*s) d (r*t) (r*x.2) w) = _
      rw [JetCoreMeasure.velocityMap_dilation hr hα hγ hs ht]
      ring

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # Reduction of the actual dilated free core to its spatial mask average -/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype

namespace BoltzmannNonuniqueness.JetCoreDensity

def dilatedMask (r η s d t : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) : ℝ :=
  (JetGeometry.mask η (r*s) a).indicator (fun _ => (1:ℝ))
    (r • x.1-(r*t) • (d • w.1))

theorem dilatedMask_measurable (r η s d t : ℝ) (a : Bool) (x : Space) :
    Measurable (dilatedMask r η s d t a x) :=
  (measurable_const.indicator (JetMaskMeasure.measurableSet_mask η (r*s) a)).comp (by fun_prop)

theorem dilatedMask_abs_le (r η s d t : ℝ) (a : Bool) (x : Space) (w : Transverse × ℝ) :
    |dilatedMask r η s d t a x w| ≤ 1 := by
  unfold dilatedMask
  by_cases h : r • x.1-(r*t) • (d • w.1) ∈ JetGeometry.mask η (r*s) a
  · simp only [indicator_of_mem h,abs_one,le_refl]
  · simp only [indicator_of_notMem h,abs_zero,zero_le_one]

theorem dilated_free_thermal_reduction {r s d : ℕ → ℝ} {K α γ μ t b B : ℝ}
    (hr : ∀ n, 0 < r n) (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hb : 0 < b) (hs : ∀ n, b ≤ s n) (hd : ∀ n, 0 < d n)
    (hμ : 0 < μ) (ht : 0 ≤ t) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    {ψ : Velocity → ℝ} (hψ : Continuous ψ) (hψB : ∀ v, |ψ v| ≤ B)
    (η : ℝ) (a : Bool) (x : Space) :
    Tendsto (fun n =>
      (∫ v, r n*JetFreeTransport.free η K α γ (r n*s n) (d n) (r n*t) a (r n • x,v)*ψ v)-
      (compressed K α γ μ t (AxialFlow.foot (sign a) α γ μ t x.2)*
        ψ (PlaneChart.join 0 (AxialFlow.velocity (sign a) α γ μ t x.2))) *
      (∫ w, dilatedMask (r n) η (s n) (d n) t a x w *
        JetThermalKernel.J (SheetMeasures.join w)
        ∂(volume : Measure Transverse).prod volume)) atTop (𝓝 0) := by
  have hbase := thermal_masked_error_tendsto hK hα hγ hb hs hd hμ ht hslim hdlim hψ hψB
    (fun n => dilatedMask_measurable (r n) η (s n) (d n) t a x)
    (fun n w => dilatedMask_abs_le (r n) η (s n) (d n) t a x w) (sign a) x.2
  apply hbase.congr'
  filter_upwards [eventually_axial_cutoff (s := s) hα (fun n => (hd n).le) ht hrlim hdlim
    (sign a) γ x.2] with n hn
  congr 1
  rw [dilated_free_test_integral (hr n) hK hα hγ (hb.trans_le (hs n)) (hd n) ht η a x hψ]
  apply integral_congr_ae
  filter_upwards [] with w
  by_cases hw : JetThermalKernel.J (SheetMeasures.join w) = 0
  · simp only [hw,mul_zero]
  · rw [indicator_of_mem (hn w hw),mul_one]
    unfold testCoefficient dilatedMask
    ring

end BoltzmannNonuniqueness.JetCoreDensity

end

end

section

/-! # A centered thermal Gaussian as an admissible product sheet -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreMeasure
open BoltzmannNonuniqueness.JetCoreMap

namespace BoltzmannNonuniqueness.JetAffineSheet

def center (u : ℝ) : Velocity := PlaneChart.join 0 u

def affineMap (d u : ℝ) (w : Transverse × ℝ) : Velocity :=
  PlaneChart.join (d • w.1) (u + d * w.2)

theorem affineMap_eq (d u : ℝ) : affineMap d u = velocityMap u 0 0 1 d 0 0 := by
  funext w
  have hv := AxialFlow.velocity_spec (σ := u) (γ := (0 : ℝ)) (s := (1 : ℝ))
    (t := (0 : ℝ)) (z := (0 : ℝ) - 0 * d * w.2) (by norm_num : (0 : ℝ) ≤ 0)
  simp only [AxialFlow.profile, zero_mul, add_zero] at hv
  unfold affineMap velocityMap axialMap
  simp only [zero_mul]
  rw [hv]
  congr 1
  ring

theorem scaled_argument {d : ℝ} (hd : d ≠ 0) (u : ℝ) (w : Transverse × ℝ) :
    d⁻¹ • (affineMap d u w - center u) = SheetMeasures.join w := by
  have ht : ∀ (c : ℝ) (v : Velocity), transverse (c • v) = c • transverse v := by
    intro c v
    apply (WithLp.ext_iff 2).mpr
    rfl
  apply split.injective
  rw [split_apply, split_apply]
  apply Prod.ext
  · change d⁻¹ * (axial (affineMap d u w) - axial (center u)) = axial (SheetMeasures.join w)
    simp only [affineMap, center, PlaneChart.axial_join]
    change d⁻¹ * (u + d * w.2 - u) = w.2
    field_simp
    ring
  · rw [ht, PlaneChart.transverse_sub]
    simp only [affineMap, center, PlaneChart.transverse_join, sub_zero, smul_smul,
      inv_mul_cancel₀ hd, one_smul]
    exact (PlaneChart.transverse_join w.1 w.2).symm

theorem gaussian_coordinate {d : ℝ} (hd : 0 < d) (c b u : ℝ) (w : Transverse × ℝ) :
    d ^ 3 * GaussianFrequency.density c b d (center u) (affineMap d u w) =
      c * Real.exp (-b * ‖SheetMeasures.join w‖ ^ 2) := by
  unfold GaussianFrequency.density JetThermalLaw.scaled JetGaussianMoments.kernel
  rw [scaled_argument hd.ne']
  field_simp

theorem gaussian_parameter_bound {c b : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b)
    (w : Transverse × ℝ) :
    c * Real.exp (-b * ‖SheetMeasures.join w‖ ^ 2) ≤
      (c * (Real.pi * Real.sqrt Real.pi)) * JetGaussianProduct.density w := by
  have he : Real.exp (-b * ‖SheetMeasures.join w‖ ^ 2) ≤
      Real.exp (-‖SheetMeasures.join w‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖SheetMeasures.join w‖]
  calc
    _ ≤ c * Real.exp (-‖SheetMeasures.join w‖ ^ 2) := mul_le_mul_of_nonneg_left he hc
    _ = _ := by rw [JetGaussianProduct.density_eq]; field_simp

theorem measure_domination {c b d : ℝ} (hc : 0 ≤ c) (hb : 1 ≤ b) (hd : 0 < d) (u : ℝ) :
    volume.withDensity (fun v => ENNReal.ofReal (GaussianFrequency.density c b d (center u) v)) ≤
      ENNReal.ofReal (c * (Real.pi * Real.sqrt Real.pi)) •
        SheetMeasures.sheetLaw d (JetAxialLaw.law u 0 0 1 d 0 0) := by
  have hf : Measurable (fun v => ENNReal.ofReal (GaussianFrequency.density c b d (center u) v)) := by
    unfold GaussianFrequency.density JetThermalLaw.scaled JetGaussianMoments.kernel
    fun_prop
  have hmap := JetCoreMeasure.map_withDensity (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) hd
    (by norm_num : (0 : ℝ) ≤ 0) u 0 hf
  have hmeas := (velocity_measurePreserving (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) hd
    (by norm_num : (0 : ℝ) ≤ 0) u 0).measurable
  rw [← hmap, ← JetGaussianProduct.parameterLaw_map (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) hd (by norm_num : (0 : ℝ) ≤ 0),
    ← Measure.map_smul _ hmeas.aemeasurable]
  apply Measure.map_mono _ hmeas
  rw [parameterMeasure_eq (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) ≤ 0)]
  have hj : (fun w : Transverse × ℝ => ENNReal.ofReal
      (d ^ 2 * JetCoreJacobian.jacobian u 0 0 1 d 0 0 w.2)) =
      (fun _ => ENNReal.ofReal (d ^ 3)) := by
    funext w
    simp only [JetCoreJacobian.jacobian, zero_mul, add_zero, div_one]
    congr 1
  rw [hj]
  have hfg : Measurable (fun w => ENNReal.ofReal
      (GaussianFrequency.density c b d (center u) (velocityMap u 0 0 1 d 0 0 w))) := hf.comp hmeas
  rw [← withDensity_mul _ measurable_const hfg, JetGaussianProduct.parameterLaw_density]
  have hg : Measurable (fun w => ENNReal.ofReal (JetGaussianProduct.density w)) := by
    unfold JetGaussianProduct.density GaussianDiskMixture.gaussianDensity
    fun_prop
  rw [← withDensity_smul _ hg]
  apply withDensity_mono
  filter_upwards [] with w
  change ENNReal.ofReal (d ^ 3) * _ ≤ ENNReal.ofReal (c * (Real.pi * Real.sqrt Real.pi)) * _
  rw [← ENNReal.ofReal_mul (pow_nonneg hd.le _),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ c * (Real.pi * Real.sqrt Real.pi)),
    ← affineMap_eq, gaussian_coordinate hd]
  exact ENNReal.ofReal_le_ofReal (gaussian_parameter_bound hc hb w)

end BoltzmannNonuniqueness.JetAffineSheet

end

end

section

/-! # Removing the annular margins in local thermal L1 -/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetGeometry

def scaleShell (η μ : ℝ) : Set Transverse := {y | μ < ‖y‖ ∧ ‖y‖ < Real.exp η*μ}

theorem measurableSet_scaleShell (η μ : ℝ) : MeasurableSet (scaleShell η μ) :=
  (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem ae_norm_ne (a : ℝ) : ∀ᵐ y : Transverse, ‖y‖ ≠ a := by
  apply ae_iff.mpr
  have he : {y : Transverse | ¬‖y‖ ≠ a} = sphere 0 a := by
    ext y
    simp only [not_not,mem_ofPred_eq,mem_sphere,dist_zero_right]
  rw [he]
  exact Measure.addHaar_sphere volume 0 a

private theorem indicator_one_abs_le {X : Type*} (s : Set X) (x : X) :
    |s.indicator (fun _ => (1:ℝ)) x| ≤ 1 := by
  by_cases h : x ∈ s
  · simp only [indicator_of_mem h,abs_one,le_refl]
  · simp only [indicator_of_notMem h,abs_zero,zero_le_one]

theorem ae_annular_indicator_tendsto {r s d : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    (η t : ℝ) (Ω : Set Transverse) :
    ∀ᵐ p : Transverse × (Transverse × ℝ) ∂(volume.restrict Ω).prod
      ((volume : Measure Transverse).prod volume),
      Tendsto (fun n => |(annularCore η (r n*s n)).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))-
        (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1| *
        JetThermalKernel.J (SheetMeasures.join p.2)) atTop (𝓝 0) := by
  have hy : ∀ᵐ y ∂(volume : Measure Transverse).restrict Ω,
      ‖y‖ ≠ μ ∧ ‖y‖ ≠ Real.exp η*μ :=
    ae_restrict_of_ae ((ae_norm_ne μ).and (ae_norm_ne (Real.exp η*μ)))
  have hp : ∀ᵐ p : Transverse × (Transverse × ℝ) ∂((volume : Measure Transverse).restrict Ω).prod
      ((volume : Measure Transverse).prod volume),
      ‖p.1‖ ≠ μ ∧ ‖p.1‖ ≠ Real.exp η*μ :=
    (Measure.quasiMeasurePreserving_fst (ν := (volume : Measure Transverse).prod volume)).ae hy
  filter_upwards [hp] with p hp
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_annularCore_dilation hr hrlim hslim hdlim η t p.1 p.2.1 hp.1 hp.2]
    with n hn
  have he : (annularCore η (r n*s n)).indicator (fun _ => (1:ℝ))
      (r n • (p.1-t • (d n • p.2.1))) =
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1 := by
    by_cases h : μ < ‖p.1‖ ∧ ‖p.1‖ < Real.exp η*μ
    · rw [indicator_of_mem (hn.mpr h),indicator_of_mem (show p.1 ∈ scaleShell η μ from h)]
    · rw [indicator_of_notMem (fun h' => h (hn.mp h')),
        indicator_of_notMem (show p.1 ∉ scaleShell η μ from h)]
  simp only [he,sub_self,abs_zero,zero_mul]

theorem annular_indicator_L1_tendsto {r s d : ℕ → ℝ} {μ : ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop (𝓝 0))
    (hslim : Tendsto s atTop (𝓝 μ)) (hdlim : Tendsto d atTop (𝓝 0))
    (η t : ℝ) (Ω : Set Transverse) (hΩ : volume Ω < ⊤) :
    Tendsto (fun n => ∫ p : Transverse × (Transverse × ℝ),
      |(annularCore η (r n*s n)).indicator (fun _ => (1:ℝ))
          (r n • (p.1-t • (d n • p.2.1))) -
        (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1| *
      JetThermalKernel.J (SheetMeasures.join p.2)
      ∂(volume.restrict Ω).prod ((volume : Measure Transverse).prod volume))
      atTop (𝓝 0) := by
  let _ : IsFiniteMeasure ((volume : Measure Transverse).restrict Ω) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hΩ⟩
  have hm (n) : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (annularCore η (r n*s n)).indicator (fun _ => (1:ℝ))
        (r n • (p.1-t • (d n • p.2.1)))) :=
    (measurable_const.indicator (JetMaskMeasure.measurableSet_annularCore η (r n*s n))).comp
      (by fun_prop)
  have hshell : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1) :=
    (measurable_const.indicator (measurableSet_scaleShell η μ)).comp measurable_fst
  have hJ := (HotRectangleDensity.join_measurePreserving.integrable_comp_of_integrable
    JetThermalKernel.J_integrable).comp_snd ((volume : Measure Transverse).restrict Ω)
  have hmJ : Measurable (fun p : Transverse × (Transverse × ℝ) =>
      JetThermalKernel.J (SheetMeasures.join p.2)) :=
    (JetThermalKernel.J_smooth.continuous.measurable.comp SheetMeasures.join.measurable).comp measurable_snd
  have hl := tendsto_integral_of_dominated_convergence
    (μ := (volume.restrict Ω).prod ((volume : Measure Transverse).prod volume))
    (F := fun n p => |(annularCore η (r n*s n)).indicator (fun _ => (1:ℝ))
      (r n • (p.1-t • (d n • p.2.1)))-
      (scaleShell η μ).indicator (fun _ => (1:ℝ)) p.1| *
      JetThermalKernel.J (SheetMeasures.join p.2)) (f := fun _ => (0:ℝ))
    (fun p => 2*JetThermalKernel.J (SheetMeasures.join p.2))
    (fun n => (((hm n).sub hshell).abs.mul hmJ).aestronglyMeasurable)
    (hJ.const_mul 2) ?_ ?_
  · simpa only [integral_zero] using hl
  · intro n
    filter_upwards [] with p
    change ‖|_ - _| *JetThermalKernel.J (SheetMeasures.join p.2)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (JetThermalKernel.J_nonneg _))]
    apply mul_le_mul_of_nonneg_right _ (JetThermalKernel.J_nonneg _)
    exact (abs_sub _ _).trans ((add_le_add (indicator_one_abs_le _ _)
      (indicator_one_abs_le _ _)).trans (by norm_num))
  · exact ae_annular_indicator_tendsto hr hrlim hslim hdlim η t Ω

end BoltzmannNonuniqueness.JetGeometry

end

end

section

/-! # The Gaussian remainder has the smaller sheet amplitude d/s² -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.JetBarrier
open BoltzmannNonuniqueness.JetSupersolution
open BoltzmannNonuniqueness.JetBarrierCollision
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetRemainderSheet

def remainder (η K α γ s d t : ℝ) (a : Bool) (x : Space) (v : Velocity) : ℝ :=
  epsilon K s d * barrier η K α γ s d t a (x, v)

def amplitude (η K α γ s d t : ℝ) (a : Bool) (x : Space) : ℝ :=
  (epsilon K s d * massScale η K α γ s d t a x) * (Real.pi * Real.sqrt Real.pi)

def uniformConstant (K : ℝ) : ℝ :=
  JetComparisonCoefficient.coefficient K * Real.exp 4 * JetThermalKernel.bound * K *
    (Real.pi * Real.sqrt Real.pi)

theorem remainder_eq {d : ℝ} (hd : 0 < d) (η K α γ s t : ℝ)
    (a : Bool) (x : Space) (v : Velocity) :
    remainder η K α γ s d t a x v =
      GaussianFrequency.density (epsilon K s d * massScale η K α γ s d t a x) (2 - t) d
        (JetAffineSheet.center (AxialFlow.velocity (sign a) α γ s t x.2)) v := by
  rw [remainder, barrier_eq_density hd]
  unfold GaussianFrequency.density centerVelocity JetAffineSheet.center
  ring

theorem measure_domination {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) :
    volume.withDensity (fun v => ENNReal.ofReal (remainder η K α γ s d t a x v)) ≤
      ENNReal.ofReal (amplitude η K α γ s d t a x) •
        SheetMeasures.sheetLaw d
          (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0) := by
  simp_rw [remainder_eq hd]
  exact JetAffineSheet.measure_domination
    (mul_nonneg (epsilon_nonneg hK hs hd) (massScale_nonneg hK hs η α γ d t a x))
    (by linarith) hd _

theorem amplitude_bound {K s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (η α γ : ℝ) (a : Bool) (x : Space) :
    amplitude η K α γ s d t a x ≤ uniformConstant K * (d / s ^ 2) := by
  have hm := massScale_le hK hs hd ht htmax η α γ a x
  have he := epsilon_nonneg hK hs hd
  calc
    _ ≤ (epsilon K s d * (Real.exp 4 * JetThermalKernel.bound * (K / s))) *
        (Real.pi * Real.sqrt Real.pi) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm he) (by positivity)
    _ = _ := by unfold epsilon uniformConstant; field_simp

theorem axial_moment {α d : ℝ} (hα : 0 ≤ α) (hd : 0 < d) (hdmax : d ≤ 1 / 16)
    (γ s t z : ℝ) (a : Bool) :
    SheetMeasures.AxialMoment (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t z) 0 0 1 d 0 0)
      (2 * Real.exp (16 * (1 + α) ^ 2)) := by
  have hm := JetAxialLaw.moment (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 0)
    (by norm_num : (0 : ℝ) < 1) hd hdmax (by norm_num : (0 : ℝ) ≤ 0)
    (AxialFlow.velocity (sign a) α γ s t z) 0
  refine ⟨hm.integrable, hm.bound.trans ?_⟩
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  have hu := AxialTransport.velocity_abs_le (σ := sign a) (γ := γ) (s := s) (t := t) (z := z) hα
  rw [hsiga] at hu
  simp only [add_zero]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (by norm_num)
  nlinarith [abs_nonneg (AxialFlow.velocity (sign a) α γ s t z), sq_abs (AxialFlow.velocity (sign a) α γ s t z)]

theorem normalized_gain_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 ≤ α)
    (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16) (htmax : t ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool) (x : Space)
    {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain
      (volume.withDensity (fun p => ENNReal.ofReal (remainder η K α γ s d t a x p))) q v ≤
      ENNReal.ofReal (amplitude η K α γ s d t a x) *
        SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2)) := by
  have hp := JetAxialLaw.probability (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0
  have he : SheetClass.IsElementary (2 * Real.exp (16 * (1 + α) ^ 2))
      (SheetMeasures.sheetLaw d
        (JetAxialLaw.law (AxialFlow.velocity (sign a) α γ s t x.2) 0 0 1 d 0 0)) :=
    ⟨d, _, hd.le, by linarith, hp, axial_moment hα hd hdmax γ s t x.2 a, rfl⟩
  apply (chartGain_mono_measure (measure_domination hK hs hd htmax η α γ a x) _ v).trans
  rw [chartGain_smul_measure]
  exact mul_le_mul' le_rfl (SheetClass.elementary_bound hq₁ hq₂ he hv)

end BoltzmannNonuniqueness.JetRemainderSheet

end

end

section

/-! # Mixed gain of the complete cold supersolution -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetPrototype
open BoltzmannNonuniqueness.ChartKernel

namespace BoltzmannNonuniqueness.JetEnvelopeGain

def amplitude (η K α γ s d t : ℝ) (a : Bool) (x : Space) : ℝ :=
  JetCoreSheet.amplitude K α γ s t + JetRemainderSheet.amplitude η K α γ s d t a x

theorem measure_eq {K s d : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (η α γ t : ℝ) (a : Bool) (x : Space) :
    volume.withDensity (fun v => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, v))) =
      volume.withDensity (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) +
      volume.withDensity (fun v => ENNReal.ofReal (JetRemainderSheet.remainder η K α γ s d t a x v)) := by
  have heq : (fun v => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, v))) =
      (fun v => ENNReal.ofReal (JetFreeTransport.free η K α γ s d t a (x, v))) +
      (fun v => ENNReal.ofReal (JetRemainderSheet.remainder η K α γ s d t a x v)) := by
    funext v
    exact ENNReal.ofReal_add (JetFreeTransport.free_nonneg hK hs.le hd.le η α γ t a (x, v))
      (mul_nonneg (JetSupersolution.epsilon_nonneg hK hs hd)
        (JetBarrier.barrier_nonneg hK hs.le hd.le η α γ t a (x, v)))
  rw [heq, withDensity_add_left]
  exact ((JetFreeTransport.measurable_free η K α γ s d t a).comp
    (measurable_const.prodMk measurable_id)).ennreal_ofReal

theorem normalized_gain_bound {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α)
    (hγ : 0 < γ) (hs : 0 < s) (hd : 0 < d) (hdmax : d ≤ 1 / 16)
    (ht : 0 ≤ t) (htmax : t ≤ 1) (hq₁ : 1 < q) (hq₂ : q < 2)
    (η : ℝ) (a : Bool) (x : Space) {v : Velocity} (hv : transverse v ≠ 0) :
    normalizedChartGain
      (volume.withDensity (fun p => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, p)))) q v ≤
      ENNReal.ofReal (amplitude η K α γ s d t a x) *
        SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2)) := by
  have hc := JetCoreSheet.normalized_gain_bound hK hα hγ hs hd hdmax ht hq₁ hq₂ η a x hv
  have hr := JetRemainderSheet.normalized_gain_bound (γ := γ) hK hα.le hs hd hdmax htmax hq₁ hq₂ η a x hv
  have hsiga : |sign a| = 1 := by cases a <;> norm_num [sign]
  rw [hsiga] at hc
  have ha := JetCoreSheet.amplitude_nonneg hK hs ht α γ
  have hb : 0 ≤ JetRemainderSheet.amplitude η K α γ s d t a x := by
    unfold JetRemainderSheet.amplitude
    have := JetSupersolution.epsilon_nonneg hK hs hd
    have := JetBarrierCollision.massScale_nonneg hK hs η α γ d t a x
    positivity
  unfold normalizedChartGain
  rw [measure_eq hK hs hd, chartGain_add_measure]
  exact (add_le_add hc hr).trans_eq (by rw [← add_mul, ← ENNReal.ofReal_add ha hb]; rfl)

theorem amplitude_bound {K α γ s d t : ℝ} (hK : 0 ≤ K) (hs : 0 < s) (hd : 0 < d)
    (ht : 0 < t) (htmax : t ≤ 1) (hsmall : d * (s + t) ≤ s ^ 2)
    (η : ℝ) (a : Bool) (x : Space) :
    amplitude η K α γ s d t a x ≤
      (K * max 1 (α * γ)⁻¹ * JetGaussianProduct.coefficient + JetRemainderSheet.uniformConstant K) /
        (s + t) := by
  have hr := JetRemainderSheet.amplitude_bound hK hs hd ht htmax η α γ a x
  have hscale : d / s ^ 2 ≤ 1 / (s + t) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hs) (by positivity : 0 < s + t)).mpr
    simpa only [one_mul] using hsmall
  have hC : 0 ≤ JetRemainderSheet.uniformConstant K := by
    unfold JetRemainderSheet.uniformConstant
    have := JetComparisonCoefficient.coefficient_ge_one hK
    have := JetThermalKernel.bound_pos
    positivity
  have hrs : JetRemainderSheet.amplitude η K α γ s d t a x ≤
      JetRemainderSheet.uniformConstant K / (s + t) := hr.trans (by
    simpa only [div_eq_mul_inv, one_mul] using (mul_le_mul_of_nonneg_left hscale hC))
  calc
    _ ≤ JetCoreSheet.amplitude K α γ s t + JetRemainderSheet.uniformConstant K / (s + t) :=
      add_le_add le_rfl hrs
    _ = _ := by unfold JetCoreSheet.amplitude; ring


theorem gain_bound (hcarleman : Published.GPV2009CarlemanInput)
    {K α γ s d t q : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s)
    (hd : 0 < d) (hdmax : d ≤ 1 / 16) (ht : 0 ≤ t) (htmax : t ≤ 1)
    (hq₁ : 1 < q) (hq₂ : q < 2) (η : ℝ) (a : Bool) (x : Space) :
    ∀ᵐ v : Velocity, nonnegativeGain
      (fun p => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, p)))
      (fun p => ENNReal.ofReal (H q p)) v ≤
      ENNReal.ofReal (H q v) * (ENNReal.ofReal (amplitude η K α γ s d t a x) *
        SheetTotal.bound q (2 * Real.exp (16 * (1 + α) ^ 2))) := by
  have hf : Measurable (fun p => ENNReal.ofReal (JetSupersolution.U η K α γ s d t a (x, p))) :=
    (JetSupersolution.measurable_velocity hd η K α γ s t a x).ennreal_ofReal
  apply nonnegativeGain_le_of_chartGain hcarleman hf ((measurable_H q).ennreal_ofReal)
  filter_upwards [SheetApplication.ae_transverse_ne_zero] with v hv
  rw [SheetApplication.gain_H_eq]
  exact mul_le_mul' le_rfl (normalized_gain_bound hK hα hγ hs hd hdmax ht htmax hq₁ hq₂ η a x hv)

theorem thermal_width_le {d₀ s : ℝ} (hd₀max : d₀ ≤ 1) (hs : 0 ≤ s) (hsmax : s ≤ 1 / 8) :
    d₀ * s ^ 10 ≤ 1 / 16 := by
  calc
    _ ≤ 1 * (1 / 8 : ℝ) ^ 10 := mul_le_mul hd₀max (pow_le_pow_left₀ hs hsmax 10)
      (pow_nonneg hs _) (by norm_num)
    _ ≤ _ := by norm_num

theorem thermal_scale_small {d₀ s t : ℝ} (hd₀max : d₀ ≤ 1)
    (hs : 0 < s) (hsmax : s ≤ 1 / 8) (ht : 0 ≤ t) (htmax : t ≤ 1 / 32) :
    (d₀ * s ^ 10) * (s + t) ≤ s ^ 2 := by
  have hp : s ^ 8 ≤ 1 := pow_le_one₀ hs.le (by linarith)
  have hprod : d₀ * s ^ 8 ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hd₀max hp (pow_nonneg hs.le _) (by norm_num)
      _ = _ := one_mul 1
  have hprod' : d₀ * s ^ 8 * (s + t) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul hprod (by linarith) (by positivity) (by norm_num)
      _ = _ := one_mul 1
  calc
    _ = s ^ 2 * (d₀ * s ^ 8 * (s + t)) := by ring
    _ ≤ s ^ 2 * 1 := mul_le_mul_of_nonneg_left hprod' (sq_nonneg s)
    _ = _ := mul_one _

end BoltzmannNonuniqueness.JetEnvelopeGain

end

end

end OAI
