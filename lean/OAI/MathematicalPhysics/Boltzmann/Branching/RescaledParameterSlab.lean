import OAI.MathematicalPhysics.Boltzmann.Branching.DilatedTwoCoreLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.RedundantParameterSupport
import OAI.MathematicalPhysics.Boltzmann.Jets.CoreParameterStep

namespace OAI

section

/-! # The physical dilated gain in bounded thermal and plane parameters -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.RedundantPlane
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

def rescaledParameterDensity (r η K α γ μ d t q : ℝ) (a : Bool) (x : JetPrototype.Space)
    (v : Velocity) (w L : FiveGainMap.V) : ℝ≥0∞ :=
  ENNReal.ofReal r*parameterDensity η K α γ (r*μ) d (r*t) q a (r • x) v w L

theorem rescaledCoreMeasure_parameter_integral {r α γ μ d t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (hd : 0 < d) (ht : 0 ≤ t)
    (η K q : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity)
    (hv : transverse v ≠ 0) {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂rescaledCoreMeasure r η K α γ μ d q a t x v) =
      ∫⁻ w : FiveGainMap.V, ∫⁻ L : FiveGainMap.V,
        rescaledParameterDensity r η K α γ μ d t q a x v w L *
          f (parameterPoint α γ μ d t a x v w L) := by
  rw [rescaledCoreMeasure,ChartKernel.offAxis_apply _ _ hv,lintegral_smul_measure]
  rw [normalizedCoreKernel_parameter_integral hα hγ (mul_pos hr hμ) hd (mul_nonneg hr.le ht)
    η K q a (r • x) v hf]
  simp only [smul_eq_mul]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro w
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro L
  rw [parameterPoint_dilation hr hα hγ hμ ht]
  exact (mul_assoc _ _ _).symm

theorem rescaledParameterDensity_bound {r K α γ μ t q b V : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ)
    (ht : 0 ≤ t) (hq : 0 ≤ q) (hb : 0 < b) (hV : 0 ≤ V)
    (η d : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity) (w L : FiveGainMap.V)
    (hv : ‖v‖ ≤ V) (hξ : b ≤ ‖transverse (parameterPoint α γ μ d t a x v w L)‖) :
    rescaledParameterDensity r η K α γ μ d t q a x v w L ≤
      2 * ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/(μ+t))*JetThermalKernel.bound) *
        ENNReal.ofReal ((1+b^(-q))/compactLower V) := by
  unfold rescaledParameterDensity parameterDensity
  rw [parameterPoint_dilation hr hα.le hγ.le hμ ht]
  have hw : ENNReal.ofReal r*ENNReal.ofReal
      (thermalWeight η K α γ (r*μ) d (r*t) a (r • x) w) ≤
      ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/(μ+t))*JetThermalKernel.bound) := by
    rw [← ENNReal.ofReal_mul hr.le]
    exact ENNReal.ofReal_le_ofReal (dilated_thermalWeight_bound hr hK hα hγ hμ ht η d a x w)
  have hn := normalDensity_le_one
    (normalCoefficient v (thermalPoint α γ (r*μ) d (r*t) a (r • x) w) L)
  have hratio := ENNReal.ofReal_le_ofReal (H_ratio_le_offAxis hq hb hV hv hξ)
  calc
    _ = (2*(ENNReal.ofReal r*ENNReal.ofReal
        (thermalWeight η K α γ (r*μ) d (r*t) a (r • x) w))) *
        normalDensity (normalCoefficient v (thermalPoint α γ (r*μ) d (r*t) a (r • x) w) L) *
        ENNReal.ofReal (H q (parameterPoint α γ μ d t a x v w L)/H q v) := by ac_rfl
    _ ≤ (2*ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/(μ+t))*JetThermalKernel.bound))*1*
        ENNReal.ofReal ((1+b^(-q))/compactLower V) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hw) hn) hratio
    _ = _ := by rw [mul_one]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Uniform compact parameter support for retained physical collisions -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreDensity
open BoltzmannNonuniqueness.RedundantPlane

namespace BoltzmannNonuniqueness.JetCoreSheet

def retainedPlaneBound (α b Vmax : ℝ) : ℝ :=
  (2*Vmax)^2/(b/2)^2+(Vmax+(α+3))^2+1

theorem rescaledParameterDensity_support {r α γ μ d t b Vmax : ℝ}
    (hr : 0 < r) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hμ : 0 < μ) (ht : 0 ≤ t)
    (hd : 0 < d) (hdmax : d ≤ 1) (hb : 0 < b) (hthin : d ≤ b/2) (hV : 0 ≤ Vmax)
    (η K q : ℝ) (color : Bool) (x : JetPrototype.Space) (v : Velocity)
    (w L : FiveGainMap.V) (hv : ‖v‖ ≤ Vmax) (hvtrans : b ≤ ‖transverse v‖)
    (hout : ‖parameterPoint α γ μ d t color x v w L‖ ≤ Vmax)
    (hnonzero : rescaledParameterDensity r η K α γ μ d t q color x v w L ≠ 0) :
    ‖WithLp.toLp 2 w‖ < 1 ∧ ‖WithLp.toLp 2 L‖ ≤ retainedPlaneBound α b Vmax := by
  let p := thermalPoint α γ (r*μ) d (r*t) color (r • x) w
  have hw : ‖WithLp.toLp 2 w‖ < 1 := by
    by_contra h
    have hz := thermalWeight_zero (η := η) (K := K) (α := α) (γ := γ) (s := r*μ)
      (d := d) (t := r*t) color (r • x) (le_of_not_gt h)
    apply hnonzero
    simp only [rescaledParameterDensity,parameterDensity,hz,ENNReal.ofReal_zero,mul_zero,zero_mul]
  have hnormal : normalDensity (normalCoefficient v p L) ≠ 0 := by
    intro hz
    apply hnonzero
    change ENNReal.ofReal r*(2*ENNReal.ofReal _*normalDensity (normalCoefficient v p L)*_) = 0
    rw [hz,mul_zero,zero_mul,mul_zero]
  have hpt : ‖transverse p‖ ≤ d :=
    thermalPoint_transverse_bound hd.le α γ (r*μ) (r*t) color (r • x) w hw.le
  have hp : ‖p‖ ≤ α+3 := thermalPoint_norm_bound hα hd.le hdmax γ (r*μ) (r*t)
    color (r • x) w hw.le
  have hlow : b/2 ≤ ‖v-p‖ := by
    have hdiff := norm_sub_norm_le (transverse v) (transverse p)
    have htrans := LargeOutput.transverse_norm_le (v-p)
    rw [PlaneChart.transverse_sub] at htrans
    linarith
  have hout' : ‖v+crossVelocity v p L‖ ≤ Vmax := by
    have he := parameterPoint_dilation hr hα hγ hμ ht d color x v w L
    change parameterPoint α γ (r*μ) d (r*t) color (r • x) v w L = _ at he
    change ‖parameterPoint α γ (r*μ) d (r*t) color (r • x) v w L‖ ≤ Vmax
    rw [he]
    exact hout
  exact ⟨hw,plane_parameter_bound (half_pos hb) hV (by linarith) v p L hv hp hlow hout' hnormal⟩

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # A common bound for retained physical gain densities on a positive slab -/

noncomputable section

open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.JetCoreSheet

def parameterSlabBound (K α γ q a b V : ℝ) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/a)*JetThermalKernel.bound) *
    ENNReal.ofReal ((1+b^(-q))/compactLower V)

theorem parameterSlabBound_ne_top (K α γ q a b V : ℝ) :
    parameterSlabBound K α γ q a b V ≠ ∞ := by
  unfold parameterSlabBound
  finiteness

theorem rescaledParameterDensity_slab_bound {r K α γ μ t q a b V : ℝ}
    (hr : 0 < r) (hK : 0 ≤ K) (hα : 0 < α) (hγ : 0 < γ) (hμ : 0 < μ)
    (ha : 0 < a) (ht : a ≤ t) (hq : 0 ≤ q) (hb : 0 < b) (hV : 0 ≤ V)
    (η d : ℝ) (sign : Bool) (x : JetPrototype.Space) (v : Velocity) (w L : FiveGainMap.V)
    (hv : ‖v‖ ≤ V) (hξ : b ≤ ‖transverse (parameterPoint α γ μ d t sign x v w L)‖) :
    rescaledParameterDensity r η K α γ μ d t q sign x v w L ≤
      parameterSlabBound K α γ q a b V := by
  apply (rescaledParameterDensity_bound hr hK hα hγ hμ (ha.le.trans ht) hq hb hV
    η d sign x v w L hv hξ).trans
  apply mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)) le_rfl
  apply mul_le_mul_of_nonneg_right _ JetThermalKernel.bound_pos.le
  exact div_le_div_of_nonneg_left
    (mul_nonneg hK (le_max_of_le_left zero_le_one)) ha (by linarith)

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
