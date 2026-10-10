import OAI.MathematicalPhysics.Boltzmann.Branching.FiveGainRank
import OAI.MathematicalPhysics.Boltzmann.Branching.RedundantParameterSupport
import OAI.MathematicalPhysics.Boltzmann.Collision.WeightLocalL1
import OAI.MathematicalPhysics.Boltzmann.Jets.CoreDensityTranslation
import OAI.MathematicalPhysics.Boltzmann.Jets.FreeCoreGainKernel

namespace OAI

section

/-! # The actual free-core normalized gain as a six-parameter integral -/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.RedundantPlane
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

def parameterPoint (α γ s d t : ℝ) (a : Bool) (x : JetPrototype.Space)
    (v : Velocity) (w L : FiveGainMap.V) : Velocity :=
  v+crossVelocity v (thermalPoint α γ s d t a x w) L

def parameterDensity (η K α γ s d t q : ℝ) (a : Bool) (x : JetPrototype.Space)
    (v : Velocity) (w L : FiveGainMap.V) : ℝ≥0∞ :=
  2 * ENNReal.ofReal (thermalWeight η K α γ s d t a x w) *
    normalDensity (normalCoefficient v (thermalPoint α γ s d t a x w) L) *
    ENNReal.ofReal (H q (parameterPoint α γ s d t a x v w L)/H q v)

theorem normalizedCoreKernel_parameter_integral {α γ s d t : ℝ}
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η K q : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity)
    {f : Velocity → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ξ, f ξ ∂normalizedCoreKernel η K α γ s d q a ((t,x),v)) =
      ∫⁻ w : FiveGainMap.V, ∫⁻ L : FiveGainMap.V,
        parameterDensity η K α γ s d t q a x v w L *
          f (parameterPoint α γ s d t a x v w L) := by
  let F : Velocity × FiveGainMap.V → ℝ≥0∞ := fun p =>
    normalDensity (normalCoefficient v p.1 p.2) *
      (ENNReal.ofReal (H q (v+crossVelocity v p.1 p.2)/H q v)*
        f (v+crossVelocity v p.1 p.2))
  have hpoint := measurable_redundant_point v
  have hF : Measurable F :=
    (measurable_normalDensity.comp (measurable_normalCoefficient v)).mul
      (((((ChartKernel.measurable_H q).comp hpoint).div_const _).ennreal_ofReal).mul
        (hf.comp hpoint))
  have houter : Measurable (fun p : Velocity => ∫⁻ L : FiveGainMap.V, F (p,L)) :=
    hF.lintegral_prod_right
  have hc : ∀ᵐ p ∂coreKernel η K α γ s d a (t,x), PlaneChart.normal v p ≠ 0 := by
    rw [coreKernel_apply]
    exact (withDensity_absolutelyContinuous volume _).ae_le (ae_normal_ne v)
  have hg := inputKernel_redundant (coreKernel η K α γ s d a) q ((t,x),v) hc hf
  change (∫⁻ ξ, f ξ ∂normalizedCoreKernel η K α γ s d q a ((t,x),v)) =
    2 * ∫⁻ p, ∫⁻ L : FiveGainMap.V, F (p,L) ∂volume ∂coreKernel η K α γ s d a (t,x) at hg
  rw [hg,coreKernel_apply,core_thermal_integral hα hγ hs hd ht η K a x houter,
    ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  apply lintegral_congr
  intro w
  rw [← mul_assoc,← lintegral_const_mul' _ _
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)]
  apply lintegral_congr
  intro L
  dsimp only [F,parameterDensity,parameterPoint]
  ac_rfl

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # Measurability and bounds for the actual six-parameter gain density -/

noncomputable section

open MeasureTheory
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.RedundantPlane
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem measurable_parameterPoint {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t) (a : Bool) (x : JetPrototype.Space) (v : Velocity) :
    Measurable (fun p : FiveGainMap.V × FiveGainMap.V => parameterPoint α γ s d t a x v p.1 p.2) := by
  let k : FiveGainMap.V × FiveGainMap.V → Velocity × FiveGainMap.V :=
    fun p => (thermalPoint α γ s d t a x p.1,p.2)
  have hk : Measurable k :=
    ((thermalPoint_measurable hα hγ hs hd ht a x).comp measurable_fst).prodMk measurable_snd
  simpa only [Function.comp_def,k,parameterPoint] using (measurable_redundant_point v).comp hk

theorem measurable_parameterDensity {α γ s d t : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hs : 0 < s) (hd : 0 < d) (ht : 0 ≤ t)
    (η K q : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity) :
    Measurable (fun p : FiveGainMap.V × FiveGainMap.V =>
      parameterDensity η K α γ s d t q a x v p.1 p.2) := by
  have hp : Measurable (fun p : FiveGainMap.V × FiveGainMap.V =>
      (thermalPoint α γ s d t a x p.1,p.2)) :=
    ((thermalPoint_measurable hα hγ hs hd ht a x).comp measurable_fst).prodMk measurable_snd
  exact ((measurable_const.mul
    (((thermalWeight_measurable hα hγ hs ht η K d a x).comp measurable_fst).ennreal_ofReal)).mul
    (measurable_normalDensity.comp ((measurable_normalCoefficient v).comp hp))).mul
    ((((ChartKernel.measurable_H q).comp
      (measurable_parameterPoint hα hγ hs hd ht a x v)).div_const _).ennreal_ofReal)

theorem parameterDensity_bound {K α γ s t q b V : ℝ} (hK : 0 ≤ K)
    (hα : 0 < α) (hγ : 0 < γ) (hs : 0 < s) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hb : 0 < b) (hV : 0 ≤ V)
    (η d : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity)
    (w L : FiveGainMap.V) (hv : ‖v‖ ≤ V)
    (hξ : b ≤ ‖transverse (parameterPoint α γ s d t a x v w L)‖) :
    parameterDensity η K α γ s d t q a x v w L ≤
      2 * ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/(s+t))*JetThermalKernel.bound) *
        ENNReal.ofReal ((1+b^(-q))/compactLower V) := by
  unfold parameterDensity
  have hw := ENNReal.ofReal_le_ofReal (thermalWeight_bound hK hα hγ hs ht η d a x w)
  have hn := normalDensity_le_one (normalCoefficient v (thermalPoint α γ s d t a x w) L)
  have hr := ENNReal.ofReal_le_ofReal (H_ratio_le_offAxis hq hb hV hv hξ)
  calc
    _ ≤ (2*ENNReal.ofReal (((K*max 1 (α*γ)⁻¹)/(s+t))*JetThermalKernel.bound))*1*
        ENNReal.ofReal ((1+b^(-q))/compactLower V) :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hw) hn) hr
    _ = _ := by rw [mul_one]

theorem parameterDensity_zero_of_thermal {η K α γ s d t q : ℝ}
    (a : Bool) (x : JetPrototype.Space) (v : Velocity) (w L : FiveGainMap.V)
    (hw : 1 ≤ ‖WithLp.toLp 2 w‖) :
    parameterDensity η K α γ s d t q a x v w L = 0 := by
  simp only [parameterDensity,thermalWeight_zero a x hw,ENNReal.ofReal_zero,mul_zero,zero_mul]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

section

/-! # The parameterized gain and its thermal collision map -/

noncomputable section

open scoped Matrix
open BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetCoreDensity

namespace BoltzmannNonuniqueness.JetCoreSheet

theorem parameterPoint_eq_center (α γ s d t : ℝ) (a : Bool)
    (x : JetPrototype.Space) (xv : FiveGainMap.V) (hx : xv 2 = x.2)
    (v : Velocity) (w L : FiveGainMap.V) :
    WithLp.ofLp (parameterPoint α γ s d t a x v w L) =
      WithLp.ofLp v + (WithLp.ofLp v-
        FiveGainMap.thermalCenter (JetPrototype.sign a) α γ s d t xv w) ⨯₃ L := by
  unfold parameterPoint RedundantPlane.crossVelocity RedundantPlane.normalVector
  rw [thermalPoint_eq_center α γ s d t a x xv w hx]
  rfl

def jetPosition (x : FiveGainMap.V) : JetPrototype.Space :=
  (transverse (WithLp.toLp 2 x),x 2)

theorem thermalStep_eq_parameterPoint (α γ s d t : ℝ) (a : Bool)
    (L w : FiveGainMap.V) (z : FiveGainMap.State) :
    FiveGainMap.thermalStep (JetPrototype.sign a) α γ s d t L w z =
      (t,z.2.1-(z.1-t) • z.2.2,
        WithLp.ofLp (parameterPoint α γ s d t a
          (jetPosition (z.2.1-(z.1-t) • z.2.2)) (WithLp.toLp 2 z.2.2) w L)) := by
  rw [parameterPoint_eq_center α γ s d t a _ (z.2.1-(z.1-t) • z.2.2) rfl]
  rfl

theorem parameterPoint_dilation {r α γ s t : ℝ} (hr : 0 < r)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hs : 0 < s) (ht : 0 ≤ t)
    (d : ℝ) (a : Bool) (x : JetPrototype.Space) (v : Velocity) (w L : FiveGainMap.V) :
    parameterPoint α γ (r*s) d (r*t) a (r • x) v w L =
      parameterPoint α γ s d t a x v w L := by
  have hp : thermalPoint α γ (r*s) d (r*t) a (r • x) w =
      thermalPoint α γ s d t a x w :=
    JetCoreMeasure.velocityMap_dilation hr hα hγ hs ht (JetPrototype.sign a) d x.2
      (thermalCoordinates w)
  simp only [parameterPoint,hp]

end BoltzmannNonuniqueness.JetCoreSheet

end

end

end OAI
