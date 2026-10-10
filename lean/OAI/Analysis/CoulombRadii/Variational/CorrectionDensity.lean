import Mathlib
import OAI.Analysis.CoulombRadii.ThomasFermi.ScaledProfile
import OAI.Analysis.CoulombRadii.Packets.CoulombKernel

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace NeutralAtom
open scoped Convolution
open ContinuousLinearMap

theorem coulombKernel_le_one {x : Position} (hx : 1 ≤ ‖x‖) : coulombKernel x ≤ 1 := by
  simpa only [coulombKernel, inv_one] using inv_anti₀ (by norm_num : (0:ℝ)<1) hx

theorem coulombKernel_sq_integrableOn_ball (r : ℝ) :
    IntegrableOn (fun x => (coulombKernel x)^2) (Metric.ball (0 : Position) r) := by
  apply integrableOn_ball_of_norm_le_rpow
    (by simp : 1 ≤ Module.finrank ℝ Position)
    (C := 1) (α := 2) (by norm_num : (2:ℝ) < Module.finrank ℝ Position)
    _ (measurable_coulombKernel.pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simp [coulombKernel, Real.rpow_neg (norm_nonneg x)])

theorem coulombKernel_sub_le {x y : Position} (hx : x ≠ 0) (hy : y ≠ 0) :
    |coulombKernel x-coulombKernel y| ≤
      ‖x-y‖/2*((coulombKernel x)^2+(coulombKernel y)^2) := by
  have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have he : |coulombKernel x-coulombKernel y| =
      |‖y‖-‖x‖| *(‖x‖⁻¹*‖y‖⁻¹) := by
    rw [coulombKernel, coulombKernel, inv_sub_inv hxp.ne' hyp.ne',
      abs_div, abs_mul, abs_of_pos hxp, abs_of_pos hyp]
    simp only [div_eq_mul_inv, mul_inv_rev, mul_comm ‖x‖⁻¹ ‖y‖⁻¹]
  rw [he]
  calc
    |‖y‖-‖x‖| *(‖x‖⁻¹*‖y‖⁻¹) ≤ ‖x-y‖*(‖x‖⁻¹*‖y‖⁻¹) := by
      apply mul_le_mul_of_nonneg_right
      · simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
      · positivity
    _ ≤ _ := by
      have hb : 2*(‖x‖⁻¹*‖y‖⁻¹) ≤ (‖x‖⁻¹)^2+(‖y‖⁻¹)^2 := by
        nlinarith [sq_nonneg (‖x‖⁻¹-‖y‖⁻¹)]
      have hm := mul_le_mul_of_nonneg_left hb (norm_nonneg (x-y))
      dsimp [coulombKernel]
      nlinarith

theorem potentialOf_lipschitz_bound {ρ : Position → ℝ} {A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) (x x' : Position) :
    ‖potentialOf ρ x-potentialOf ρ x'‖ ≤
      (A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+(∫ y, ρ y))*‖x-x'‖ := by
  have hi (z : Position) : Integrable (fun y => coulombKernel (z-y)*ρ y) :=
    (bounded_density_convolution measurable_coulombKernel coulombKernel_nonneg
      (coulombKernel_integrableOn_ball 1) (fun _ => coulombKernel_le_one)
      hρ hpos hA z).1
  have hb (z : Position) := bounded_density_convolution
    (measurable_coulombKernel.pow_const 2) (fun y => sq_nonneg (coulombKernel y))
    (coulombKernel_sq_integrableOn_ball 1)
    (fun y hy => by nlinarith [coulombKernel_le_one hy, coulombKernel_nonneg y])
    hρ hpos hA z
  have hdomi : Integrable (fun y => ‖x-x'‖/2*
      ((coulombKernel (x-y))^2*ρ y+(coulombKernel (x'-y))^2*ρ y)) :=
    ((hb x).1.add (hb x').1).const_mul (‖x-x'‖/2)
  have hdom : ∀ᵐ y : Position ∂volume,
      ‖coulombKernel (x-y)*ρ y-coulombKernel (x'-y)*ρ y‖ ≤
        ‖x-x'‖/2*((coulombKernel (x-y))^2*ρ y+(coulombKernel (x'-y))^2*ρ y) := by
    filter_upwards [volume.ae_ne x, volume.ae_ne x'] with y hy hy'
    rw [← sub_mul, norm_mul, Real.norm_eq_abs (ρ y), abs_of_nonneg (hpos y)]
    have hh := mul_le_mul_of_nonneg_right
      (coulombKernel_sub_le (sub_ne_zero.mpr hy.symm) (sub_ne_zero.mpr hy'.symm)) (hpos y)
    simpa only [sub_sub_sub_cancel_right, Real.norm_eq_abs, mul_add, add_mul, mul_assoc] using hh
  have hh := norm_integral_le_of_norm_le hdomi hdom
  rw [integral_sub (hi x) (hi x'), integral_const_mul,
    integral_add (hb x).1 (hb x').1] at hh
  refine hh.trans ?_
  have hh' := add_le_add (hb x).2 (hb x').2
  nlinarith [mul_le_mul_of_nonneg_left hh' (norm_nonneg (x-x'))]

theorem potentialOf_lipschitz {ρ : Position → ℝ} {A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) :
    ∃ C : NNReal, LipschitzWith C (potentialOf ρ) := by
  let B := A*(∫ y in Metric.ball (0 : Position) 1, (coulombKernel y)^2)+(∫ y, ρ y)
  have hB : 0 ≤ B := by
    exact add_nonneg (mul_nonneg ((hpos 0).trans (hA 0))
      (integral_nonneg (fun y => sq_nonneg _))) (integral_nonneg hpos)
  exact ⟨⟨B,hB⟩, lipschitzWith_iff_norm_sub_le.mpr (potentialOf_lipschitz_bound hρ hpos hA)⟩

theorem potentialOf_continuous {ρ : Position → ℝ} {A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x) (hA : ∀ x, ρ x ≤ A) :
    Continuous (potentialOf ρ) :=
  (potentialOf_lipschitz hρ hpos hA).choose_spec.continuous

theorem translated_kernel_indicator_eq (x : Position) (r : ℝ) :
    (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) =
      (fun y => (Metric.ball (0 : Position) r).indicator coulombKernel (x-y)) := by
  ext y
  have hh : x-y ∈ Metric.ball (0 : Position) r ↔ y ∈ Metric.ball x r := by
    simp only [Metric.mem_ball, dist_eq_norm, sub_zero, norm_sub_rev]
  by_cases hy : y ∈ Metric.ball x r <;> simp [hh, hy]

theorem translated_kernel_indicator_integrable (x : Position) (r : ℝ) :
    Integrable ((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) := by
  rw [translated_kernel_indicator_eq]
  exact (integrable_comp_sub_left
    ((Metric.ball (0 : Position) r).indicator coulombKernel) x).mpr
      ((coulombKernel_integrableOn_ball r).integrable_indicator measurableSet_ball)

theorem translated_kernel_indicator_integral (x : Position) (r : ℝ) :
    (∫ y, (Metric.ball x r).indicator (fun y => coulombKernel (x-y)) y) =
      kernelBallMass r := by
  rw [translated_kernel_indicator_eq, integral_sub_left_eq_self,
    integral_indicator measurableSet_ball]
  rfl

theorem kernelBallMass_nonneg (r : ℝ) : 0 ≤ kernelBallMass r :=
  integral_nonneg (fun _ => coulombKernel_nonneg _)

theorem potential_integrable_and_bound {ρ : Position → ℝ} {x : Position} {r A : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ y, 0 ≤ ρ y) (hr : 0 < r)
    (hloc : ∀ y ∈ Metric.ball x r, ρ y ≤ A) :
    Integrable (fun y => coulombKernel (x-y)*ρ y) ∧
      potentialOf ρ x ≤ A*kernelBallMass r+r⁻¹*(∫ y, ρ y) := by
  let b : Position → ℝ := fun y =>
    A*((Metric.ball x r).indicator (fun y => coulombKernel (x-y))) y+r⁻¹*ρ y
  have hb : Integrable b :=
    ((translated_kernel_indicator_integrable x r).const_mul A).add (hρ.const_mul r⁻¹)
  have hdom : ∀ y, coulombKernel (x-y)*ρ y ≤ b y := by
    intro y
    by_cases hy : y ∈ Metric.ball x r
    · simp only [b, Set.indicator_of_mem hy]
      exact (mul_le_mul_of_nonneg_left (hloc y hy) (coulombKernel_nonneg _)).trans
        (by nlinarith [mul_nonneg (inv_nonneg.mpr hr.le) (hpos y)])
    · simp only [b, Set.indicator_of_notMem hy, mul_zero, zero_add]
      have hd : r ≤ ‖x-y‖ := by
        simpa only [Metric.mem_ball, not_lt, dist_eq_norm, norm_sub_rev] using hy
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hr hd) (hpos y)
  have hprod : AEStronglyMeasurable (fun y => coulombKernel (x-y)*ρ y) volume :=
    ((measurable_coulombKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      hρ.aestronglyMeasurable
  have hi : Integrable (fun y => coulombKernel (x-y)*ρ y) := hb.mono' hprod
    (Filter.Eventually.of_forall (fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hpos y))]
      exact hdom y))
  refine ⟨hi, (integral_mono hi hb hdom).trans_eq ?_⟩
  dsimp [b]
  rw [integral_add ((translated_kernel_indicator_integrable x r).const_mul A) (hρ.const_mul r⁻¹),
    integral_const_mul, integral_const_mul, translated_kernel_indicator_integral]

theorem potential_le_inner_mass {ρ : Position → ℝ} {x : Position} {a : ℝ}
    (hρ : Integrable ρ) (hpos : ∀ y, 0 ≤ ρ y) (hx : x ≠ 0)
    (ha : a ≤ ‖x‖/2) (hsupp : ∀ y, a < ‖y‖ → ρ y = 0) :
    Integrable (fun y => coulombKernel (x-y)*ρ y) ∧
      potentialOf ρ x ≤ (2/‖x‖)*(∫ y, ρ y) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb := hρ.const_mul (2/‖x‖)
  have hdom : ∀ y, coulombKernel (x-y)*ρ y ≤ (2/‖x‖)*ρ y := by
    intro y
    by_cases hy : a < ‖y‖
    · simp [hsupp y hy]
    · have hh : ‖x‖/2 ≤ ‖x-y‖ := by
        have := norm_le_norm_sub_add x y
        linarith [le_of_not_gt hy]
      have hi := inv_anti₀ (half_pos hxpos) hh
      have heq : (‖x‖/2)⁻¹ = 2/‖x‖ := by ring
      rw [heq] at hi
      exact mul_le_mul_of_nonneg_right hi (hpos y)
  have hm : AEStronglyMeasurable (fun y => coulombKernel (x-y)*ρ y) volume :=
    ((measurable_coulombKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
      hρ.aestronglyMeasurable
  have hi := hb.mono' hm (Filter.Eventually.of_forall (fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (coulombKernel_nonneg _) (hpos y))]
    exact hdom y))
  refine ⟨hi, (integral_mono hi hb hdom).trans_eq ?_⟩
  exact integral_const_mul _ _

theorem integral_exterior_inverse_sixth {a : ℝ} (ha : 0 < a) :
    (∫ x : Position in {x | a < ‖x‖}, (‖x‖^6)⁻¹) = 4*Real.pi/(3*a^3) := by
  rw [radial_integral_exterior (fun r => (r^6)⁻¹) ha.le]
  have heq : (∫ r : ℝ in Set.Ioi a, r^2*(r^6)⁻¹) =
      ∫ r : ℝ in Set.Ioi a, r^(-4 : ℝ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := ha.trans hr
    change r^2*(r^6)⁻¹ = r^(-4 : ℝ)
    norm_num [Real.rpow_neg hr0.le]
    field_simp
  rw [heq, integral_Ioi_rpow_of_lt (by norm_num : (-4:ℝ)< -1) ha]
  norm_num
  ring

theorem integrable_exterior_inverse_sixth {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : Position => (‖x‖^6)⁻¹) {x | a < ‖x‖} := by
  rw [radial_integrable_exterior (fun r => (r^6)⁻¹) ha.le]
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4:ℝ)< -1) ha).congr_fun ?_
    measurableSet_Ioi
  intro r hr
  have hr0 : 0 < r := ha.trans hr
  change r^(-4 : ℝ) = r^2*(r^6)⁻¹
  norm_num [Real.rpow_neg hr0.le]
  field_simp

theorem potentialOf_nonneg {ρ : Position → ℝ} (hρ : ∀ y, 0 ≤ ρ y) (x : Position) :
    0 ≤ potentialOf ρ x := integral_nonneg (fun y => mul_nonneg (coulombKernel_nonneg _) (hρ y))

theorem inner_potential_tendsto_zero {ρ : ℕ → Position → ℝ} {a : ℕ → ℝ}
    (hi : ∀ n, Integrable (ρ n)) (hp : ∀ n y, 0 ≤ ρ n y)
    (hsupp : ∀ n y, a n < ‖y‖ → ρ n y = 0)
    (ha : Tendsto a atTop (𝓝 0)) (hmass : Tendsto (fun n => ∫ y, ρ n y) atTop (𝓝 0))
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => potentialOf (ρ n) x) atTop (𝓝 0) := by
  have he := ha.eventually (gt_mem_nhds (half_pos (norm_pos_iff.mpr hx)))
  apply squeeze_zero' (Filter.Eventually.of_forall (fun n => potentialOf_nonneg (hp n) x))
    (he.mono (fun n hn => (potential_le_inner_mass (hi n) (hp n) hx hn.le (hsupp n)).2))
  simpa using hmass.const_mul (2/‖x‖)

theorem potential_tendsto_zero_of_local_bound {ρ : ℕ → Position → ℝ} {A : ℕ → ℝ}
    {x : Position} {r : ℝ} (hr : 0 < r)
    (hi : ∀ n, Integrable (ρ n)) (hp : ∀ n y, 0 ≤ ρ n y)
    (hloc : ∀ n y, y ∈ Metric.ball x r → ρ n y ≤ A n)
    (hA : Tendsto A atTop (𝓝 0)) (hmass : Tendsto (fun n => ∫ y, ρ n y) atTop (𝓝 0)) :
    Tendsto (fun n => potentialOf (ρ n) x) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => potentialOf_nonneg (hp n) x)
    (fun n => (potential_integrable_and_bound (hi n) (hp n) hr (hloc n)).2)
  simpa using (hA.mul_const (kernelBallMass r)).add (hmass.const_mul r⁻¹)

def correctionDensity (q a S : ℝ) (x : Position) : ℝ :=
  {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S}.indicator (fun y => (q^8)⁻¹*(‖y‖^6)⁻¹) x

theorem correctionDensity_nonneg (q a S : ℝ) (x : Position) :
    0 ≤ correctionDensity q a S x := by
  apply Set.indicator_nonneg
  intro y hy
  positivity

theorem correctionDensity_measurable (q a S : ℝ) : Measurable (correctionDensity q a S) := by
  apply Measurable.indicator
    (measurable_const.mul ((measurable_norm.pow_const 6).inv))
  exact (isClosed_le continuous_const continuous_norm).measurableSet.inter
    (isClosed_le continuous_norm continuous_const).measurableSet

theorem correctionDensity_le_exterior {q a S : ℝ} :
    correctionDensity q a S ≤ᵐ[volume]
      (fun y : Position => (q^8)⁻¹*({y : Position | a < ‖y‖}.indicator (fun y => (‖y‖^6)⁻¹) y)) := by
  have hsphere : ∀ᵐ y : Position, ‖y‖ ≠ a := by
    rw [ae_iff]
    convert Measure.addHaar_sphere volume (0 : Position) a using 1
    congr 1
    ext y
    simp
  filter_upwards [hsphere] with y hy
  by_cases he : a ≤ ‖y‖ ∧ ‖y‖ ≤ S
  · have hm : a < ‖y‖ := lt_of_le_of_ne he.1 hy.symm
    simp [correctionDensity, he, hm]
  · have hp : 0 ≤ ({y : Position | a < ‖y‖}.indicator (fun y => (‖y‖^6)⁻¹)) y := by
      apply Set.indicator_nonneg
      intro z hz
      positivity
    have he' : y ∉ {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S} := he
    rw [correctionDensity, Set.indicator_of_notMem he']
    exact mul_nonneg (by positivity : 0 ≤ (q^8)⁻¹) hp

theorem correctionDensity_integrable_and_mass {q a S : ℝ} (ha : 0 < a) :
    Integrable (correctionDensity q a S) ∧
      (∫ y, correctionDensity q a S y) ≤ (q^8)⁻¹*(4*Real.pi/(3*a^3)) := by
  have hset : MeasurableSet {y : Position | a < ‖y‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  have hb := ((integrable_exterior_inverse_sixth ha).integrable_indicator hset).const_mul (q^8)⁻¹
  have hi : Integrable (correctionDensity q a S) := hb.mono'
    (correctionDensity_measurable q a S).aestronglyMeasurable
    (correctionDensity_le_exterior.mono (fun y hy => by
      rw [Real.norm_eq_abs, abs_of_nonneg (correctionDensity_nonneg q a S y)]
      exact hy))
  refine ⟨hi, (integral_mono_ae hi hb correctionDensity_le_exterior).trans_eq ?_⟩
  rw [integral_const_mul, integral_indicator hset, integral_exterior_inverse_sixth ha]

theorem correctionDensity_mass_bound {q a S : ℝ} (hq : 0 < q) (ha : 1/(2*q) ≤ a) :
    (∫ y, correctionDensity q a S y) ≤ (32*Real.pi/3)*(q^5)⁻¹ := by
  have ha0 : 0 < a := (by positivity : 0 < 1/(2*q)).trans_le ha
  apply (correctionDensity_integrable_and_mass ha0).2.trans
  have hm : (1/(2*q))^3 ≤ a^3 := pow_le_pow_left₀ (by positivity) ha 3
  have hd : (a^3)⁻¹ ≤ ((1/(2*q))^3)⁻¹ := inv_anti₀ (by positivity) hm
  have hc : 0 ≤ (q^8)⁻¹*(4*Real.pi/3) := by positivity
  calc
    (q^8)⁻¹*(4*Real.pi/(3*a^3)) = ((q^8)⁻¹*(4*Real.pi/3))*(a^3)⁻¹ := by ring
    _ ≤ ((q^8)⁻¹*(4*Real.pi/3))*((1/(2*q))^3)⁻¹ := mul_le_mul_of_nonneg_left hd hc
    _ = (32*Real.pi/3)*(q^5)⁻¹ := by field_simp; ring

theorem correctionDensity_local_bound {q a S : ℝ} {x y : Position} (hx : x ≠ 0)
    (hy : y ∈ Metric.ball x (‖x‖/4)) :
    correctionDensity q a S y ≤ (q^8)⁻¹*((‖x‖/2)^6)⁻¹ := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hyd : ‖x-y‖ < ‖x‖/4 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
  have hyl : ‖x‖/2 ≤ ‖y‖ := by linarith [norm_le_norm_sub_add x y]
  have hi : (‖y‖^6)⁻¹ ≤ ((‖x‖/2)^6)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hyl 6)
  by_cases he : a ≤ ‖y‖ ∧ ‖y‖ ≤ S
  · simpa [correctionDensity, he] using mul_le_mul_of_nonneg_left hi
      (by positivity : 0 ≤ (q^8)⁻¹)
  · have he' : y ∉ {y : Position | a ≤ ‖y‖ ∧ ‖y‖ ≤ S} := he
    rw [correctionDensity, Set.indicator_of_notMem he']
    positivity

theorem correction_potential_tendsto_zero {q a : ℕ → ℝ} (S : ℝ)
    (hq : Tendsto q atTop atTop) (ha : ∀ᶠ n in atTop, 1/(2*q n) ≤ a n)
    {x : Position} (hx : x ≠ 0) :
    Tendsto (fun n => potentialOf (correctionDensity (q n) (a n) S) x) atTop (𝓝 0) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hq8 : Tendsto (fun n => ((q n)^8)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : 8 ≠ 0)).comp hq)
  have hq5 : Tendsto (fun n => ((q n)^5)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by decide : 5 ≠ 0)).comp hq)
  have hbound : ∀ᶠ n in atTop, potentialOf (correctionDensity (q n) (a n) S) x ≤
      ((q n)^8)⁻¹*((‖x‖/2)^6)⁻¹*kernelBallMass (‖x‖/4)+
        (‖x‖/4)⁻¹*((32*Real.pi/3)*((q n)^5)⁻¹) := by
    filter_upwards [ha, hq.eventually (eventually_gt_atTop 0)] with n hn hqn
    have han : 0 < a n := (by positivity : 0 < 1/(2*q n)).trans_le hn
    apply (potential_integrable_and_bound (correctionDensity_integrable_and_mass han).1
      (correctionDensity_nonneg _ _ _) (by positivity)
      (fun y hy => correctionDensity_local_bound hx hy)).2.trans
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_left (correctionDensity_mass_bound hqn hn)
      (by positivity : 0 ≤ (‖x‖/4)⁻¹)
  apply squeeze_zero' (Filter.Eventually.of_forall
    (fun n => potentialOf_nonneg (correctionDensity_nonneg _ _ _) x)) hbound
  simpa using ((hq8.mul_const (((‖x‖/2)^6)⁻¹)).mul_const (kernelBallMass (‖x‖/4))).add
    ((hq5.const_mul (32*Real.pi/3)).const_mul (‖x‖/4)⁻¹)

def WeakNuclearSubsolution (U : Position → ℝ) (lam : ℝ) (Ω : Set Position)
    (s : Position → ℝ) : Prop :=
  ∀ φ : Position → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∀ x, 0 ≤ φ x) →
    -(4*Real.pi*lam*φ 0)+(∫ x, s x*φ x) ≤ ∫ x, U x*coordinateLaplacian φ x

theorem integrable_mul_test_on {q φ : Position → ℝ} {Ω : Set Position}
    (hq : LocallyIntegrableOn q Ω) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (ht : tsupport φ ⊆ Ω) : Integrable (fun x => q x*φ x) := by
  exact (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right q φ).trans (subset_tsupport φ))).mp
    ((hq.integrableOn_compact_subset ht hc).mul_continuousOn hφ.continuousOn hc)

theorem integral_coordinateLaplacian {φ : Position → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, coordinateLaplacian φ x) = 0 := by
  have hh := integral_mul_coordinateLaplacian_eq
    (f := fun _ => (1:ℝ)) (fun _ _ => contDiffAt_const) hφ hc
  simpa [coordinateLaplacian] using hh

theorem corrected_test_identity {U σ η φ : Position → ℝ} {lam c Aσ Aη : ℝ}
    (hU : Continuous (fun x => U x-lam*coulombKernel x))
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hη : Integrable η) (hηpos : ∀ x, 0 ≤ η x) (hηbd : ∀ x, η x ≤ Aη)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, (U x-(lam*coulombKernel x-potentialOf σ x)-potentialOf η x-c)*coordinateLaplacian φ x) =
      (∫ x, U x*coordinateLaplacian φ x)+4*Real.pi*lam*φ 0-
        (∫ x, (4*Real.pi)*σ x*φ x)+(∫ x, (4*Real.pi)*η x*φ x) := by
  have hL : Continuous (coordinateLaplacian φ) :=
    continuous_coordinateLaplacian (hφ.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hLc := hasCompactSupport_coordinateLaplacian hc
  have hiK : Integrable (fun x => coulombKernel x*coordinateLaplacian φ x) := by
    simpa only [smul_eq_mul] using
      locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport hL hLc
  have hiUreg : Integrable (fun x => (U x-lam*coulombKernel x)*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt (fun x _ => hU.continuousAt) hL hLc
  have hiU : Integrable (fun x => U x*coordinateLaplacian φ x) := by
    exact (hiUreg.add (hiK.const_mul lam)).congr (Filter.Eventually.of_forall (by
      intro x
      simp only [Pi.add_apply]
      ring))
  have hiσ : Integrable (fun x => potentialOf σ x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun _ _ => (potentialOf_continuous hσ hσpos hσbd).continuousAt) hL hLc
  have hiη : Integrable (fun x => potentialOf η x*coordinateLaplacian φ x) :=
    integrable_mul_compact_of_continuousAt
      (fun _ _ => (potentialOf_continuous hη hηpos hηbd).continuousAt) hL hLc
  have hilamK : Integrable (fun x => lam*coulombKernel x*coordinateLaplacian φ x) := by
    simpa only [mul_assoc] using hiK.const_mul lam
  have he : (fun x => (U x-(lam*coulombKernel x-potentialOf σ x)-potentialOf η x-c)*coordinateLaplacian φ x) =
      (fun x => (((U x*coordinateLaplacian φ x-lam*coulombKernel x*coordinateLaplacian φ x)+
        potentialOf σ x*coordinateLaplacian φ x)-potentialOf η x*coordinateLaplacian φ x)-c*coordinateLaplacian φ x) := by
    funext x
    ring
  have hii1 : Integrable (fun x => U x*coordinateLaplacian φ x-
      lam*coulombKernel x*coordinateLaplacian φ x) := hiU.sub hilamK
  have hii2 : Integrable (fun x => U x*coordinateLaplacian φ x-
      lam*coulombKernel x*coordinateLaplacian φ x+
      potentialOf σ x*coordinateLaplacian φ x) := hii1.add hiσ
  have hii3 : Integrable (fun x => U x*coordinateLaplacian φ x-
      lam*coulombKernel x*coordinateLaplacian φ x+
      potentialOf σ x*coordinateLaplacian φ x-
      potentialOf η x*coordinateLaplacian φ x) := hii2.sub hiη
  rw [he, integral_sub hii3
    ((hL.integrable_of_hasCompactSupport hLc).const_mul c),
    integral_sub hii2 hiη, integral_add hii1 hiσ, integral_sub hiU hilamK]
  have hσP := potentialOf_weakLaplacian hσ φ hφ hc (Set.subset_univ _)
  have hηP := potentialOf_weakLaplacian hη φ hφ hc (Set.subset_univ _)
  rw [hσP, hηP]
  simp_rw [show ∀ x, lam*coulombKernel x*coordinateLaplacian φ x =
    lam*(coulombKernel x*coordinateLaplacian φ x) by intro x; ring,
    integral_const_mul, integral_coulombKernel_laplacian hφ hc,
    integral_coordinateLaplacian hφ hc]
  simp only [neg_mul, integral_neg, mul_zero]
  ring

theorem cancel_nuclear_source {U σ η s q : Position → ℝ} {lam c Aσ Aη : ℝ}
    {Ω : Set Position} (hU : Continuous (fun x => U x-lam*coulombKernel x))
    (hσ : Integrable σ) (hσpos : ∀ x, 0 ≤ σ x) (hσbd : ∀ x, σ x ≤ Aσ)
    (hη : Integrable η) (hηpos : ∀ x, 0 ≤ η x) (hηbd : ∀ x, η x ≤ Aη)
    (hs : LocallyIntegrableOn s Ω) (hq : LocallyIntegrableOn q Ω)
    (hw : WeakNuclearSubsolution U lam Ω s)
    (hle : ∀ x ∈ Ω, q x ≤ s x-(4*Real.pi)*σ x+(4*Real.pi)*η x) :
    WeakLaplacianGE
      (fun x => U x-(lam*coulombKernel x-potentialOf σ x)-potentialOf η x-c) Ω q := by
  intro φ hφ hc ht hp
  have his := integrable_mul_test_on hs hφ.continuous hc ht
  have hiq := integrable_mul_test_on hq hφ.continuous hc ht
  have hiσ : Integrable (fun x => σ x*φ x) := by
    simpa only [smul_eq_mul] using
      hσ.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hiη : Integrable (fun x => η x*φ x) := by
    simpa only [smul_eq_mul] using
      hη.locallyIntegrable.integrable_smul_right_of_hasCompactSupport hφ.continuous hc
  have hiσ' : Integrable (fun x => (4*Real.pi)*σ x*φ x) := by
    simpa only [mul_assoc] using hiσ.const_mul (4*Real.pi)
  have hiη' : Integrable (fun x => (4*Real.pi)*η x*φ x) := by
    simpa only [mul_assoc] using hiη.const_mul (4*Real.pi)
  have hle' : ∀ x, q x*φ x ≤ s x*φ x-(4*Real.pi)*σ x*φ x+(4*Real.pi)*η x*φ x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hh := mul_le_mul_of_nonneg_right (hle x (ht hx)) (hp x)
      nlinarith
    · simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero, sub_self, add_zero, le_refl]
  have hh := integral_mono hiq ((his.sub hiσ').add hiη') hle'
  simp only [Pi.add_apply, Pi.sub_apply] at hh
  have hisub : Integrable (fun x => s x*φ x-(4*Real.pi)*σ x*φ x) := his.sub hiσ'
  rw [integral_add hisub hiη', integral_sub his hiσ'] at hh
  rw [corrected_test_identity hU hσ hσpos hσbd hη hηpos hηbd hφ hc]
  have hw' := hw φ hφ hc ht hp
  linarith

end NeutralAtom
end
end
end

end OAI
