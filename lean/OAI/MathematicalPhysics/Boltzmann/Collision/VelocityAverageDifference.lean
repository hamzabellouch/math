import OAI.MathematicalPhysics.Boltzmann.Branching.DampedBranchingBlocks

namespace OAI

section

/-! # Joint integrability for damped velocity-dependent characteristic lines -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

def velocityLineShear (s : ℝ) (p : Velocity × FourierSpace) : Velocity × FourierSpace :=
  (p.1,p.2-s • characteristicDirection p.1)

theorem velocityLineShear_measurePreserving (s : ℝ) :
    MeasurePreserving (velocityLineShear s) (volume : Measure (Velocity × FourierSpace)) volume := by
  unfold velocityLineShear
  apply (MeasurePreserving.id (volume : Measure Velocity)).skew_product
    (g := fun v x => x-s • characteristicDirection v)
    (μc := (volume : Measure FourierSpace)) (μd := (volume : Measure FourierSpace))
  · unfold characteristicDirection
    fun_prop
  · exact ae_of_all _ (fun v => (measurePreserving_add_right volume
      (-(s • characteristicDirection v))).map_eq)

def velocityTimeShear (p : ℝ × (Velocity × FourierSpace)) : ℝ × (Velocity × FourierSpace) :=
  (p.1,velocityLineShear p.1 p.2)

theorem velocityTimeShear_measurePreserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving velocityTimeShear (μ.prod (volume : Measure (Velocity × FourierSpace)))
      (μ.prod volume) := by
  unfold velocityTimeShear
  apply (MeasurePreserving.id μ).skew_product
    (g := velocityLineShear)
    (μc := (volume : Measure (Velocity × FourierSpace)))
    (μd := (volume : Measure (Velocity × FourierSpace)))
  · unfold velocityLineShear characteristicDirection
    fun_prop
  · exact ae_of_all _ (fun s => (velocityLineShear_measurePreserving s).map_eq)

def velocityLineResolvent (r : Velocity × FourierSpace → ℂ) (p : Velocity × FourierSpace) : ℂ :=
  dampedLineResolvent (fun x => r (p.1,x)) (characteristicDirection p.1) p.2

theorem velocityLine_integrable {r : Velocity × FourierSpace → ℂ} (hr : Integrable r) :
    Integrable (fun p : ℝ × (Velocity × FourierSpace) =>
      Real.exp (-p.1) • r (velocityLineShear p.1 p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  exact (velocityTimeShear_measurePreserving _).integrable_comp_of_integrable
    ((integrableOn_exp_neg_Ioi 0).smul_prod hr)

theorem velocityLineResolvent_integrable {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) : Integrable (velocityLineResolvent r) :=
  (velocityLine_integrable hr).integral_prod_right

def velocityLineAverage (r : Velocity × FourierSpace → ℂ) (x : FourierSpace) : ℂ :=
  ∫ v, velocityLineResolvent r (v,x)

theorem velocityLineAverage_integrable {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) : Integrable (velocityLineAverage r) :=
  (velocityLineResolvent_integrable hr).integral_prod_right

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The complex velocity-line average is an L1 contraction -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published

theorem integral_norm_partial_le {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : X × Y → ℂ} (hf : Integrable f (μ.prod ν)) :
    (∫ y, ‖∫ x, f (x,y) ∂μ‖ ∂ν) ≤ ∫ p, ‖f p‖ ∂(μ.prod ν) := by
  calc
    _ ≤ ∫ y, ∫ x, ‖f (x,y)‖ ∂μ ∂ν :=
      integral_mono hf.integral_prod_right.norm hf.norm.integral_prod_right
        (fun y => norm_integral_le_integral_norm _)
    _ = _ := (integral_prod_symm _ hf.norm).symm

theorem velocityLineShear_integral_norm {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (s : ℝ) :
    (∫ p, ‖r (velocityLineShear s p)‖) = ∫ p, ‖r p‖ := by
  have hp := velocityLineShear_measurePreserving s
  have hm : AEStronglyMeasurable (fun p => ‖r p‖) (Measure.map (velocityLineShear s) volume) := by
    rw [hp.map_eq]
    exact hr.norm.aestronglyMeasurable
  have he := integral_map hp.measurable.aemeasurable hm
  rw [hp.map_eq] at he
  exact he.symm

theorem velocityLineResolvent_L1_le {r : Velocity × FourierSpace → ℂ} (hr : Integrable r) :
    (∫ p, ‖velocityLineResolvent r p‖) ≤ ∫ p, ‖r p‖ := by
  have h := integral_norm_partial_le (velocityLine_integrable hr)
  calc
    _ ≤ ∫ q : ℝ × (Velocity × FourierSpace),
        ‖Real.exp (-q.1) • r (velocityLineShear q.1 q.2)‖
        ∂((volume.restrict (Ioi 0)).prod volume) := h
    _ = ∫ s in Ioi (0 : ℝ), Real.exp (-s)*(∫ p, ‖r p‖) := by
      rw [integral_prod _ (velocityLine_integrable hr).norm]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun s => by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        rw [integral_const_mul,velocityLineShear_integral_norm hr])
    _ = _ := by rw [integral_mul_const,integral_exp_neg_Ioi_zero,one_mul]

theorem velocityLineAverage_L1_le {r : Velocity × FourierSpace → ℂ} (hr : Integrable r) :
    (∫ x, ‖velocityLineAverage r x‖) ≤ ∫ p, ‖r p‖ :=
  (integral_norm_partial_le (velocityLineResolvent_integrable hr)).trans
    (velocityLineResolvent_L1_le hr)

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Linearity and L1 stability of the actual velocity average -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.Published

theorem velocityLineResolvent_sub {r q : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (hq : Integrable q) :
    velocityLineResolvent (r-q) =ᵐ[volume] velocityLineResolvent r-velocityLineResolvent q := by
  filter_upwards [(velocityLine_integrable hr).prod_left_ae,
    (velocityLine_integrable hq).prod_left_ae] with p hp hq'
  change (∫ s in Ioi (0:ℝ), Real.exp (-s) • (r (velocityLineShear s p)-q (velocityLineShear s p))) = _
  simp_rw [smul_sub]
  exact integral_sub hp hq'

theorem velocityLineAverage_sub {r q : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (hq : Integrable q) :
    velocityLineAverage (r-q) =ᵐ[volume] velocityLineAverage r-velocityLineAverage q := by
  have he := (Measure.measurePreserving_swap (μ := (volume : Measure FourierSpace))
    (ν := (volume : Measure Velocity))).quasiMeasurePreserving.ae_eq_comp (velocityLineResolvent_sub hr hq)
  filter_upwards [Measure.ae_ae_of_ae_prod he,
    (velocityLineResolvent_integrable hr).prod_left_ae,
    (velocityLineResolvent_integrable hq).prod_left_ae] with x hx hri hqi
  simp only [Function.comp_apply,Prod.swap_prod_mk,Pi.sub_apply] at hx
  change (∫ v, velocityLineResolvent (r-q) (v,x)) = _
  rw [integral_congr_ae hx,integral_sub hri hqi]
  rfl

theorem velocityLineAverage_eLpNorm_le {r : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) :
    eLpNorm (velocityLineAverage r) 1 volume ≤ eLpNorm r 1 volume := by
  rw [eLpNorm_one_eq_lintegral_enorm (velocityLineAverage_integrable hr).aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hr.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm (velocityLineAverage_integrable hr),
    ← ofReal_integral_norm_eq_lintegral_enorm hr]
  exact ENNReal.ofReal_le_ofReal (velocityLineAverage_L1_le hr)

theorem velocityLineAverage_difference_le {r q : Velocity × FourierSpace → ℂ}
    (hr : Integrable r) (hq : Integrable q) :
    eLpNorm (velocityLineAverage r-velocityLineAverage q) 1 volume ≤
      eLpNorm (r-q) 1 volume := by
  rw [← eLpNorm_congr_ae (velocityLineAverage_sub hr hq)]
  exact velocityLineAverage_eLpNorm_le (hr.sub hq)

end BoltzmannNonuniqueness.Published

end

end

end OAI
