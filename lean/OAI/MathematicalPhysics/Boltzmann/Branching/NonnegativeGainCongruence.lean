import OAI.MathematicalPhysics.Boltzmann.Collision.CarlemanOperator
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

section

/-! # Integrating a nonnegative characteristic source from fiber bounds -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]

theorem integrable_nonnegative_of_fiber_bound {T : ℝ} {F : ℝ × X → ℝ} {B : X → ℝ}
    (hF : AEStronglyMeasurable F ((volume.restrict (Icc 0 T)).prod ν))
    (hFn : ∀ p t, t ∈ Icc 0 T → 0 ≤ F (t,p))
    (hFi : ∀ᵐ p ∂ν, Integrable (fun t => F (t,p)) (volume.restrict (Icc 0 T)))
    (hB : Integrable B ν)
    (hb : ∀ᵐ p ∂ν, (∫ t in Icc 0 T, F (t,p)) ≤ B p) :
    Integrable F ((volume.restrict (Icc 0 T)).prod ν) := by
  apply (integrable_prod_iff' hF).mpr
  refine ⟨hFi,hB.mono' hF.norm.prod_swap.integral_prod_right' ?_⟩
  filter_upwards [hb] with p hp
  have hn : (fun t => ‖F (t,p)‖) =ᵐ[volume.restrict (Icc 0 T)] fun t => F (t,p) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Real.norm_of_nonneg (hFn p t ht)
  rw [Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg _)),integral_congr_ae hn]
  exact hp

end BoltzmannNonuniqueness

end

end

section

/-! # Nonnegative gain respects almost-everywhere input representatives -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

namespace BoltzmannNonuniqueness

theorem nonnegativeGain_congr_ae {a b f g : Velocity → ℝ≥0∞}
    (hab : a =ᵐ[volume] b) (hfg : f =ᵐ[volume] g) :
    nonnegativeGain a f =ᵐ[volume] nonnegativeGain b g := by
  let : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
  have hal := ae_ae_of_ae_prod (CollisionNullSets.left_quasiMeasurePreserving.ae hab)
  have har := ae_ae_of_ae_prod (CollisionNullSets.right_quasiMeasurePreserving.ae hab)
  have hfl := ae_ae_of_ae_prod (CollisionNullSets.left_quasiMeasurePreserving.ae hfg)
  have hfr := ae_ae_of_ae_prod (CollisionNullSets.right_quasiMeasurePreserving.ae hfg)
  filter_upwards [hal,har,hfl,hfr] with v hal har hfl hfr
  apply lintegral_congr_ae
  filter_upwards [hal,har,hfl,hfr] with p hal har hfl hfr
  change a (scatterLeft v p.1 p.2) = b (scatterLeft v p.1 p.2) at hal
  change a (scatterRight v p.1 p.2) = b (scatterRight v p.1 p.2) at har
  change f (scatterLeft v p.1 p.2) = g (scatterLeft v p.1 p.2) at hfl
  change f (scatterRight v p.1 p.2) = g (scatterRight v p.1 p.2) at hfr
  rw [hal,har,hfl,hfr]

end BoltzmannNonuniqueness

end

end

end OAI
