import OAI.MathematicalPhysics.Boltzmann.Branching.InMeasureDifference
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionConservation
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedGainCompactness
import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrability

namespace OAI

section

/-! # A common gain limit controls the normalized difference of two positive profiles -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem normalized_source_difference_L1
    {u v a b : ℕ → X → ℝ} {g : X → ℝ}
    (hum : ∀ n, Measurable (u n)) (hvm : ∀ n, Measurable (v n))
    (ham : ∀ n, Measurable (a n)) (hbm : ∀ n, Measurable (b n))
    (hu : ∀ n x, 0 ≤ u n x) (hv : ∀ n x, 0 ≤ v n x)
    (ha0 : ∀ n x, 0 ≤ a n x) (hb0 : ∀ n x, 0 ≤ b n x)
    (ha : TendstoInMeasure μ a atTop g) (hb : TendstoInMeasure μ b atTop g)
    (hai : UniformIntegrable (fun n x => a n x/(1+u n x)) 1 μ)
    (hbi : UniformIntegrable (fun n x => b n x/(1+v n x)) 1 μ) :
    Tendsto (fun n => eLpNorm (fun x => (a n x-b n x)/(1+u n x+v n x)) 1 μ) atTop (𝓝 0) := by
  let D : ℕ → X → ℝ := fun n x => (a n x-b n x)/(1+u n x+v n x)
  let H : ℕ → X → ℝ := fun n x => a n x/(1+u n x)+b n x/(1+v n x)
  have hDm n : Measurable (D n) := ((ham n).sub (hbm n)).div
    ((measurable_const.add (hum n)).add (hvm n))
  have hdiff : TendstoInMeasure μ (fun n x => a n x-b n x) atTop (fun _ => 0) := by
    simpa only [sub_self] using tendstoInMeasure_sub (fun n => (ham n).aestronglyMeasurable)
      (fun n => (hbm n).aestronglyMeasurable) ha hb
  have hdi : TendstoInMeasure μ D atTop (fun _ => 0) := by
    apply tendstoInMeasure_zero_of_abs_le hdiff
    intro n x
    exact normalized_difference_abs_le (hu n x) (hv n x)
  have hHi : UniformIntegrable H 1 μ := uniformIntegrable_add hai hbi
  have hbound n x : |D n x| ≤ H n x :=
    normalized_difference_source_bound (ha0 n x) (hb0 n x) (hu n x) (hv n x)
  have hDi : UniformIntegrable D 1 μ :=
    uniformIntegrable_abs_le hHi (fun n => (hDm n).aestronglyMeasurable)
      (fun n => ae_of_all _ (hbound n))
  have h := tendsto_Lp_finite_of_tendstoInMeasure (by norm_num) (by norm_num)
    (fun n => (hDm n).aestronglyMeasurable) (hDi.memLp_of_tendstoInMeasure hdi) hDi.1 hdi
  apply h.congr'
  apply Eventually.of_forall
  intro n
  apply eLpNorm_congr_ae
  exact ae_of_all _ (fun x => sub_zero (D n x))

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # Finite dissipation gives actual gain/loss fibers and separate renormalized terms -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness

local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]

theorem rateDissipation_finite_regrouped {f : X × Velocity → ℝ} (hfm : Measurable f)
    (hD : rateDissipation μ f < ⊤) :
    (∫⁻ z : (X × Velocity) × (Velocity × Sphere), extendedEntropyProduction
      (postRate f (collisionGrouping.symm z)) (preRate f (collisionGrouping.symm z))
      ∂((μ.prod volume).prod ((volume : Measure Velocity).prod sphereArea))) < ⊤ := by
  have hm : Measurable (fun z : (X × (Velocity × Velocity)) × Sphere =>
      extendedEntropyProduction (postRate f z) (preRate f z)) := measurable_extendedEntropyProduction
    ((preRate_measurable hfm).comp scatterTriple_measurable) (preRate_measurable hfm)
  have hmap := ((collisionGrouping_measurePreserving μ).symm collisionGrouping).lintegral_comp hm
  rw [hmap]
  have he : (∫⁻ z, extendedEntropyProduction (postRate f z) (preRate f z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) =
      4*rateDissipation μ f := by
    unfold rateDissipation
    rw [← mul_assoc,ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_mul]
  rw [he]
  exact ENNReal.mul_lt_top (by norm_num) hD

theorem normalized_gainLoss_and_fibers {f : X × Velocity → ℝ}
    (hfm : Measurable f) (hfn : ∀ p, 0 ≤ f p)
    (hf : Integrable f (μ.prod volume))
    (hm : Integrable (fun p => ‖p.2‖*f p) (μ.prod volume))
    (hD : rateDissipation μ f < ⊤) :
    Integrable (fun p => gainDensity f p/(1+f p/maxwellian p.2)) (μ.prod volume) ∧
    Integrable (fun p => lossDensity f p/(1+f p/maxwellian p.2)) (μ.prod volume) ∧
    ∀ᵐ p ∂μ.prod (volume : Measure Velocity),
      Integrable (fun q => postRate f (collisionGrouping.symm (p,q))) ((volume : Measure Velocity).prod sphereArea) ∧
      Integrable (fun q => preRate f (collisionGrouping.symm (p,q))) ((volume : Measure Velocity).prod sphereArea) := by
  have hpre := normalizedPreRate_integrable hfm hfn hf hm
  have hpost := normalizedPostRate_integrable hfm hfn hpre (rateDissipation_finite_regrouped hfm hD)
  refine ⟨hpost.integral_prod_left.congr (ae_of_all _ (normalizedPostRate_integral f)),
    renormalized_loss_integrable hfm hfn hf hm,?_⟩
  filter_upwards [hpre.prod_right_ae,hpost.prod_right_ae] with p hp hq
  let d := 1+f p/maxwellian p.2
  have hd : d ≠ 0 := ne_of_gt (show 0 < d from by
    have := hfn p
    have := (maxwellian_pos p.2).le
    dsimp [d]
    positivity)
  constructor
  · apply (hq.mul_const d).congr
    apply ae_of_all
    intro q
    change (postRate f (collisionGrouping.symm (p,q))/d)*d = _
    exact div_mul_cancel₀ _ hd
  · apply (hp.mul_const d).congr
    apply ae_of_all
    intro q
    change (preRate f (collisionGrouping.symm (p,q))/d)*d = _
    exact div_mul_cancel₀ _ hd

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
