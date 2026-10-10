import OAI.MathematicalPhysics.Boltzmann.Approximation.MassNormalizedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Branching.ExtendedProductionScale
import OAI.MathematicalPhysics.Boltzmann.Compactness.FiniteRatesWindowUI
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicInitialEntropyLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1ToWeakStar
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations

namespace OAI

section

/-! # Bounded restoration of spatial mass preserves the dissipation bound -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
theorem extendedProduction_eq_regularized_rates {N : ℝ} (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    extendedProduction N f z =
      extendedEntropyProduction (regularizedPostRate N f z) (regularizedPreRate N f z) := by
  rw [regularizedPostRate_factor,regularizedPreRate_factor]
  symm
  simpa only [extendedProduction,mul_assoc] using extendedEntropyProduction_scale
    (mul_nonneg (windowKernel_bounds hN.le z).1 (rateMultiplier_bounds hN hf z).1)
    (mul_nonneg (hf _) (hf _)) (mul_nonneg (hf _) (hf _))

omit [MeasurableSpace X] in
theorem collisionMassClip_ratio_bounds {K : ℝ} (hK : 0 ≤ K)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    0 ≤ collisionMassClip K f z/(1+fiberMass volume f z.1.1) ∧
      collisionMassClip K f z/(1+fiberMass volume f z.1.1) ≤ 1 := by
  have hr : 0 ≤ fiberMass volume f z.1.1 := integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hf (z.1.1,v))
  have hd : 0 < 1+fiberMass volume f z.1.1 := by linarith
  exact ⟨div_nonneg (massClip_bounds hK hr).1 hd.le,
    (div_le_one hd).mpr (min_le_right _ _)⟩

omit [MeasurableSpace X] in
theorem clipped_regularizedProduction_le {K N : ℝ} (hK : 0 ≤ K) (hN : 0 < N)
    {f : X × Velocity → ℝ} (hf : ∀ p, 0 ≤ f p)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    extendedEntropyProduction
      (collisionMassClip K f z*massRegularizedPostRate N f z)
      (collisionMassClip K f z*massRegularizedPreRate N f z) ≤ extendedProduction N f z := by
  have hc := collisionMassClip_ratio_bounds hK hf z
  have hp : 0 ≤ regularizedPostRate N f z := (regularizedPreRate_bounds hN hf (scatterTriple z)).1
  have hq := (regularizedPreRate_bounds hN hf z).1
  have he : extendedEntropyProduction
      (collisionMassClip K f z*massRegularizedPostRate N f z)
      (collisionMassClip K f z*massRegularizedPreRate N f z) =
      ENNReal.ofReal (collisionMassClip K f z/(1+fiberMass volume f z.1.1))*
        extendedProduction N f z := by
    rw [extendedProduction_eq_regularized_rates hN hf]
    convert extendedEntropyProduction_scale hc.1 hp hq using 1
    simp only [massRegularizedPostRate,massRegularizedPreRate]
    congr 1 <;> ring
  rw [he]
  have hcle : ENNReal.ofReal (collisionMassClip K f z/(1+fiberMass volume f z.1.1)) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hc.2
  exact (mul_le_mul' hcle (le_refl (extendedProduction N f z))).trans_eq (one_mul _)

omit [MeasurableSpace X] in
theorem collisionMassClip_eventually_full {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : (X × (Velocity × Velocity)) × Sphere) :
    ∀ᶠ k : ℕ in atTop,
      collisionMassClip (k:ℝ) f z*massNormalizedPreRate f z = preRate f z ∧
      collisionMassClip (k:ℝ) f z*massNormalizedPostRate f z = postRate f z := by
  have hr : 0 ≤ fiberMass volume f z.1.1 := integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hf (z.1.1,v))
  have hd : 1+fiberMass volume f z.1.1 ≠ 0 := by linarith
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (1+fiberMass volume f z.1.1))] with k hk
  simp only [collisionMassClip,massClip,min_eq_right hk,massNormalizedPreRate,massNormalizedPostRate]
  constructor <;> field_simp

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Weak convergence after restoring bounded spatial-mass factors -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem weak_clipped_collision_rates
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n p, 0 ≤ f n p) (hg : ∀ p, 0 ≤ g p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n)
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass volume (f n) x-fiberMass volume g x)
      1 μ) atTop (𝓝 0))
    (hp : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPreRate (N n) (f n)) (massNormalizedPreRate g))
    (hq : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPostRate (N n) (f n)) (massNormalizedPostRate g))
    (K : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    Published.WeakL1Converges
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R))
      (fun n z => collisionMassClip K (f n) z*massRegularizedPreRate (N n) (f n) z)
      (fun z => collisionMassClip K g z*massNormalizedPreRate g z) ∧
    Published.WeakL1Converges
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R))
      (fun n z => collisionMassClip K (f n) z*massRegularizedPostRate (N n) (f n) z)
      (fun z => collisionMassClip K g z*massNormalizedPostRate g z) := by
  have hclip n z : |collisionMassClip K (f n) z| ≤ K := by
    have h := massClip_bounds K.coe_nonneg (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hf n (z.1.1,v)))
    exact (abs_of_nonneg h.1).trans_le h.2
  have hgclip z : |collisionMassClip K g z| ≤ K := by
    have h := massClip_bounds K.coe_nonneg (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hg (z.1.1,v)))
    exact (abs_of_nonneg h.1).trans_le h.2
  have hs := collisionMassClip_strong_on_window hfm hgm hm (K:ℝ) hR
  exact ⟨(hp.restrict (collisionWindow_measurable R)).varying_bounded_mul
      (massRegularizedPreRate_window_uniformIntegrable hfm hf hi hb hN hR)
      (fun n => massRegularizedPreRate_measurable (N n) (hfm n))
      (fun n => collisionMassClip_measurable K (hfm n)) (collisionMassClip_measurable K hgm)
      K hclip hgclip hs,
    (hq.restrict (collisionWindow_measurable R)).varying_bounded_mul
      (massRegularizedPostRate_window_uniformIntegrable hfm hf hi hb hN hR)
      (fun n => massRegularizedPostRate_measurable (N n) (hfm n))
      (fun n => collisionMassClip_measurable K (hfm n)) (collisionMassClip_measurable K hgm)
      K hclip hgclip hs⟩

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Lower semicontinuity of dissipation with a bounded spatial-mass restoration -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem clipped_production_liminf
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n p, 0 ≤ f n p) (hg : ∀ p, 0 ≤ g p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n)
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass volume (f n) x-fiberMass volume g x)
      1 μ) atTop (𝓝 0))
    (hp : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPreRate (N n) (f n)) (massNormalizedPreRate g))
    (hq : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPostRate (N n) (f n)) (massNormalizedPostRate g))
    (K : ℝ≥0) {R : ℝ} (hR : 0 ≤ R) :
    (∫⁻ z in collisionWindow R, extendedEntropyProduction
      (collisionMassClip K g z*massNormalizedPostRate g z)
      (collisionMassClip K g z*massNormalizedPreRate g z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤
    liminf (fun n => ∫⁻ z, extendedProduction (N n) (f n) z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) atTop := by
  let ν := ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)
  have hw := weak_clipped_collision_rates hfm hgm hf hg hi hb hN hm hp hq K hR
  have hcb n z : |collisionMassClip K (f n) z| ≤ K := by
    have h := massClip_bounds K.coe_nonneg (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hf n (z.1.1,v)))
    exact (abs_of_nonneg h.1).trans_le h.2
  have hpi n : Integrable (fun z => collisionMassClip K (f n) z*massRegularizedPreRate (N n) (f n) z) ν :=
    (memLp_one_iff_integrable.mp
      ((massRegularizedPreRate_window_uniformIntegrable hfm hf hi hb hN hR).memLp n)).bdd_mul
        (collisionMassClip_measurable K (hfm n)).aestronglyMeasurable (ae_of_all _ (hcb n))
  have hqi n : Integrable (fun z => collisionMassClip K (f n) z*massRegularizedPostRate (N n) (f n) z) ν :=
    (memLp_one_iff_integrable.mp
      ((massRegularizedPostRate_window_uniformIntegrable hfm hf hi hb hN hR).memLp n)).bdd_mul
        (collisionMassClip_measurable K (hfm n)).aestronglyMeasurable (ae_of_all _ (hcb n))
  have hgn z : 0 ≤ collisionMassClip K g z :=
    (massClip_bounds K.coe_nonneg (integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hg (z.1.1,v)))).1
  have hd (z : (X × (Velocity × Velocity)) × Sphere) : 0 ≤ 1+fiberMass volume g z.1.1 := by
    have h : 0 ≤ fiberMass volume g z.1.1 := integral_nonneg (μ := (volume : Measure Velocity)) (fun v => hg (z.1.1,v))
    linarith
  have hl := Published.weak_production_liminf hw.2 hw.1 hqi hpi
    (ae_of_all ν (fun z => mul_nonneg (hgn z) (div_nonneg (preRate_nonneg hg (scatterTriple z)) (hd z))))
    (ae_of_all ν (fun z => mul_nonneg (hgn z) (div_nonneg (preRate_nonneg hg z) (hd z))))
  exact hl.trans (liminf_le_liminf (Eventually.of_forall (fun n =>
    (lintegral_mono (clipped_regularizedProduction_le K.coe_nonneg (hN n) (hf n))).trans
      (setLIntegral_le_lintegral _ _))))

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
