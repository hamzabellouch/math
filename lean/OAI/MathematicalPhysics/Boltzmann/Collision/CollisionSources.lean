import OAI.MathematicalPhysics.Boltzmann.Approximation.CutoffLossFrequency
import OAI.MathematicalPhysics.Boltzmann.Branching.MixedPhysicalMeasures
import OAI.MathematicalPhysics.Boltzmann.Compactness.PairBoundedTruncation

namespace OAI

section

/-! # Uniform integrability of the actual cutoff equation's right-hand side -/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def collisionSource (b : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) : ℝ :=
  KineticCollisionNullSets.gain b f p-f p*KineticCollisionNullSets.frequency b f p

theorem collisionSource_measurable {f : X × Velocity → ℝ} (hf : Measurable f) (b : ℝ) :
    Measurable (collisionSource b f) :=
  (KineticCollisionNullSets.measurable_gain hf b).sub
    (hf.mul (KineticCollisionNullSets.measurable_frequency hf b))

private theorem uniformIntegrable_sub {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    {f g : ℕ → Y → ℝ} (hf : UniformIntegrable f 1 ν) (hg : UniformIntegrable g 1 ν) :
    UniformIntegrable (fun n y => f n y-g n y) 1 ν := by
  obtain ⟨hu,C,hC⟩ := hf
  obtain ⟨hv,D,hD⟩ := hg
  refine ⟨hu.sub hv (by norm_num),C+D,fun n => ?_⟩
  exact (eLpNorm_sub_le (by norm_num : (1 : ℝ≥0∞) ≤ 1)).trans
    (by simpa only [ENNReal.coe_add] using add_le_add (hC n) (hD n))

theorem collisionSource_uniformIntegrable [SFinite μ]
    {f : ℕ → X × Velocity → ℝ} (hfm : ∀ n, Measurable (f n)) (hf : ∀ n z, 0 ≤ f n z)
    (hpair : UniformIntegrable (fun n => pairDensity (f n)) 1
      (μ.prod (volume : Measure (Velocity × Velocity)))) (b : ℕ → ℝ)
    (hgain : UniformIntegrable (fun n => KineticCollisionNullSets.gain (b n) (f n)) 1
      (μ.prod (volume : Measure Velocity)))
    (hloss : UniformIntegrable (fun n => cutoffLossDensity (b n) (f n)) 1
      (μ.prod (volume : Measure Velocity))) :
    UniformIntegrable (fun n => collisionSource (b n) (f n)) 1
      (μ.prod (volume : Measure Velocity)) := by
  have he (n) := cutoff_loss_ae_eq_frequency (hfm n) (hf n)
    (memLp_one_iff_integrable.mp (hpair.memLp n)) (b n)
  exact uniformIntegrable_sub hgain (hloss.ae_eq he)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Discarding the nonnegative losses in the actual hot source -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*}

theorem cutoffFrequency_nonneg (b : ℝ) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    0 ≤ KineticCollisionNullSets.frequency b f p := by
  apply mul_nonneg (by positivity : (0:ℝ) ≤ 2*Real.pi)
  exact integral_nonneg (fun w => mul_nonneg (CollisionCutoff.rate_nonneg b p.2 w) (hf _))

theorem collisionSource_le_gain (b : ℝ) {f : X × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (p : X × Velocity) :
    collisionSource b f p ≤ KineticCollisionNullSets.gain b f p :=
  sub_le_self _ (mul_nonneg (hf _) (cutoffFrequency_nonneg b hf p))

variable [MeasurableSpace X]

theorem hot_source_le_gain (b r e : ℝ) {c h : X × Velocity → ℝ}
    (hc : ∀ p, 0 ≤ c p) (hh : ∀ p, 0 ≤ h p) (p : X × Velocity) :
    2*mixedGainDensity b c h p-h p*KineticCollisionNullSets.frequency b c p+
      r^2*collisionSource b h p+e ≤
      2*mixedGainDensity b c h p+r^2*KineticCollisionNullSets.gain b h p+e := by
  exact add_le_add (add_le_add (sub_le_self _ (mul_nonneg (hh _) (cutoffFrequency_nonneg b hc p)))
    (mul_le_mul_of_nonneg_left (collisionSource_le_gain b hh p) (sq_nonneg r))) le_rfl

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Scaling and base-coordinate identities for physical cutoff collisions -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

omit [MeasurableSpace X] in
theorem mixedPostRate_const_mul (b a d : ℝ) (c h : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    mixedPostRate b (fun p => a*c p) (fun p => d*h p) z =
      (a*d)*mixedPostRate b c h z := by
  unfold mixedPostRate mixedPreRate
  ring

theorem mixedGain_const_mul (b a d : ℝ) (c h : X × Velocity → ℝ) (p : X × Velocity) :
    mixedGainDensity b (fun p => a*c p) (fun p => d*h p) p =
      (a*d)*mixedGainDensity b c h p := by
  unfold mixedGainDensity
  simp_rw [mixedPostRate_const_mul]
  rw [integral_const_mul,integral_const_mul]
  ring

theorem cutoffGain_const_mul (b a : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    KineticCollisionNullSets.gain b (fun p => a*f p) p =
      a^2*KineticCollisionNullSets.gain b f p := by
  rw [← mixedGainDensity_self, mixedGain_const_mul, mixedGainDensity_self]
  ring

omit [MeasurableSpace X] in
theorem cutoffFrequency_const_mul (b a : ℝ) (f : X × Velocity → ℝ) (p : X × Velocity) :
    KineticCollisionNullSets.frequency b (fun p => a*f p) p =
      a*KineticCollisionNullSets.frequency b f p := by
  unfold KineticCollisionNullSets.frequency CollisionCutoff.frequency
  simp_rw [show ∀ w, CollisionCutoff.rate b p.2 w*(a*f (p.1,w)) =
    a*(CollisionCutoff.rate b p.2 w*f (p.1,w)) by intro w; ring]
  rw [integral_const_mul]
  ring

omit [MeasurableSpace X] in
theorem cutoffFrequency_add (b : ℝ) (c h : X × Velocity → ℝ) (p : X × Velocity)
    (hc : Integrable (fun w => CollisionCutoff.rate b p.2 w*c (p.1,w)))
    (hh : Integrable (fun w => CollisionCutoff.rate b p.2 w*h (p.1,w))) :
    KineticCollisionNullSets.frequency b (c+h) p =
      KineticCollisionNullSets.frequency b c p+KineticCollisionNullSets.frequency b h p := by
  unfold KineticCollisionNullSets.frequency CollisionCutoff.frequency
  simp only [Pi.add_apply,mul_add]
  have he := integral_add hc hh
  rw [he]
  ring

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem mixedPostRate_base_comp (b : ℝ) (c h : X × Velocity → ℝ) (τ : Y → X)
    (z : (Y × (Velocity × Velocity)) × Sphere) :
    mixedPostRate b (fun p => c (τ p.1,p.2)) (fun p => h (τ p.1,p.2)) z =
      mixedPostRate b c h ((τ z.1.1,z.1.2),z.2) := rfl

theorem mixedGain_base_comp (b : ℝ) (c h : X × Velocity → ℝ) (τ : Y → X)
    (p : Y × Velocity) :
    mixedGainDensity b (fun p => c (τ p.1,p.2)) (fun p => h (τ p.1,p.2)) p =
      mixedGainDensity b c h (τ p.1,p.2) := rfl

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem cutoffGain_base_comp (b : ℝ) (f : X × Velocity → ℝ) (τ : Y → X)
    (p : Y × Velocity) :
    KineticCollisionNullSets.gain b (fun p => f (τ p.1,p.2)) p =
      KineticCollisionNullSets.gain b f (τ p.1,p.2) := rfl

omit [MeasurableSpace X] [MeasurableSpace Y] in
theorem cutoffFrequency_base_comp (b : ℝ) (f : X × Velocity → ℝ) (τ : Y → X)
    (p : Y × Velocity) :
    KineticCollisionNullSets.frequency b (fun p => f (τ p.1,p.2)) p =
      KineticCollisionNullSets.frequency b f (τ p.1,p.2) := rfl

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # L1 contraction for marginalizing a collision rate -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BoltzmannNonuniqueness.CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [SFinite μ]
local instance : SFinite ((volume : Measure Velocity).prod sphereArea) := Measure.prod.instSFinite

def collisionMarginal (h : (X × (Velocity × Velocity)) × Sphere → ℝ)
    (p : X × Velocity) : ℝ :=
  ∫ q : Velocity × Sphere, h (collisionGrouping.symm (p,q))
    ∂(volume : Measure Velocity).prod sphereArea

theorem collisionMarginal_integrable {h : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hi : Integrable h ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    Integrable (collisionMarginal h) (μ.prod volume) :=
  ((collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hi).integral_prod_left

theorem collisionMarginal_sub_ae {h k : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hi : Integrable h ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (ki : Integrable k ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    collisionMarginal (h-k) =ᵐ[μ.prod volume] collisionMarginal h-collisionMarginal k := by
  have hhi := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable hi
  have hki := (collisionGrouping_measurePreserving μ).symm.integrable_comp_of_integrable ki
  filter_upwards [hhi.prod_right_ae,hki.prod_right_ae] with p hp kp
  exact integral_sub hp kp

theorem collisionMarginal_eLpNorm_le {h : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hm : Measurable h) :
    eLpNorm (collisionMarginal h) 1 (μ.prod volume) ≤
      eLpNorm h 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  have ht := Compactness.eLpNorm_integral_le (μ := μ.prod volume)
    (ν := (volume : Measure Velocity).prod sphereArea) (hm.comp collisionGrouping.symm.measurable)
  apply ht.trans_eq
  exact eLpNorm_comp_measurePreserving hm.aestronglyMeasurable (collisionGrouping_measurePreserving μ).symm

theorem collisionMarginal_difference_le {h k : (X × (Velocity × Velocity)) × Sphere → ℝ}
    (hm : Measurable h) (km : Measurable k)
    (hi : Integrable h ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea))
    (ki : Integrable k ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)) :
    eLpNorm (collisionMarginal h-collisionMarginal k) 1 (μ.prod volume) ≤
      eLpNorm (h-k) 1 ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) := by
  rw [← eLpNorm_congr_ae (collisionMarginal_sub_ae hi ki)]
  exact collisionMarginal_eLpNorm_le (hm.sub km)

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # Collision operators depend only on the velocity fibre at their base point -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.CollisionCompactness

variable {X : Type*} [MeasurableSpace X]

private theorem mixedPostRate_fiber_congr (b : ℝ) {c d h k : X × Velocity → ℝ} {x : X}
    (hc : ∀ v, c (x,v) = d (x,v)) (hh : ∀ v, h (x,v) = k (x,v))
    (v : Velocity) (w : Velocity × Sphere) :
    mixedPostRate b c h (collisionGrouping.symm ((x,v),w)) =
      mixedPostRate b d k (collisionGrouping.symm ((x,v),w)) := by
  rw [mixedPostRate_formula,mixedPostRate_formula]
  change CollisionCutoff.kernel b v w.1 w.2*c (x,scatterLeft v w.1 w.2)*h (x,scatterRight v w.1 w.2) =
    CollisionCutoff.kernel b v w.1 w.2*d (x,scatterLeft v w.1 w.2)*k (x,scatterRight v w.1 w.2)
  rw [hc,hh]

theorem mixedGain_fiber_congr (b : ℝ) {c d h k : X × Velocity → ℝ} {x : X}
    (hc : ∀ v, c (x,v) = d (x,v)) (hh : ∀ v, h (x,v) = k (x,v)) (v : Velocity) :
    mixedGainDensity b c h (x,v) = mixedGainDensity b d k (x,v) := by
  unfold mixedGainDensity
  simp_rw [mixedPostRate_fiber_congr b hc hh,mixedPostRate_fiber_congr b hh hc]

omit [MeasurableSpace X] in
theorem cutoffGain_fiber_congr (b : ℝ) {f g : X × Velocity → ℝ} {x : X}
    (hf : ∀ v, f (x,v) = g (x,v)) (v : Velocity) :
    KineticCollisionNullSets.gain b f (x,v) = KineticCollisionNullSets.gain b g (x,v) := by
  unfold KineticCollisionNullSets.gain CollisionCutoff.gain CollisionCutoff.integrand
  simp_rw [hf]

omit [MeasurableSpace X] in
theorem cutoffFrequency_fiber_congr (b : ℝ) {f g : X × Velocity → ℝ} {x : X}
    (hf : ∀ v, f (x,v) = g (x,v)) (v : Velocity) :
    KineticCollisionNullSets.frequency b f (x,v) = KineticCollisionNullSets.frequency b g (x,v) := by
  unfold KineticCollisionNullSets.frequency CollisionCutoff.frequency
  simp_rw [hf]

omit [MeasurableSpace X] in
theorem collisionSource_fiber_congr (b : ℝ) {f g : X × Velocity → ℝ} {x : X}
    (hf : ∀ v, f (x,v) = g (x,v)) (v : Velocity) :
    collisionSource b f (x,v) = collisionSource b g (x,v) := by
  unfold collisionSource
  rw [cutoffGain_fiber_congr b hf,cutoffFrequency_fiber_congr b hf,hf]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
