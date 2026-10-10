import OAI.MathematicalPhysics.Boltzmann.Branching.LossIntegrability
import OAI.MathematicalPhysics.Boltzmann.Collision.AngularPairTests
import OAI.MathematicalPhysics.Boltzmann.Compactness.NormalizedCollisionRates

namespace OAI

section

/-! # A compact incoming cutoff and a translated outgoing velocity smoothing kernel -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Compactness

def translatedVelocityTest (χ : C(Velocity,ℝ)) (z : Velocity) : C(Velocity,ℝ) :=
  ⟨fun v => χ (z-v),χ.continuous.comp (continuous_const.sub continuous_id)⟩

def smoothedAngularKernel (η χ : C(Velocity,ℝ)) (p : Velocity × (Velocity × Velocity)) : ℝ :=
  (η p.2.1*η p.2.2)*∫ ω : Sphere,
    collisionKernel p.2.1 p.2.2 ω*χ (p.1-scatterLeft p.2.1 p.2.2 ω) ∂sphereArea

theorem smoothedAngularKernel_continuous (η χ : C(Velocity,ℝ)) :
    Continuous (smoothedAngularKernel η χ) := by
  have hc : Continuous (fun z : (Velocity × (Velocity × Velocity)) × Sphere =>
      collisionKernel z.1.2.1 z.1.2.2 z.2*χ (z.1.1-scatterLeft z.1.2.1 z.1.2.2 z.2)) := by
    unfold collisionKernel scatterLeft normalComponent
    fun_prop
  have h := continuous_parametric_integral_of_continuous (μ := sphereArea)
    (f := fun p : Velocity × (Velocity × Velocity) => fun ω : Sphere =>
      collisionKernel p.2.1 p.2.2 ω*χ (p.1-scatterLeft p.2.1 p.2.2 ω)) hc isCompact_univ
  have hi : Continuous (fun p : Velocity × (Velocity × Velocity) =>
      ∫ ω : Sphere, collisionKernel p.2.1 p.2.2 ω*χ (p.1-scatterLeft p.2.1 p.2.2 ω) ∂sphereArea) := by
    simpa only [Measure.restrict_univ] using h
  exact ((η.continuous.comp continuous_snd.fst).mul (η.continuous.comp continuous_snd.snd)).mul hi

theorem smoothedAngularKernel_slice (η χ : C(Velocity,ℝ)) (z : Velocity) :
    (fun y => smoothedAngularKernel η χ (z,y)) =
      angularPostCutoffTest η (translatedVelocityTest χ z) := rfl

theorem smoothedAngularKernel_support (η χ : C(Velocity,ℝ))
    (hη : HasCompactSupport η) (z : Velocity) :
    HasCompactSupport (fun y => smoothedAngularKernel η χ (z,y)) := by
  rw [smoothedAngularKernel_slice]
  exact angularPostCutoffTest_hasCompactSupport η (translatedVelocityTest χ z) hη

theorem smoothedAngularKernel_bounded (η χ : C(Velocity,ℝ))
    (hη : HasCompactSupport η) (hχ : HasCompactSupport χ) :
    ∃ C : ℝ, ∀ p, |smoothedAngularKernel η χ p| ≤ C := by
  let w : C(Velocity × Velocity,ℝ) :=
    ⟨fun y => (η y.1*η y.2)*(‖y.1‖+‖y.2‖),by fun_prop⟩
  have hw : HasCompactSupport w := (tensorTest_hasCompactSupport hη hη).mul_right
  obtain ⟨B,hB⟩ := w.continuous.bounded_above_of_compact_support hw
  obtain ⟨D,hD⟩ := χ.continuous.bounded_above_of_compact_support hχ
  have hD0 : 0 ≤ D := (abs_nonneg (χ 0)).trans (hD 0)
  refine ⟨sphereArea.real univ*(B*D),fun p => ?_⟩
  have hc : ∀ ω : Sphere, ‖(η p.2.1*η p.2.2)*
      (collisionKernel p.2.1 p.2.2 ω*χ (p.1-scatterLeft p.2.1 p.2.2 ω))‖ ≤ B*D := by
    intro ω
    have hk := (collisionKernel_le_norm p.2.1 p.2.2 ω).trans (norm_sub_le _ _)
    have hk0 := collisionKernel_nonneg p.2.1 p.2.2 ω
    calc
      _ = |η p.2.1*η p.2.2| * (collisionKernel p.2.1 p.2.2 ω *
          |χ (p.1-scatterLeft p.2.1 p.2.2 ω)|) := by
        rw [norm_mul (η p.2.1*η p.2.2) _,norm_mul (collisionKernel p.2.1 p.2.2 ω) _,
          Real.norm_of_nonneg hk0]
        rfl
      _ ≤ |η p.2.1*η p.2.2| * ((‖p.2.1‖+‖p.2.2‖)*D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hk (hD _) (abs_nonneg _) (by positivity)) (abs_nonneg _)
      _ = |w p.2| * D := by
        dsimp only [w,ContinuousMap.coe_mk]
        simp only [abs_mul,abs_of_nonneg (by positivity : 0 ≤ ‖p.2.1‖+‖p.2.2‖)]
        ring
      _ ≤ B*D := mul_le_mul_of_nonneg_right (hB _) hD0
  have h := norm_integral_le_of_norm_le (integrable_const (μ := sphereArea) (B*D)) (ae_of_all _ hc)
  rw [integral_const] at h
  simpa only [smoothedAngularKernel,integral_const_mul,Real.norm_eq_abs,smul_eq_mul] using h

end BoltzmannNonuniqueness.Compactness

end

end

section

/-! # The outgoing smoothing kernel is the actual incoming physical collision rate -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*}

theorem massNormalizedPreRate_eq_pair (f : X × Velocity → ℝ)
    (z : (X × (Velocity × Velocity)) × Sphere) :
    massNormalizedPreRate f z = collisionKernel z.1.2.1 z.1.2.2 z.2*
      normalizedPair volume f z.1 := by
  unfold massNormalizedPreRate preRate normalizedPair normalizedTensor
  ring

theorem smoothed_preRate_angular_identity (η χ : C(Velocity,ℝ))
    (f : X × Velocity → ℝ) (x : X) (v : Velocity) (y : Velocity × Velocity) :
    (∫ ω : Sphere, (η y.1*η y.2)*χ (v-scatterLeft y.1 y.2 ω)*
      massNormalizedPreRate f ((x,y),ω) ∂sphereArea) =
    smoothedAngularKernel η χ (v,y)*normalizedPair volume f (x,y) := by
  calc
    _ = ∫ ω : Sphere, (η y.1*η y.2)*
        (collisionKernel y.1 y.2 ω*χ (v-scatterLeft y.1 y.2 ω))*
        normalizedPair volume f (x,y) ∂sphereArea := by
      apply integral_congr_ae
      filter_upwards [] with ω
      rw [massNormalizedPreRate_eq_pair]
      ring
    _ = _ := by rw [integral_mul_const,integral_const_mul]; rfl

theorem smoothed_preRate_pair_identity (η χ : C(Velocity,ℝ))
    (f : X × Velocity → ℝ) (x : X) (v : Velocity) :
    (∫ y : Velocity × Velocity, ∫ ω : Sphere,
      (η y.1*η y.2)*χ (v-scatterLeft y.1 y.2 ω)*
        massNormalizedPreRate f ((x,y),ω) ∂sphereArea) =
    ∫ y : Velocity × Velocity, smoothedAngularKernel η χ (v,y)*normalizedPair volume f (x,y) := by
  simp_rw [smoothed_preRate_angular_identity]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

section

/-! # The exact physical pre/post change of variables for the smoothed gain -/
noncomputable section
open MeasureTheory
namespace BoltzmannNonuniqueness.CollisionCompactness
open Compactness
variable {X : Type*}

theorem smoothed_pre_post_fixed_normal (η χ : C(Velocity,ℝ))
    (f : X × Velocity → ℝ) (x : X) (v : Velocity) (ω : Sphere) :
    (∫ y : Velocity × Velocity, (η y.1*η y.2)*χ (v-scatterLeft y.1 y.2 ω)*
      massNormalizedPreRate f ((x,y),ω)) =
    ∫ y : Velocity × Velocity,
      (η (scatterLeft y.1 y.2 ω)*η (scatterRight y.1 y.2 ω))*χ (v-y.1)*
        massNormalizedPostRate f ((x,y),ω) := by
  have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  let a : Velocity × Velocity → ℝ := fun y =>
    (η (scatterLeft y.1 y.2 ω)*η (scatterRight y.1 y.2 ω))*χ (v-y.1)*
      massNormalizedPostRate f ((x,y),ω)
  have hr y : massNormalizedPostRate f ((x,scatterPair ω y),ω) =
      massNormalizedPreRate f ((x,y),ω) := by
    change massNormalizedPreRate f ((x,scatterPair ω (scatterPair ω y)),ω) = _
    rw [scatterPair_involutive ω hω y]
  have he y : a (scatterPair ω y) = (η y.1*η y.2)*χ (v-scatterLeft y.1 y.2 ω)*
      massNormalizedPreRate f ((x,y),ω) := by
    change (η (scatterPair ω (scatterPair ω y)).1*η (scatterPair ω (scatterPair ω y)).2)*
      χ (v-(scatterPair ω y).1)*massNormalizedPostRate f ((x,scatterPair ω y),ω) = _
    rw [scatterPair_involutive ω hω y,hr]
    rfl
  have h := integral_scatterPair ω hω a
  simp_rw [he] at h
  exact h

theorem smoothed_pre_post_normals (η χ : C(Velocity,ℝ))
    (f : X × Velocity → ℝ) (x : X) (v : Velocity) :
    (∫ ω : Sphere, (∫ y : Velocity × Velocity,
      (η y.1*η y.2)*χ (v-scatterLeft y.1 y.2 ω)*massNormalizedPreRate f ((x,y),ω)) ∂sphereArea) =
    ∫ ω : Sphere, (∫ y : Velocity × Velocity,
      (η (scatterLeft y.1 y.2 ω)*η (scatterRight y.1 y.2 ω))*χ (v-y.1)*
        massNormalizedPostRate f ((x,y),ω)) ∂sphereArea := by
  simp_rw [smoothed_pre_post_fixed_normal]

end BoltzmannNonuniqueness.CollisionCompactness

end

end

end OAI
