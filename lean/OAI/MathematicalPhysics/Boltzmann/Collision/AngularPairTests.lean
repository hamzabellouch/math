import OAI.MathematicalPhysics.Boltzmann.Branching.SupportedTensorConvergence
import OAI.MathematicalPhysics.Boltzmann.Model
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

namespace OAI

section

/-!
# Angular normalization of the hard-sphere collision kernel

The angular measure is the ordinary area measure `volume.toSphere`. Its mass is
`4 * π`; the absolute normal component integrates to `2 * π * ‖g‖`.
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

instance sphereArea_isFiniteMeasure : IsFiniteMeasure sphereArea := by
  unfold sphereArea
  infer_instance

theorem sphereArea_real_univ : sphereArea.real univ = 4 * Real.pi := by
  rw [sphereArea, Measure.toSphere_real_apply_univ]
  simp only [Fintype.card_fin, finrank_euclideanSpace]
  rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  norm_num
  ring

theorem sphereArea_univ : sphereArea univ = ENNReal.ofReal (4 * Real.pi) := by
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (by positivity)]
  exact sphereArea_real_univ

private theorem gaussian_radial_one :
    (∫ r : ℝ in Ioi 0, r * Real.exp (-r ^ 2)) = 1 / 2 := by
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 2)))
    (fun r : ℝ => Real.exp (-r ^ 2))
  have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin 2)) (b := 1) zero_lt_one
  simp only [one_mul, neg_mul, finrank_euclideanSpace, Fintype.card_fin] at hg
  rw [hg] at h
  rw [Measure.real, EuclideanSpace.volume_ball_fin_two] at h
  norm_num [ENNReal.toReal_ofReal, Real.pi_pos.le] at h
  nlinarith [Real.pi_pos]

private theorem gaussian_radial_three :
    (∫ r : ℝ in Ioi 0, r ^ 3 * Real.exp (-r ^ 2)) = 1 / 2 := by
  have h := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin 4)))
    (fun r : ℝ => Real.exp (-r ^ 2))
  have hg := GaussianFourier.integral_rexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin 4)) (b := 1) zero_lt_one
  simp only [one_mul, neg_mul, finrank_euclideanSpace, Fintype.card_fin] at hg
  rw [hg] at h
  rw [Measure.real, InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)] at h
  simp only [ENNReal.ofReal_one, one_pow, one_mul] at h
  rw [ENNReal.toReal_ofReal (by positivity)] at h
  norm_num at h
  nlinarith [sq_pos_of_pos Real.pi_pos]

private theorem gaussian_abs_integral :
    (∫ x : ℝ, |x| * Real.exp (-x ^ 2)) = 1 := by
  have h := integral_fun_norm_addHaar (volume : Measure ℝ)
    (fun r : ℝ => r * Real.exp (-r ^ 2))
  norm_num [Measure.real, Real.volume_ball, Real.norm_eq_abs, sq_abs,
    gaussian_radial_one] at h
  exact h

private theorem gaussian_coordinate_integral :
    (∫ x : Velocity, |x 0| * Real.exp (-‖x‖ ^ 2)) = Real.pi := by
  rw [← (PiLp.volume_preserving_toLp (Fin 3)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  let f : Fin 3 → ℝ → ℝ := fun i t =>
    if i = 0 then |t| * Real.exp (-t ^ 2) else Real.exp (-t ^ 2)
  have hf : ∀ x : Fin 3 → ℝ,
      |WithLp.toLp 2 x 0| * Real.exp (-‖WithLp.toLp 2 x‖ ^ 2) = ∏ i, f i (x i) := by
    intro x
    simp [f, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, Fin.prod_univ_succ,
      Real.exp_add, mul_assoc]
    left
    ring
  have hg : (∫ x : ℝ, Real.exp (-x ^ 2)) = Real.sqrt Real.pi := by
    simpa only [neg_mul, one_mul, div_one] using integral_gaussian 1
  simp_rw [hf]
  rw [integral_fintype_prod_volume_eq_prod]
  simp [f, Fin.prod_univ_succ, gaussian_abs_integral, hg,
    Real.sq_sqrt Real.pi_pos.le]

private theorem gaussian_linear_integral (g : Velocity) :
    (∫ x : Velocity, |inner ℝ g x| * Real.exp (-‖x‖ ^ 2)) = Real.pi * ‖g‖ := by
  let a : Velocity := EuclideanSpace.single 0 ‖g‖
  let R : Velocity ≃ₗᵢ[ℝ] Velocity := (ℝ ∙ (g - a))ᗮ.reflection
  have hnorm : ‖g‖ = ‖a‖ := by simp [a, EuclideanSpace.single, PiLp.norm_single]
  have hRg : R g = a := Submodule.reflection_sub hnorm
  have hinner (x : Velocity) : inner ℝ g (R x) = ‖g‖ * x 0 := by
    have h := R.inner_map_eq_flip g x
    rw [hRg] at h
    simpa [R, a, EuclideanSpace.inner_single_left] using h.symm
  rw [← R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding]
  simp_rw [hinner, R.norm_map, abs_mul, abs_of_nonneg (norm_nonneg g), mul_assoc]
  rw [integral_const_mul, gaussian_coordinate_integral]
  ring

private theorem gaussian_radial_weighted :
    (∫ r : Ioi (0 : ℝ), (r : ℝ) * Real.exp (-(r : ℝ) ^ 2)
      ∂Measure.volumeIoiPow 2) = 1 / 2 := by
  rw [Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  rw [integral_subtype_comap measurableSet_Ioi
    (fun r : ℝ => r ^ 2 * (r * Real.exp (-r ^ 2)))]
  convert gaussian_radial_three using 1
  congr 1
  funext r
  ring

private theorem gaussian_polar_identity (g : Velocity) :
    (∫ x : Velocity, |inner ℝ g x| * Real.exp (-‖x‖ ^ 2)) =
      (∫ ω : Sphere, |inner ℝ g (ω : Velocity)| ∂sphereArea) * (1 / 2) := by
  let F : Velocity → ℝ := fun x => |inner ℝ g x| * Real.exp (-‖x‖ ^ 2)
  let H := homeomorphUnitSphereProd Velocity
  have hpolar := (volume : Measure Velocity).measurePreserving_homeomorphUnitSphereProd.integral_comp
    H.measurableEmbedding (fun p => F (H.symm p))
  change (∫ x, F x) = _
  calc
    (∫ x : Velocity, F x) =
        ∫ x : ({0}ᶜ : Set Velocity), F x ∂((volume : Measure Velocity).comap (↑)) := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl,
        restrict_compl_singleton]
    _ = ∫ p : Sphere × Ioi (0 : ℝ), F ((p.2 : ℝ) • (p.1 : Velocity))
        ∂sphereArea.prod (Measure.volumeIoiPow 2) := by
      simpa only [sphereArea, H, Homeomorph.symm_apply_apply,
        homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub] using hpolar
    _ = ∫ p : Sphere × Ioi (0 : ℝ),
        |inner ℝ g (p.1 : Velocity)| * ((p.2 : ℝ) * Real.exp (-(p.2 : ℝ) ^ 2))
        ∂sphereArea.prod (Measure.volumeIoiPow 2) := by
      apply integral_congr_ae
      filter_upwards [] with p
      have hω : ‖(p.1 : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp p.1.property
      have hr : (0 : ℝ) < p.2 := p.2.property
      simp [F, inner_smul_right, norm_smul, Real.norm_eq_abs, hω, abs_of_pos hr, mul_assoc,
        mul_left_comm, mul_comm]
    _ = (∫ ω : Sphere, |inner ℝ g (ω : Velocity)| ∂sphereArea) *
        (∫ r : Ioi (0 : ℝ), (r : ℝ) * Real.exp (-(r : ℝ) ^ 2)
          ∂Measure.volumeIoiPow 2) :=
      integral_prod_mul (fun ω : Sphere => |inner ℝ g (ω : Velocity)|)
        (fun r : Ioi (0 : ℝ) => (r : ℝ) * Real.exp (-(r : ℝ) ^ 2))
    _ = _ := by rw [gaussian_radial_weighted]

theorem integrable_abs_inner_sphereArea (g : Velocity) :
    Integrable (fun ω : Sphere => |inner ℝ g (ω : Velocity)|) sphereArea := by
  apply (integrable_const ‖g‖).mono' (by fun_prop)
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_abs]
  have hω : ‖(ω : Velocity)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.property
  simpa only [hω, mul_one] using abs_real_inner_le_norm g (ω : Velocity)

/-- The normal-parametrized hard-sphere angular integral has coefficient `2 * π`. -/
theorem integral_abs_inner_sphereArea (g : Velocity) :
    (∫ ω : Sphere, |inner ℝ g (ω : Velocity)| ∂sphereArea) = 2 * Real.pi * ‖g‖ := by
  have hp := gaussian_polar_identity g
  rw [gaussian_linear_integral] at hp
  linarith

/-- The loss-frequency angular normalization in the manuscript. -/
theorem integral_collisionKernel_sphereArea (v w : Velocity) :
    (∫ ω : Sphere, collisionKernel v w ω ∂sphereArea) = 2 * Real.pi * ‖v - w‖ :=
  integral_abs_inner_sphereArea (v - w)

theorem integrable_collisionKernel_sphereArea (v w : Velocity) :
    Integrable (fun ω : Sphere => collisionKernel v w ω) sphereArea :=
  integrable_abs_inner_sphereArea (v - w)

end BoltzmannNonuniqueness

end

end

section

/-! # Continuous compact pair kernels for the physical outgoing angular law -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Compactness

def angularPostTest (φ : C(Velocity,ℝ)) (p : Velocity × Velocity) : ℝ :=
  ∫ ω : Sphere, collisionKernel p.1 p.2 ω*φ (scatterLeft p.1 p.2 ω) ∂sphereArea

theorem angularPostTest_continuous (φ : C(Velocity,ℝ)) : Continuous (angularPostTest φ) := by
  have hc : Continuous (fun z : (Velocity × Velocity) × Sphere =>
      collisionKernel z.1.1 z.1.2 z.2*φ (scatterLeft z.1.1 z.1.2 z.2)) := by
    unfold collisionKernel scatterLeft normalComponent
    fun_prop
  have h := continuous_parametric_integral_of_continuous (μ := sphereArea)
    (f := fun p : Velocity × Velocity => fun ω : Sphere =>
      collisionKernel p.1 p.2 ω*φ (scatterLeft p.1 p.2 ω)) hc isCompact_univ
  change Continuous (fun p : Velocity × Velocity =>
    ∫ ω : Sphere, collisionKernel p.1 p.2 ω*φ (scatterLeft p.1 p.2 ω) ∂sphereArea)
  simpa only [Measure.restrict_univ] using h

def angularPostCutoffTest (η φ : C(Velocity,ℝ)) : C(Velocity × Velocity,ℝ) :=
  ⟨fun p => (η p.1*η p.2)*angularPostTest φ p,
    ((η.continuous.comp continuous_fst).mul (η.continuous.comp continuous_snd)).mul
      (angularPostTest_continuous φ)⟩

theorem angularPostCutoffTest_hasCompactSupport (η φ : C(Velocity,ℝ))
    (hη : HasCompactSupport η) : HasCompactSupport (angularPostCutoffTest η φ) := by
  exact (tensorTest_hasCompactSupport hη hη).mul_right

end BoltzmannNonuniqueness.Compactness

end

end

end OAI
