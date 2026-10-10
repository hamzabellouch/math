import OAI.MathematicalPhysics.Boltzmann.Branching.NormalGainMeasureActions

namespace OAI

section

/-! # A polynomial radial extension of the normal-angle reflection map

On the positive hemisphere this quadratic map is injective. Its radial coordinate
is squared, allowing the angular change of variables to be proved in ambient space.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

def radialReflection (e : Sphere) (x : Velocity) : Velocity :=
  ‖x‖^2 • e.1 - (2*inner ℝ e.1 x) • x

theorem radialReflection_continuous (e : Sphere) : Continuous (radialReflection e) := by
  unfold radialReflection
  fun_prop

theorem radialReflection_inner (e : Sphere) (x : Velocity) :
    inner ℝ e.1 (radialReflection e x) = ‖x‖^2-2*(inner ℝ e.1 x)^2 := by
  unfold radialReflection
  rw [inner_sub_right,real_inner_smul_right,real_inner_smul_right,
    real_inner_self_eq_norm_sq,mem_sphere_zero_iff_norm.mp e.property]
  ring

theorem radialReflection_norm (e : Sphere) (x : Velocity) :
    ‖radialReflection e x‖ = ‖x‖^2 := by
  have hs : ‖radialReflection e x‖^2 = (‖x‖^2)^2 := by
    unfold radialReflection
    rw [norm_sub_sq_real,real_inner_smul_left,real_inner_smul_right,norm_smul,norm_smul]
    simp only [Real.norm_eq_abs,mul_pow,sq_abs,mem_sphere_zero_iff_norm.mp e.property]
    ring
  nlinarith [norm_nonneg (radialReflection e x),sq_nonneg ‖x‖]

theorem radialReflection_sphere (e n : Sphere) (r : ℝ) :
    radialReflection e (r • n.1) = r^2 • (normalReflection e n).1 := by
  unfold radialReflection normalReflection normalReflectionVector
  rw [norm_smul,real_inner_smul_right]
  simp only [Real.norm_eq_abs,sq_abs,mem_sphere_zero_iff_norm.mp n.property,mul_one]
  module

theorem radialReflection_injOn (e : Sphere) :
    InjOn (radialReflection e) {x | 0 < inner ℝ e.1 x} := by
  intro x hx y hy hxy
  have hn : ‖x‖^2 = ‖y‖^2 := by
    simpa only [radialReflection_norm] using congrArg norm hxy
  have hi : inner ℝ e.1 x = inner ℝ e.1 y := by
    have h := congrArg (inner ℝ e.1) hxy
    rw [radialReflection_inner,radialReflection_inner,hn] at h
    have hx' : 0 < inner ℝ e.1 x := hx
    have hy' : 0 < inner ℝ e.1 y := hy
    nlinarith
  have hc : (2*inner ℝ e.1 x) • x = (2*inner ℝ e.1 x) • y := by
    unfold radialReflection at hxy
    rw [hn,hi] at hxy
    rw [hi]
    exact sub_right_injective hxy
  exact (smul_right_injective _ (ne_of_gt (mul_pos (by norm_num) hx))) hc

end BoltzmannNonuniqueness

end

end

section

/-! # Image of the positive half-space under the radial reflection map -/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem radialReflection_image (e : Sphere) :
    radialReflection e '' {x | 0 < inner ℝ e.1 x} =
      {y | inner ℝ e.1 y < ‖y‖} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change inner ℝ e.1 (radialReflection e x) < ‖radialReflection e x‖
    rw [radialReflection_inner,radialReflection_norm]
    have hx' : 0 < inner ℝ e.1 x := hx
    nlinarith [sq_pos_of_pos hx']
  · intro hy
    have ha : 0 < ‖y‖-inner ℝ e.1 y := sub_pos.mpr hy
    let a : ℝ := ‖y‖-inner ℝ e.1 y
    let d : ℝ := Real.sqrt (2*a)
    let z : Velocity := ‖y‖ • e.1-y
    have hd : 0 < d := Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
    have hd2 : d^2 = 2*a := Real.sq_sqrt (by positivity)
    have hi : inner ℝ e.1 z = a := by
      dsimp [z,a]
      rw [inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
        mem_sphere_zero_iff_norm.mp e.property]
      ring
    have hz : ‖z‖^2 = 2*‖y‖*a := by
      dsimp [z,a]
      rw [norm_sub_sq_real,norm_smul,real_inner_smul_left]
      simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg y),
        mem_sphere_zero_iff_norm.mp e.property]
      ring
    have hc : (2*(d⁻¹*a))*d⁻¹ = 1 := by
      field_simp
      nlinarith [hd2]
    have hn : ‖d⁻¹ • z‖^2 = ‖y‖ := by
      rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hz]
      field_simp
      nlinarith [hd2]
    refine ⟨d⁻¹ • z,?_,?_⟩
    · change 0 < inner ℝ e.1 (d⁻¹ • z)
      rw [real_inner_smul_right,hi]
      exact mul_pos (inv_pos.mpr hd) ha
    · rw [radialReflection,hn,real_inner_smul_right,hi,smul_smul,hc,one_smul]
      dsimp [z]
      module

end BoltzmannNonuniqueness

end

end

section

/-! # Derivative of the ambient polynomial reflection map -/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace BoltzmannNonuniqueness

def radialReflectionDerivative (e : Sphere) (x : Velocity) : Velocity →L[ℝ] Velocity :=
  ((2:ℝ) • innerSL ℝ x).smulRight e.1 -
    ((2*inner ℝ e.1 x) • ContinuousLinearMap.id ℝ Velocity + ((2:ℝ) • innerSL ℝ e.1).smulRight x)

theorem radialReflection_hasFDerivAt (e : Sphere) (x : Velocity) :
    HasFDerivAt (radialReflection e) (radialReflectionDerivative e x) x := by
  convert! ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.smul_const e.1).sub
    (((innerSL ℝ e.1).hasFDerivAt.const_mul 2).smul (hasFDerivAt_id x)) using 1
  ext h
  simp [radialReflectionDerivative,two_smul]

def northSphere : Sphere :=
  ⟨EuclideanSpace.single 0 1,by simp [EuclideanSpace.single]⟩

theorem radialReflectionDerivative_north (x h : Velocity) :
    radialReflectionDerivative northSphere x h =
      (2*inner ℝ x h) • (EuclideanSpace.single 0 1) -
        (2*h 0) • x - (2*x 0) • h := by
  simp only [radialReflectionDerivative,sub_apply,
    add_apply,ContinuousLinearMap.smulRight_apply,
    smul_apply,innerSL_apply_apply,
    ContinuousLinearMap.id_apply,northSphere,EuclideanSpace.inner_single_left,map_one,one_mul]
  module

theorem radialReflectionDerivative_det_north (x : Velocity) :
    (radialReflectionDerivative northSphere x).det = -8*x 0*‖x‖^2 := by
  change (radialReflectionDerivative northSphere x).toLinearMap.det = _
  rw [← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]
  rw [Matrix.det_fin_three]
  simp only [LinearMap.toMatrix_apply,OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply,EuclideanSpace.basisFun_repr,
    ContinuousLinearMap.coe_coe]
  simp only [radialReflectionDerivative_north,
    EuclideanSpace.inner_single_right,EuclideanSpace.single,PiLp.single_apply,
    PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
  norm_num
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_succ,Fin.isValue,Fin.reduceSucc]
  ring

end BoltzmannNonuniqueness

end

end

section

/-! # Ambient change of variables for the normal-angle reflection -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

namespace BoltzmannNonuniqueness

theorem radialReflection_image_ae (e : Sphere) :
    radialReflection e '' {x | 0 < inner ℝ e.1 x} =ᵐ[volume] (univ : Set Velocity) := by
  rw [radialReflection_image,ae_eq_univ]
  have he : e.1 ≠ 0 := by
    intro h
    have := mem_sphere_zero_iff_norm.mp e.property
    rw [h,norm_zero] at this
    norm_num at this
  have hn : (ℝ ∙ e.1 : Submodule ℝ Velocity) ≠ ⊤ := by
    intro h
    have hd := finrank_span_singleton (K := ℝ) he
    rw [h,finrank_top] at hd
    norm_num [finrank_euclideanSpace] at hd
  apply measure_mono_null (t := (ℝ ∙ e.1 : Submodule ℝ Velocity)) _
    (Measure.addHaar_submodule volume _ hn)
  intro y hy
  have hle : ‖y‖ ≤ inner ℝ e.1 y := le_of_not_gt hy
  have hinner : inner ℝ e.1 y ≤ ‖y‖ := by
    simpa only [mem_sphere_zero_iff_norm.mp e.property,one_mul] using real_inner_le_norm e.1 y
  have hi : inner ℝ e.1 y = ‖y‖ := le_antisymm hinner hle
  have hz : y-‖y‖ • e.1 = 0 := by
    apply norm_eq_zero.mp
    have hs : ‖y-‖y‖ • e.1‖^2 = 0 := by
      rw [norm_sub_sq_real,real_inner_smul_right,real_inner_comm,hi,norm_smul]
      simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg y),
        mem_sphere_zero_iff_norm.mp e.property,mul_one]
      ring
    nlinarith [norm_nonneg (y-‖y‖ • e.1)]
  rw [sub_eq_zero] at hz
  rw [hz]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem lintegral_radialReflection_north (g : Velocity → ℝ≥0∞) :
    (∫⁻ y, g y) = ∫⁻ x in {x : Velocity | 0 < x 0},
      ENNReal.ofReal (8*x 0*‖x‖^2) * g (radialReflection northSphere x) := by
  have hi : {x : Velocity | 0 < inner ℝ northSphere.1 x} = {x : Velocity | 0 < x 0} := by
    ext x
    simp [northSphere,EuclideanSpace.inner_single_left]
  have hs : MeasurableSet {x : Velocity | 0 < x 0} := measurableSet_lt measurable_const (by fun_prop)
  have hc := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x _ => (radialReflection_hasFDerivAt northSphere x).hasFDerivWithinAt)
    (hi ▸ radialReflection_injOn northSphere) g
  rw [← hi] at hc
  rw [Measure.restrict_congr_set (radialReflection_image_ae northSphere),Measure.restrict_univ] at hc
  rw [hi] at hc
  rw [hc]
  apply setLIntegral_congr_fun hs
  intro x hx
  dsimp only
  rw [radialReflectionDerivative_det_north]
  congr 2
  rw [show -8*x 0*‖x‖^2 = -(8*x 0*‖x‖^2) by ring,abs_neg,abs_of_nonneg]
  exact mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hx)) (sq_nonneg _)

end BoltzmannNonuniqueness

end

end

end OAI
