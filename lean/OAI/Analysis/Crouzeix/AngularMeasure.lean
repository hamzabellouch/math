import Mathlib
import OAI.Analysis.Crouzeix.AngularMoments

namespace OAI

/-! Angular Measure. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

open Boundary

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U) (R : InteriorCollar U)

def interiorAngle : C(CircleSpace, CircleSpace) :=
  ⟨fun t => (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm
    ⟨C.interiorBoundary R t, by exact mem_sphere_zero_iff_norm.mpr (C.norm_interiorBoundary R t)⟩,
    (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).symm.continuous.comp
      ((C.interiorBoundary R).continuous.subtype_mk _)⟩

lemma circleCoordinate_interiorAngle (t : CircleSpace) :
    circleCoordinate (C.interiorAngle R t) = C.interiorBoundary R t := by
  simp only [circleCoordinate, fourier_one]
  rw [← AddCircle.homeomorphCircle_apply (by norm_num : (1 : ℝ) ≠ 0)]
  exact congrArg Subtype.val ((AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)).apply_symm_apply _)

lemma fourier_interiorAngle (j : ℤ) (t : CircleSpace) :
    fourier j (C.interiorAngle R t) = (C.interiorBoundary R t)^j := by
  rw [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  have he := C.circleCoordinate_interiorAngle R t
  simp only [circleCoordinate, fourier_one] at he
  rw [he]

def angularIntegralCLM : C(CircleSpace, ℂ) →L[ℂ] ℂ := by
  have hi (f : C(CircleSpace, ℂ)) : Integrable
      (fun t => C.angularJacobian R t * f (C.interiorAngle R t)) circleMeasure :=
    ((C.angularJacobian R).continuous.mul (f.continuous.comp (C.interiorAngle R).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let L : C(CircleSpace, ℂ) →ₗ[ℂ] ℂ := {
    toFun f := ∫ t, C.angularJacobian R t * f (C.interiorAngle R t) ∂circleMeasure
    map_add' f g := by
      simp only [ContinuousMap.add_apply, mul_add]
      exact integral_add (hi f) (hi g)
    map_smul' c f := by
      simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
      simp_rw [mul_left_comm _ c, ← smul_eq_mul c]
      exact integral_smul c _ }
  refine L.mkContinuous ‖C.angularJacobian R‖ fun f => ?_
  have hb : ∀ᵐ t ∂circleMeasure, ‖C.angularJacobian R t * f (C.interiorAngle R t)‖ ≤
      ‖C.angularJacobian R‖ * ‖f‖ := Eventually.of_forall fun t => by
    rw [norm_mul]
    exact mul_le_mul ((C.angularJacobian R).norm_coe_le_norm t)
      (f.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, probReal_univ, one_mul, mul_one] using norm_integral_le_of_norm_le_const hb

def circleIntegralCLM : C(CircleSpace, ℂ) →L[ℂ] ℂ := by
  let L : C(CircleSpace, ℂ) →ₗ[ℂ] ℂ := {
    toFun f := ∫ t, f t ∂circleMeasure
    map_add' f g := integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    map_smul' c f := integral_smul c _ }
  refine L.mkContinuous 1 fun f => ?_
  simpa only [L, LinearMap.coe_mk, AddHom.coe_mk, probReal_univ, one_mul, mul_one] using norm_integral_le_of_norm_le_const
    (Eventually.of_forall f.norm_coe_le_norm : ∀ᵐ t ∂circleMeasure, ‖f t‖ ≤ ‖f‖)

lemma angularIntegralCLM_eq (hU : IsOpen U) (hc : Convex ℝ U) :
    C.angularIntegralCLM R = circleIntegralCLM := by
  apply ContinuousLinearMap.ext_on (s := range (fourier (T := (1 : ℝ))))
  · rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      span_fourier_closure_eq_top, Submodule.top_coe]
  · rintro f ⟨j,rfl⟩
    change (∫ t, C.angularJacobian R t * fourier j (C.interiorAngle R t) ∂circleMeasure) =
      ∫ t, fourier j t ∂circleMeasure
    simp_rw [C.fourier_interiorAngle]
    rw [C.integral_angularJacobian_zpow R hU hc, Disk.integral_fourier]

lemma integral_angularChange {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hU : IsOpen U) (hc : Convex ℝ U) (f : C(CircleSpace, E)) :
    (∫ t, C.angularJacobian R t • f (C.interiorAngle R t) ∂circleMeasure) =
      ∫ t, f t ∂circleMeasure := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro l
  have h1 : Integrable (fun t => C.angularJacobian R t • f (C.interiorAngle R t)) circleMeasure :=
    ((C.angularJacobian R).continuous.smul (f.continuous.comp (C.interiorAngle R).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable f circleMeasure := f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← l.integral_comp_comm h1, ← l.integral_comp_comm h2]
  simp only [map_smul, smul_eq_mul]
  exact congrArg (fun L : C(CircleSpace, ℂ) →L[ℂ] ℂ => L ⟨l ∘ f, l.continuous.comp f.continuous⟩)
    (C.angularIntegralCLM_eq R hU hc)

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
