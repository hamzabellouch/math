import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.ManifoldComplexDifferential

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.ExteriorForms
open ContinuousAlternatingMap
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma antiDdc_vector_bound (J : E →L[ℝ] E) (D : E →L[ℝ] E →L[ℝ] E) (u v : E) :
    ‖D v u - D u v + D (J u) (J v) - D (J v) (J u)‖ ≤
      2*‖D‖*(1+‖J‖^2)*‖u‖*‖v‖ := by
  have hd (a b : E) : ‖D a b‖ ≤ ‖D‖*‖a‖*‖b‖ :=
    ((D a).le_opNorm b).trans (mul_le_mul_of_nonneg_right (D.le_opNorm a) (norm_nonneg b))
  have hj (a b : E) : ‖D (J a) (J b)‖ ≤ ‖D‖*‖J‖^2*‖a‖*‖b‖ := by
    calc
      _ ≤ ‖D‖*‖J a‖*‖J b‖ := hd _ _
      _ ≤ ‖D‖*(‖J‖*‖a‖)*(‖J‖*‖b‖) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (J.le_opNorm a) (norm_nonneg D))
          (J.le_opNorm b) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ‖D v u - D u v + D (J u) (J v)‖ + ‖D (J v) (J u)‖ := norm_sub_le _ _
    _ ≤ (‖D v u‖+‖D u v‖)+‖D (J u) (J v)‖+‖D (J v) (J u)‖ := by
      exact add_le_add (norm_add_le _ _ |>.trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl
    _ ≤ (‖D‖*‖v‖*‖u‖+‖D‖*‖u‖*‖v‖)+‖D‖*‖J‖^2*‖u‖*‖v‖+‖D‖*‖J‖^2*‖v‖*‖u‖ :=
      add_le_add (add_le_add (add_le_add (hd _ _) (hd _ _)) (hj _ _)) (hj _ _)
    _ = _ := by ring

lemma norm_anti_ddc_evaluation_le {J : E → E →L[ℝ] E} {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hJ : DifferentiableAt ℝ J x)
    (hJJ : ∀ v, J x (J x v) = -v) (u v : E) :
    ‖(extDeriv (dc J f) x ![u,v] - extDeriv (dc J f) x ![J x u,J x v])/2‖ ≤
      ‖fderiv ℝ f x‖ * ‖fderiv ℝ J x‖ * (1+‖J x‖^2) * ‖u‖ * ‖v‖ := by
  rw [anti_ddc_first_order hf hJ hJJ]
  rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  apply (mul_le_mul_of_nonneg_left ((fderiv ℝ f x).le_opNorm _) (by norm_num : (0:ℝ) ≤ 1/2)).trans
  have hb := mul_le_mul_of_nonneg_left
    (antiDdc_vector_bound (J x) (fderiv ℝ J x) u v) (norm_nonneg (fderiv ℝ f x))
  have h := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 1/2)
  convert h using 1; ring
end TamingCompatibility.ExteriorForms

namespace TamingCompatibility.ManifoldForms
open ManifoldHodge ContinuousAlternatingMap
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]

lemma ddc_smooth_closed (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) :
    IsSmooth (exteriorDerivative (complexDifferential J f)) ∧
      IsClosed (exteriorDerivative (complexDifferential J f)) :=
  ⟨(complexDifferential_smooth J hf).exteriorDerivative,
    (complexDifferential_smooth J hf).closed_exteriorDerivative⟩

lemma norm_anti_ddc_chart_le (J : AlmostComplexStructure X) {f : X → ℝ}
    (hf : ContMDiff Model 𝓘(ℝ,ℝ) ∞ f) (p : X) {z : Space}
    (hz : z ∈ (extChartAt Model p).target) :
    ‖pullback (antiInvariantPart J (exteriorDerivative (complexDifferential J f)))
      (extChartAt Model p).symm z‖ ≤
      ‖fderiv ℝ (f ∘ (extChartAt Model p).symm) z‖ * ‖fderiv ℝ (coordinateJ J p) z‖ *
        (1+‖coordinateJ J p z‖^2) := by
  apply ContinuousAlternatingMap.opNorm_le_bound _ (by positivity)
  intro m
  have hm : m = ![m 0,m 1] := by ext i; fin_cases i <;> rfl
  rw [hm]
  rw [anti_ddc_chart_first_order J hf p hz]
  rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have hdf := (fderiv ℝ (f ∘ (extChartAt Model p).symm) z).le_opNorm
    ((fderiv ℝ (coordinateJ J p) z (m 1)) (m 0) - (fderiv ℝ (coordinateJ J p) z (m 0)) (m 1) +
      (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z (m 0))) (coordinateJ J p z (m 1)) -
      (fderiv ℝ (coordinateJ J p) z (coordinateJ J p z (m 1))) (coordinateJ J p z (m 0)))
  have hb := ExteriorForms.antiDdc_vector_bound (coordinateJ J p z) (fderiv ℝ (coordinateJ J p) z) (m 0) (m 1)
  have h := mul_le_mul_of_nonneg_left (hdf.trans
    (mul_le_mul_of_nonneg_left hb (norm_nonneg _))) (by norm_num : (0:ℝ) ≤ 1/2)
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
  convert h using 1
  first | rfl | ring
end TamingCompatibility.ManifoldForms

end
end

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def logPotential (s : ℝ) (z : E) : ℝ := (1/2:ℝ)*Real.log (s^2+‖z‖^2)
def sqrtPotential (s : ℝ) (z : E) : ℝ := Real.sqrt (s^2+‖z‖^2)

omit [InnerProductSpace ℝ E] in
lemma radial_sq_pos {s : ℝ} (hs : 0 < s) (z : E) : 0 < s^2+‖z‖^2 := by positivity

lemma logPotential_fderiv {s : ℝ} (hs : 0 < s) (z : E) :
    fderiv ℝ (logPotential s) z = (s^2+‖z‖^2)⁻¹ • innerSL ℝ z := by
  have h := (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (s^2)).log
    (ne_of_gt (radial_sq_pos hs z))).const_mul (1/2:ℝ)
  rw [show logPotential s = (fun z : E => (1/2:ℝ)*Real.log (s^2+‖z‖^2)) from rfl,h.fderiv]
  ext v
  simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply]
  ring

lemma sqrtPotential_fderiv {s : ℝ} (hs : 0 < s) (z : E) :
    fderiv ℝ (sqrtPotential s) z = (Real.sqrt (s^2+‖z‖^2))⁻¹ • innerSL ℝ z := by
  have h := ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (s^2)).sqrt
    (ne_of_gt (radial_sq_pos hs z))
  rw [show sqrtPotential s = (fun z : E => Real.sqrt (s^2+‖z‖^2)) from rfl,h.fderiv]
  ext v
  simp only [_root_.smul_apply,smul_eq_mul,innerSL_apply_apply]
  ring

lemma logPotential_hessian {s : ℝ} (hs : 0 < s) (z u v : E) :
    fderiv ℝ (fderiv ℝ (logPotential s)) z u v =
      ⟪u,v⟫/(s^2+‖z‖^2) - 2*⟪z,u⟫*⟪z,v⟫/(s^2+‖z‖^2)^2 := by
  have he : fderiv ℝ (logPotential s) = fun z : E => (s^2+‖z‖^2)⁻¹ • innerSL ℝ z :=
    funext (logPotential_fderiv hs)
  rw [he]
  have hi := (hasDerivAt_inv (ne_of_gt (radial_sq_pos hs z))).comp_hasFDerivAt z
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (s^2))
  have h := hi.smul ((innerSL ℝ (E := E)).hasFDerivAt (x := z))
  change HasFDerivAt (fun z : E => (s^2+‖z‖^2)⁻¹ • innerSL ℝ z) _ z at h
  rw [h.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,smul_eq_mul,nsmul_eq_mul,innerSL_apply_apply,Function.comp_apply,Nat.cast_ofNat]
  change (s^2+‖z‖^2)⁻¹ * ⟪u,v⟫ + (-((s^2+‖z‖^2)^2)⁻¹ * (2*⟪z,u⟫))*⟪z,v⟫ = _
  ring

lemma sqrtPotential_hessian {s : ℝ} (hs : 0 < s) (z u v : E) :
    fderiv ℝ (fderiv ℝ (sqrtPotential s)) z u v =
      ⟪u,v⟫/Real.sqrt (s^2+‖z‖^2) -
        ⟪z,u⟫*⟪z,v⟫/(Real.sqrt (s^2+‖z‖^2))^3 := by
  have he : fderiv ℝ (sqrtPotential s) =
      fun z : E => (Real.sqrt (s^2+‖z‖^2))⁻¹ • innerSL ℝ z :=
    funext (sqrtPotential_fderiv hs)
  rw [he]
  have hi := (hasDerivAt_inv (ne_of_gt (Real.sqrt_pos.2 (radial_sq_pos hs z)))).comp_hasFDerivAt z
    (((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add (s^2)).sqrt
    (ne_of_gt (radial_sq_pos hs z)))
  have h := hi.smul ((innerSL ℝ (E := E)).hasFDerivAt (x := z))
  change HasFDerivAt (fun z : E => (Real.sqrt (s^2+‖z‖^2))⁻¹ • innerSL ℝ z) _ z at h
  rw [h.fderiv]
  simp only [_root_.add_apply,ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,smul_eq_mul,nsmul_eq_mul,innerSL_apply_apply,Function.comp_apply,Nat.cast_ofNat]
  change (Real.sqrt (s^2+‖z‖^2))⁻¹ * ⟪u,v⟫ +
    (-((Real.sqrt (s^2+‖z‖^2))^2)⁻¹ * ((1/(2*Real.sqrt (s^2+‖z‖^2)))*(2*⟪z,u⟫)))*⟪z,v⟫ = _
  ring
end TamingCompatibility.RadialPotential

end
end

end
end
end

end OAI
