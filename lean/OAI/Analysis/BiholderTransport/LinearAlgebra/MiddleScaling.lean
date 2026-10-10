import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.CompactQuadratic
import OAI.Analysis.BiholderTransport.Regularity.NormMinMax

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleScaling
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleHessian_scaled_ray (z : TangentBundle 𝓘(ℝ,Model n) M)
    (h T : ℝ) (hT : T ≠ 0) :
    HEq (middleHessian (tangentScale T z) (h/T) 1) (T • middleHessian z h T) := by
  unfold middleHessian
  rw [sprayFlow_scale,mul_div_cancel₀ _ hT]
  change HEq
    ((h/T)⁻¹ • normalHessian (sprayFlow h z).1 (-(h/T) • (T • (sprayFlow h z).2)) +
      (1-h/T)⁻¹ • normalHessian (sprayFlow h z).1 ((1-h/T) • (T • (sprayFlow h z).2)))
    (T • (h⁻¹ • normalHessian (sprayFlow h z).1 ((-h) • (sprayFlow h z).2) +
      (T-h)⁻¹ • normalHessian (sprayFlow h z).1 ((T-h) • (sprayFlow h z).2)))
  simp only [smul_smul]
  have h1 : -(h/T)*T = -h := by field_simp
  have h2 : (1-h/T)*T = T-h := by field_simp
  rw [h1,h2]
  apply heq_of_eq
  ext v w
  simp only [add_apply,smul_apply,smul_eq_mul]
  have h3 : (h/T)⁻¹ = T*h⁻¹ := by simp [div_eq_mul_inv]
  have h4 : (1-h/T)⁻¹ = T*(T-h)⁻¹ := by
    rw [show 1-h/T=(T-h)/T by field_simp]
    simp [div_eq_mul_inv]
  rw [h3,h4]
  ring

end MiddleScaling
end WeakMTWTransport

end

end

section

noncomputable section
namespace WeakMTWTransport
section SpectralScaling
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

lemma ordered_singularValues_positive_smul (A : E →ₗ[ℝ] F) {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    (t • A).singularValues i = t * A.singularValues i := by
  have h1 := ordered_singularValues_pullback (A := t • A) (B := A)
    (LinearMap.id) ht.le (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1*‖v‖; simp)
    (fun v => by simp only [LinearMap.smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_pos ht,LinearMap.id_apply]; exact le_rfl) hn hn i
  have h2 := ordered_singularValues_pullback (A := A) (B := t • A)
    (LinearMap.id) (inv_nonneg.mpr ht.le) (by norm_num : (0:ℝ) ≤ 1)
    (fun v => by change ‖v‖ ≤ 1*‖v‖; simp)
    (fun v => by simp only [LinearMap.smul_apply,norm_smul,Real.norm_eq_abs,
      abs_of_pos ht,LinearMap.id_apply]; rw [←mul_assoc,inv_mul_cancel₀ ht.ne',one_mul]) hn hn i
  simp only [mul_one] at h1 h2
  apply le_antisymm h1
  have H := mul_le_mul_of_nonneg_left h2 ht.le
  simpa only [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] using H
end SpectralScaling
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleSingular
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def intrinsicBilinearOperator (y : M)
    (B : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ) :
    TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y :=
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B

def intrinsicBilinearSingular (y : M)
    (B : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)
    (i : ℕ) : ℝ := (intrinsicBilinearOperator y B).toLinearMap.singularValues i

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma intrinsicBilinearSingular_heq {x y : M} (hxy : x=y)
    {B : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] ℝ}
    {C : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ}
    (hBC : HEq B C) (i : ℕ) :
    intrinsicBilinearSingular x B i=intrinsicBilinearSingular y C i := by
  subst y
  cases hBC
  rfl

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma intrinsicBilinearOperator_smul (y : M)
    (B : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)
    (t : ℝ) : intrinsicBilinearOperator y (t • B)=t • intrinsicBilinearOperator y B := by
  ext v
  simp only [intrinsicBilinearOperator,comp_apply,smul_apply,map_smul]

omit [CompactSpace M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma intrinsicBilinearSingular_pos_smul (y : M)
    (B : TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] TangentSpace 𝓘(ℝ,Model n) y →L[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) (i : Fin (Module.finrank ℝ (Model n))) :
    intrinsicBilinearSingular y (t • B) i=t*intrinsicBilinearSingular y B i := by
  unfold intrinsicBilinearSingular
  rw [intrinsicBilinearOperator_smul]
  exact ordered_singularValues_positive_smul (intrinsicBilinearOperator y B).toLinearMap ht rfl i

def middleSingularValue (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) (i : ℕ) : ℝ :=
  intrinsicBilinearSingular (sprayFlow h z).1 (middleHessian z h T) i

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma middleSingularValue_scaled_ray (z : TangentBundle 𝓘(ℝ,Model n) M)
    (h T : ℝ) (hT : 0 < T) (i : Fin (Module.finrank ℝ (Model n))) :
    middleSingularValue (tangentScale T z) (h/T) 1 i = T*middleSingularValue z h T i := by
  have hbase : (sprayFlow (h/T) (tangentScale T z)).1=(sprayFlow h z).1 := by
    rw [sprayFlow_scale,mul_div_cancel₀ _ hT.ne']
    rfl
  have H := intrinsicBilinearSingular_heq hbase (middleHessian_scaled_ray z h T hT.ne') i
  change middleSingularValue (tangentScale T z) (h/T) 1 i = _ at H
  rw [H,intrinsicBilinearSingular_pos_smul _ _ hT]
  rfl

end MiddleSingular
end WeakMTWTransport

end

end

end

end OAI
