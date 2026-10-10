import OAI.Geometry.Kahler.BaseSphere

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

private def suMap (a b : ℂ) : Base →ₗ[ℂ] Base :=
  Matrix.toEuclideanLin !![a,b; -star b,star a]

private lemma suMap_norm (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) (z : Base) :
    ‖suMap a b z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two]
  have h0 : suMap a b z 0 = a*z 0+b*z 1 := by simp [suMap,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]
  have h1 : suMap a b z 1 = -star b*z 0+star a*z 1 := by simp [suMap,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]
  rw [h0,h1]
  simp only [← Complex.normSq_eq_norm_sq]
  calc
    _ = (Complex.normSq a+Complex.normSq b)*(Complex.normSq (z 0)+Complex.normSq (z 1)) := by
      simp [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
        Complex.neg_re,Complex.neg_im,Complex.conj_re,Complex.conj_im]
      ring
    _ = _ := by rw [h,one_mul]

def suIsometry (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) : Base ≃ₗᵢ[ℂ] Base :=
  let L : Base →ₗᵢ[ℂ] Base := ⟨suMap a b,suMap_norm a b h⟩
  LinearIsometryEquiv.ofSurjective L (LinearMap.surjective_of_injective L.injective)

@[simp] lemma suIsometry_zero (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) (z : Base) :
    suIsometry a b h z 0 = a*z 0+b*z 1 := by
  simp [suIsometry,suMap,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]

@[simp] lemma suIsometry_one (a b : ℂ) (h : Complex.normSq a + Complex.normSq b = 1) (z : Base) :
    suIsometry a b h z 1 = -star b*z 0+star a*z 1 := by
  simp [suIsometry,suMap,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]

def rotationIsometry (t : ℝ) : Base ≃ₗᵢ[ℂ] Base :=
  suIsometry (Real.cos t) (Real.sin t) (by
    simp only [Complex.normSq_ofReal]
    nlinarith [Real.cos_sq_add_sin_sq t])

def diagIsometry (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) : Base ≃ₗᵢ[ℂ] Base :=
  let L : Base →ₗᵢ[ℂ] Base :=
    { toLinearMap := Matrix.toEuclideanLin !![a,0;0,b]
      norm_map' z := by
        apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        simp [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two,Matrix.toLpLin_apply,
          dotProduct,ha,hb] }
  LinearIsometryEquiv.ofSurjective L (LinearMap.surjective_of_injective L.injective)

@[simp] lemma diagIsometry_zero (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (z : Base) :
    diagIsometry a b ha hb z 0 = a*z 0 := by
  simp [diagIsometry,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]

@[simp] lemma diagIsometry_one (a b : ℂ) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (z : Base) :
    diagIsometry a b ha hb z 1 = b*z 1 := by
  simp [diagIsometry,Matrix.toLpLin_apply,dotProduct,Fin.sum_univ_two]

def radialU (ξ : Sphere) : ℝ := Complex.normSq ((ξ:Base) 0)
def radialV (ξ : Sphere) : ℝ := Complex.normSq ((ξ:Base) 1)
def radialR (ξ : Sphere) : ℝ := (((ξ:Base) 0)*star ((ξ:Base) 1)).re

def radialJ (ξ : Sphere) : ℝ := (((ξ:Base) 0)*star ((ξ:Base) 1)).im

lemma radialUV (ξ : Sphere) : radialU ξ + radialV ξ = 1 := by
  have h := congrArg (fun r : ℝ => r^2) (sphere_norm ξ)
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two] at h
  simpa only [one_pow,← Complex.normSq_eq_norm_sq,radialU,radialV] using h

lemma radialRI (ξ : Sphere) : radialR ξ^2+radialJ ξ^2 = radialU ξ*radialV ξ := by
  simp [radialR,radialJ,radialU,radialV,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,
    Complex.conj_re,Complex.conj_im]
  ring

lemma radialU_continuous : Continuous radialU := by
  exact Complex.continuous_normSq.comp ((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val)
lemma radialV_continuous : Continuous radialV := by
  exact Complex.continuous_normSq.comp ((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val)
lemma radialR_continuous : Continuous radialR := by
  exact Complex.continuous_re.comp (((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).mul
    (((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val).star))
lemma radialJ_continuous : Continuous radialJ := by
  exact Complex.continuous_im.comp (((EuclideanSpace.proj 0).continuous.comp continuous_subtype_val).mul
    (((EuclideanSpace.proj 1).continuous.comp continuous_subtype_val).star))

lemma radial_phase_square (n : ℕ) :
    (∫ ξ, radialU ξ^n * radialR ξ^2 ∂sigma) =
      ∫ ξ, radialU ξ^n * radialJ ξ^2 ∂sigma := by
  have hi := sigma_integral_unitary (diagIsometry Complex.I 1 (by simp) (by simp))
    (fun ξ => radialU ξ^n * radialR ξ^2)
  have he : ∀ ξ : Sphere,
      radialU (sphereAction (diagIsometry Complex.I 1 (by simp) (by simp)) ξ)^n *
      radialR (sphereAction (diagIsometry Complex.I 1 (by simp) (by simp)) ξ)^2 =
      radialU ξ^n*radialJ ξ^2 := by
    intro ξ
    simp [radialU,radialR,radialJ,Complex.normSq_mul,mul_assoc]
    left
    ring
  simpa only [he] using hi.symm

lemma radial_square_integral (n : ℕ) :
    2*(∫ ξ, radialU ξ^n*radialR ξ^2 ∂sigma) =
      ∫ ξ, radialU ξ^(n+1)*radialV ξ ∂sigma := by
  have hR : Integrable (fun ξ => radialU ξ^n*radialR ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialR_continuous.pow 2))
  have hJ : Integrable (fun ξ => radialU ξ^n*radialJ ξ^2) sigma :=
    continuous_integrable ((radialU_continuous.pow n).mul (radialJ_continuous.pow 2))
  calc
    _ = (∫ ξ, radialU ξ^n*radialR ξ^2 ∂sigma) +
        (∫ ξ, radialU ξ^n*radialJ ξ^2 ∂sigma) := by rw [← radial_phase_square n]; ring
    _ = ∫ ξ, radialU ξ^n*radialR ξ^2 + radialU ξ^n*radialJ ξ^2 ∂sigma :=
      (integral_add hR hJ).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [← mul_add,radialRI,pow_succ]
      ring

end PinchedHartogs.BaseConstruction

end

end OAI
