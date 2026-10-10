import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Tactic.FieldSimp
import OAI.Geometry.NodalSets.Elliptic.BasisDivergence

namespace OAI

namespace Yau.Geometry
open Matrix
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : Type*} [Fintype n] [DecidableEq n]

def basisMetricMatrix (b : Module.Basis n ℝ E) (B : LinearMap.BilinForm ℝ E) : Matrix n n ℝ :=
  LinearMap.toMatrix₂ b b B

def basisMetricFlux (b : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) (i : n) (y : E) : ℝ :=
  Real.sqrt (basisMetricMatrix b (B y)).det *
    ∑ j, (basisMetricMatrix b (B y))⁻¹ i j * fderiv ℝ f y (b j)

def basisMetricLaplacian (b : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) (y : E) : ℝ :=
  (Real.sqrt (basisMetricMatrix b (B y)).det)⁻¹ *
    ∑ i, fderiv ℝ (basisMetricFlux b B f i) y (b i)

lemma basis_change_det_ne_zero (b c : Module.Basis n ℝ E) : (b.toMatrix c).det ≠ 0 := by
  have h := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip c)
  rw [det_mul,det_one] at h
  exact (mul_ne_zero_iff.mp (h ▸ one_ne_zero)).1

lemma basis_change_inverse (b c : Module.Basis n ℝ E) : (b.toMatrix c)⁻¹ = c.toMatrix b :=
  inv_eq_left_inv (c.toMatrix_mul_toMatrix_flip b)

lemma basisMetricMatrix_change (b c : Module.Basis n ℝ E) (B : LinearMap.BilinForm ℝ E) :
    basisMetricMatrix c B = (b.toMatrix c).transpose * basisMetricMatrix b B * b.toMatrix c :=
  (LinearMap.toMatrix₂_mul_basis_toMatrix b b c c B).symm

lemma basisMetricMatrix_volume_change (b c : Module.Basis n ℝ E) (B : LinearMap.BilinForm ℝ E) :
    Real.sqrt (basisMetricMatrix c B).det =
      |(b.toMatrix c).det| * Real.sqrt (basisMetricMatrix b B).det := by
  rw [basisMetricMatrix_change,det_mul,det_mul,det_transpose]
  rw [show (b.toMatrix c).det * (basisMetricMatrix b B).det * (b.toMatrix c).det =
    (b.toMatrix c).det^2 * (basisMetricMatrix b B).det by ring,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs]

omit [DecidableEq n] in
lemma basis_derivative_vector (b c : Module.Basis n ℝ E) (f : E → ℝ) (y : E) :
    (fun j ↦ fderiv ℝ f y (c j)) = (b.toMatrix c).transpose *ᵥ (fun a ↦ fderiv ℝ f y (b a)) := by
  ext j
  conv_lhs => rw [← b.sum_toMatrix_smul_self c j]
  simp only [map_sum,map_smul,smul_eq_mul,mulVec,dotProduct,transpose_apply]

lemma basis_inverse_derivative_vector (b c : Module.Basis n ℝ E)
    (B : LinearMap.BilinForm ℝ E) (f : E → ℝ) (y : E) :
    (basisMetricMatrix c B)⁻¹ *ᵥ (fun j ↦ fderiv ℝ f y (c j)) =
      c.toMatrix b *ᵥ ((basisMetricMatrix b B)⁻¹ *ᵥ (fun a ↦ fderiv ℝ f y (b a))) := by
  rw [basis_derivative_vector b c f y,mulVec_mulVec,basisMetricMatrix_change b c,
    Matrix.mul_inv_rev,Matrix.mul_inv_rev]
  have hc : IsUnit ((b.toMatrix c).transpose.det) := by
    rw [det_transpose]
    exact isUnit_iff_ne_zero.mpr (basis_change_det_ne_zero b c)
  rw [Matrix.mul_assoc,Matrix.mul_assoc,nonsing_inv_mul _ hc,Matrix.mul_one,
    basis_change_inverse, ← mulVec_mulVec]

lemma basisMetricFlux_change (b c : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) (i : n) (y : E) :
    basisMetricFlux c B f i y = |(b.toMatrix c).det| *
      ∑ a, c.toMatrix b i a * basisMetricFlux b B f a y := by
  have h := congrFun (basis_inverse_derivative_vector b c (B y) f y) i
  change (∑ j, _ * _) = _ at h
  rw [basisMetricFlux,basisMetricMatrix_volume_change b c,h]
  simp only [mulVec,dotProduct,basisMetricFlux,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma basisMetricLaplacian_change (b c : Module.Basis n ℝ E) (B : E → LinearMap.BilinForm ℝ E)
    (f : E → ℝ) {y : E} (hF : ∀ i, DifferentiableAt ℝ (basisMetricFlux b B f i) y) :
    basisMetricLaplacian c B f y = basisMetricLaplacian b B f y := by
  have hfun (i : n) : basisMetricFlux c B f i = fun z ↦ |(b.toMatrix c).det| *
      ∑ a, c.toMatrix b i a * basisMetricFlux b B f a z := by
    funext z; exact basisMetricFlux_change b c B f i z
  unfold basisMetricLaplacian
  simp_rw [hfun]
  have hd (i : n) : DifferentiableAt ℝ
      (fun z ↦ ∑ a, c.toMatrix b i a * basisMetricFlux b B f a z) y :=
    by
      convert! (DifferentiableAt.sum (u := Finset.univ)
        (fun a _ ↦ (hF a).const_mul (c.toMatrix b i a))) using 1
      ext z; simp
  simp_rw [fderiv_const_mul (hd _) _,_root_.smul_apply,smul_eq_mul]
  rw [← Finset.mul_sum,basis_divergence_change b c _ hF,basisMetricMatrix_volume_change b c]
  have hn := (abs_pos.mpr (basis_change_det_ne_zero b c)).ne'
  rw [_root_.mul_inv_rev]
  field_simp

end
end Yau.Geometry

end OAI
