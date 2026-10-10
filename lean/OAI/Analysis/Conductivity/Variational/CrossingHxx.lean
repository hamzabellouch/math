import Mathlib
import OAI.Analysis.Conductivity.Variational.Symmetrize

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section
open Real

def crossingHxx (D J R l m x y : ℝ) : ℝ :=
  R / (D * l ^ 2) * cos (l*x) * cos (m*y) -
    2*R*J / (D^2*l^2) * sin (m*y)^2

def crossingHxy (D R l m x y : ℝ) : ℝ :=
  2*R / (D*l*m) * sin (l*x) * sin (m*y)

def crossingFluxX (D J R l m x y : ℝ) : ℝ :=
  crossingHxx D J R l m x y * (-D*l*sin (l*x)) +
    crossingHxy D R l m x y * (-J*m*sin (m*y))

def crossingFluxY (D R l m x y : ℝ) : ℝ :=
  crossingHxy D R l m x y * (-D*l*sin (l*x))

lemma crossingFluxX_simplify {D l m : ℝ} (hD : D ≠ 0) (hl : l ≠ 0) (hm : m ≠ 0)
    (J R x y : ℝ) :
    crossingFluxX D J R l m x y = -(R/l) * (cos (l*x)*sin (l*x)) * cos (m*y) := by
  unfold crossingFluxX crossingHxx crossingHxy
  field_simp
  ring

lemma crossingFluxY_simplify {D l m : ℝ} (hD : D ≠ 0) (hl : l ≠ 0) (hm : m ≠ 0)
    (R x y : ℝ) :
    crossingFluxY D R l m x y = -(2*R/m) * sin (l*x)^2 * sin (m*y) := by
  unfold crossingFluxY crossingHxy
  field_simp

theorem crossing_divergence {D l m : ℝ} (hD : D ≠ 0) (hl : l ≠ 0) (hm : m ≠ 0)
    (J R x y : ℝ) :
    deriv (fun a => crossingFluxX D J R l m a y) x +
      deriv (fun b => crossingFluxY D R l m x b) y = -R*cos (m*y) := by
  have hx := (hasDerivAt_id x).const_mul l
  have hy := (hasDerivAt_id y).const_mul m
  have hfx := (((hx.cos.mul hx.sin).const_mul (-(R/l))).mul_const (cos (m*y)))
  have hfy := hy.sin.const_mul (-(2*R/m)*sin (l*x)^2)
  have hex : (fun a => crossingFluxX D J R l m a y) =
      (fun a => -(R/l)*(cos (l*a)*sin (l*a))*cos (m*y)) := by
    funext a
    exact crossingFluxX_simplify hD hl hm J R a y
  have hey : (fun b => crossingFluxY D R l m x b) =
      (fun b => (-(2*R/m)*sin (l*x)^2)*sin (m*b)) := by
    funext b
    exact crossingFluxY_simplify hD hl hm R x b
  simp only [id_eq, Pi.mul_apply, mul_one] at hfx hfy
  rw [hex, hey, hfx.deriv, hfy.deriv]
  field_simp
  linear_combination -(R*cos (m*y)) * Real.sin_sq_add_cos_sq (l*x)

lemma crossing_coefficients_small {D J R l m ε : ℝ}
    (hD : D ≠ 0) (hl : l ≠ 0) (hm : m ≠ 0)
    (hα : |R / (D*l^2)| ≤ ε) (hβ : |J/D| ≤ 1) (hr : |l/m| ≤ 2)
    (x y : ℝ) :
    |crossingHxx D J R l m x y| ≤ 3*ε ∧
      |crossingHxy D R l m x y| ≤ 4*ε := by
  have he : 0 ≤ ε := (abs_nonneg _).trans hα
  have hs (t : ℝ) : |sin t| ≤ 1 := abs_sin_le_one t
  have hc (t : ℝ) : |cos t| ≤ 1 := abs_cos_le_one t
  have hxx : crossingHxx D J R l m x y =
      (R/(D*l^2)) * (cos (l*x)*cos (m*y) - 2*(J/D)*sin (m*y)^2) := by
    unfold crossingHxx
    field_simp
  have hxy : crossingHxy D R l m x y =
      2*(R/(D*l^2))*(l/m)*(sin (l*x)*sin (m*y)) := by
    unfold crossingHxy
    field_simp
  have hp (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a*b| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg a, abs_nonneg b]
  have hsin2 : |sin (m*y)^2| ≤ 1 := by
    simpa only [pow_two] using hp _ _ (hs (m*y)) (hs (m*y))
  constructor
  · rw [hxx, abs_mul]
    have h1 := hp _ _ (hc (l*x)) (hc (m*y))
    have h2 : |2*(J/D)*sin (m*y)^2| ≤ 2 := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
      nlinarith [abs_nonneg (J/D), abs_nonneg (sin (m*y)^2)]
    have hh := abs_sub (cos (l*x)*cos (m*y)) (2*(J/D)*sin (m*y)^2)
    nlinarith [abs_nonneg (R/(D*l^2))]
  · rw [hxy, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := hp _ _ (hs (l*x)) (hs (m*y))
    have hprod : |R/(D*l^2)| * |l/m| ≤ 2*ε := by
      nlinarith [abs_nonneg (R/(D*l^2)), abs_nonneg (l/m)]
    nlinarith [abs_nonneg (R/(D*l^2)), abs_nonneg (l/m),
      abs_nonneg (sin (l*x)*sin (m*y)), mul_nonneg (abs_nonneg (R/(D*l^2))) (abs_nonneg (l/m))]

lemma crossing_quadratic_ellipticity {a b h k ε : ℝ}
    (ha : 1/4 ≤ a) (hb : 1/4 ≤ b) (ha' : a ≤ 9) (hb' : b ≤ 9)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1/56) (hh : |h| ≤ 3*ε) (hk : |k| ≤ 4*ε)
    (x y : ℝ) :
    (1/8)*(x^2+y^2) ≤ (a+h)*x^2+2*k*x*y+b*y^2 ∧
      (a+h)*x^2+2*k*x*y+b*y^2 ≤ 10*(x^2+y^2) := by
  have hh' := (abs_le.mp hh)
  have hk' := (abs_le.mp hk)
  have hx : 0 ≤ x^2 := sq_nonneg x
  have hy : 0 ≤ y^2 := sq_nonneg y
  have hcross : |2*k*x*y| ≤ 4*ε*(x^2+y^2) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hs : 2*|x| * |y| ≤ x^2+y^2 := by
      nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]
    have hkxy := mul_le_mul_of_nonneg_right hk (mul_nonneg (abs_nonneg x) (abs_nonneg y))
    have hexy := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 4*ε)
    nlinarith
  have hcross' := abs_le.mp hcross
  have hal := mul_le_mul_of_nonneg_right ha hx
  have hbl := mul_le_mul_of_nonneg_right hb hy
  have hau := mul_le_mul_of_nonneg_right ha' hx
  have hbu := mul_le_mul_of_nonneg_right hb' hy
  have hhl := mul_le_mul_of_nonneg_right hh'.1 hx
  have hhu := mul_le_mul_of_nonneg_right hh'.2 hx
  have heu := mul_le_mul_of_nonneg_right hε' (add_nonneg hx hy)
  have hey := mul_nonneg hε hy
  constructor <;> nlinarith

end

open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

def pushGradient {m : Type*} [Fintype m] (J : Mat3) (E : Matrix (Fin 3) m ℝ) :
    Matrix (Fin 3) m ℝ := J⁻¹ᵀ * E

def pushFlux {m : Type*} [Fintype m] (J : Mat3) (F : Matrix (Fin 3) m ℝ) :
    Matrix (Fin 3) m ℝ := J.det⁻¹ • (J * F)

lemma pushGradient_leftInverse {m : Type*} [Fintype m] (J : Mat3)
    (hJ : J.det ≠ 0) (E : Matrix (Fin 3) m ℝ) : Jᵀ * pushGradient J E = E := by
  have hj := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hJ)
  unfold pushGradient
  rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hj, Matrix.transpose_one, Matrix.one_mul]

lemma pushGradient_rank {m : Type*} [Fintype m] (J : Mat3)
    (hJ : J.det ≠ 0) (E : Matrix (Fin 3) m ℝ) (hE : LinearIndependent ℝ E.col) :
    LinearIndependent ℝ (pushGradient J E).col := by
  apply Matrix.mulVec_injective_iff.mp
  intro v w hvw
  apply Matrix.mulVec_injective_iff.mpr hE
  have h := congrArg Jᵀ.mulVec hvw
  simpa only [Matrix.mulVec_mulVec, pushGradient_leftInverse J hJ E] using h

lemma push_pairing {m : Type*} [Fintype m] (J : Mat3)
    (hJ : J.det ≠ 0) (E F : Matrix (Fin 3) m ℝ) :
    (pushGradient J E)ᵀ * pushFlux J F = J.det⁻¹ • (Eᵀ * F) := by
  have hj := Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.mpr hJ)
  unfold pushGradient pushFlux
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul]
  congr 1
  calc
    Eᵀ * J⁻¹ * (J * F) = Eᵀ * (J⁻¹ * J) * F := by simp only [Matrix.mul_assoc]
    _ = Eᵀ * F := by rw [hj, Matrix.mul_one]

lemma pushFlux_constitutive {m : Type*} [Fintype m] (J B : Mat3)
    (hJ : J.det ≠ 0) (E : Matrix (Fin 3) m ℝ) :
    pushFlux J (B * E) = (J.det⁻¹ • (J * B * Jᵀ)) * pushGradient J E := by
  rw [Matrix.smul_mul, Matrix.mul_assoc, pushGradient_leftInverse J hJ E]
  simp only [pushFlux, Matrix.mul_assoc]

lemma symmetric_gram_pairing {m : Type*} [Fintype m]
    (A : Symmetric3) (E : Matrix (Fin 3) m ℝ) : (Eᵀ * (A.val * E)).IsSymm := by
  unfold Matrix.IsSymm
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    (Matrix.isHermitian_iff_isSymm.mp A.property).eq]
  exact Matrix.mul_assoc _ _ _

def repairPushed {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (J : Mat3) (E F : Matrix (Fin 3) m ℝ) : Symmetric3 :=
  repairError A (pushGradient J E) (pushFlux J F - A.val * pushGradient J E)

lemma repairPushed_mul {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (J : Mat3) (E F : Matrix (Fin 3) m ℝ)
    (hJ : J.det ≠ 0) (hE : LinearIndependent ℝ E.col) (hEF : (Eᵀ * F).IsSymm) :
    (repairPushed A J E F).val * pushGradient J E = pushFlux J F := by
  unfold repairPushed
  rw [repairError_mul A _ _ (pushGradient_rank J hJ E hE)]
  · exact add_sub_cancel _ _
  · rw [Matrix.mul_sub, push_pairing J hJ E F]
    exact (hEF.smul _).sub (symmetric_gram_pairing A _)

lemma repairPushed_exact {m : Type*} [Fintype m] [DecidableEq m]
    (A : Symmetric3) (J B : Mat3) (E : Matrix (Fin 3) m ℝ)
    (hJ : J.det ≠ 0) (hA : A.val = J.det⁻¹ • (J * B * Jᵀ)) :
    repairPushed A J E (B * E) = A := by
  unfold repairPushed
  rw [hA, ← pushFlux_constitutive J B hJ E, sub_self, repairError_zero]

lemma continuousAt_matrixInverse (J : Mat3) (hJ : J.det ≠ 0) :
    ContinuousAt (fun M : Mat3 => M⁻¹) J := by
  apply continuousAt_matrix_inv
  convert continuousAt_inv₀ hJ using 1
  ext x
  exact Ring.inverse_eq_inv x

lemma continuousAt_pushGradient {m X : Type*} [Fintype m] [TopologicalSpace X]
    (J : X → Mat3) (E : X → Matrix (Fin 3) m ℝ) {x : X}
    (hJ : ContinuousAt J x) (hE : ContinuousAt E x) (hdet : (J x).det ≠ 0) :
    ContinuousAt (fun y => pushGradient (J y) (E y)) x := by
  have hi : ContinuousAt (fun y => (J y)⁻¹) x :=
    ContinuousAt.comp (f := J) (continuousAt_matrixInverse (J x) hdet) hJ
  exact matrix_mul_contAt (matrix_transpose_contAt hi) hE

lemma continuousAt_pushFlux {m X : Type*} [Fintype m] [TopologicalSpace X]
    (J : X → Mat3) (F : X → Matrix (Fin 3) m ℝ) {x : X}
    (hJ : ContinuousAt J x) (hF : ContinuousAt F x) (hdet : (J x).det ≠ 0) :
    ContinuousAt (fun y => pushFlux (J y) (F y)) x := by
  have hc : Continuous (fun M : Mat3 => M.det) := continuous_id.matrix_det
  have hd : ContinuousAt (fun y => (J y).det) x := hc.continuousAt.comp hJ
  exact (hd.inv₀ hdet).smul (matrix_mul_contAt hJ hF)

lemma continuousAt_repairPushed {m X : Type*} [Fintype m] [DecidableEq m]
    [TopologicalSpace X] (A : X → Symmetric3) (J : X → Mat3)
    (E F : X → Matrix (Fin 3) m ℝ) {x : X}
    (hA : ContinuousAt A x) (hJ : ContinuousAt J x)
    (hE : ContinuousAt E x) (hF : ContinuousAt F x)
    (hdet : (J x).det ≠ 0) (hi : LinearIndependent ℝ (E x).col) :
    ContinuousAt (fun y => repairPushed (A y) (J y) (E y) (F y)) x := by
  have hG := continuousAt_pushGradient J E hJ hE hdet
  have hP := continuousAt_pushFlux J F hJ hF hdet
  exact continuousAt_repairError _ _ _ hA hG
    (hP.sub (matrix_mul_contAt (continuousAt_subtype_val.comp hA) hG))
    (pushGradient_rank (J x) hdet (E x) hi)

end ScalarConductivity

end

end OAI
