import OAI.Geometry.Arnold.Symplectic

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

local instance : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The actual real-matrix action on C5, jointly continuous bilinear. -/
def matrixAction : RM →L[ℝ] CV →L[ℝ] CV :=
  ({ toFun := fun A ↦ ((complexMat A).mulVecLin.restrictScalars ℝ).toContinuousLinearMap
     map_add' := by intro A B; apply ContinuousLinearMap.ext; intro z; exact act_add_left A B z
     map_smul' := by intro c A; apply ContinuousLinearMap.ext; intro z; exact act_real_smul_left c A z } :
      RM →ₗ[ℝ] CV →L[ℝ] CV).toContinuousLinearMap

@[simp] lemma matrixAction_apply (A : RM) (z : CV) : matrixAction A z = act A z := rfl

/-- Intrinsic derivative along the genuine coordinate-plane rotation. -/
def rotationDerivative (G : CV → ℝ) (a b : Fin 5) (z : CV) : ℝ :=
  fderiv ℝ G z (matrixAction (rotGen a b) z)

lemma rotationDerivative_contDiff (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) (a b : Fin 5) :
    ContDiff ℝ ∞ (rotationDerivative G a b) :=
  (hG.fderiv_right (by simp)).clm_apply (matrixAction (rotGen a b)).contDiff

/-- Smooth negative gradient written in the spanning infinitesimal rotations. -/
def negativeRotationMatrix (G : CV → ℝ) (z : CV) : RM :=
  -(∑ a : Fin 5, ∑ b : Fin 5, rotationDerivative G a b z • rotGen a b)

def gradientSquare (G : CV → ℝ) (z : CV) : ℝ :=
  ∑ a : Fin 5, ∑ b : Fin 5, rotationDerivative G a b z ^ 2

lemma negativeRotationMatrix_contDiff (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (negativeRotationMatrix G) := by
  exact (ContDiff.sum (fun a _ ↦ ContDiff.sum (fun b _ ↦
    (rotationDerivative_contDiff G hG a b).smul contDiff_const))).neg

lemma gradientSquare_contDiff (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (gradientSquare G) := by
  exact ContDiff.sum (fun a _ ↦ ContDiff.sum (fun b _ ↦
    (rotationDerivative_contDiff G hG a b).pow 2))

lemma gradientSquare_nonneg (G : CV → ℝ) (z : CV) : 0 ≤ gradientSquare G z :=
  Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _))

lemma gradientSquare_eq_zero_iff (G : CV → ℝ) (z : CV) :
    gradientSquare G z = 0 ↔ ∀ a b, rotationDerivative G a b z = 0 := by
  simp only [gradientSquare, Finset.sum_eq_zero_iff_of_nonneg
    (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ sq_nonneg (rotationDerivative G a b z))),
    Finset.sum_eq_zero_iff_of_nonneg (fun b _ ↦ sq_nonneg (rotationDerivative G _ b z)),
    Finset.mem_univ, forall_const, sq_eq_zero_iff]

lemma negativeRotationMatrix_skew (G : CV → ℝ) (z : CV) :
    star (negativeRotationMatrix G z) = -negativeRotationMatrix G z := by
  simp only [negativeRotationMatrix, star_neg, star_sum, star_smul, star_trivial,
    rotGen_skew, smul_neg, Finset.sum_neg_distrib, neg_neg]

lemma negativeRotationMatrix_derivative (G : CV → ℝ) (z : CV) :
    fderiv ℝ G z (matrixAction (negativeRotationMatrix G z) z) = -gradientSquare G z := by
  simp only [negativeRotationMatrix, map_neg, map_sum, map_smul,
    neg_apply, sum_apply,
    smul_apply, gradientSquare, rotationDerivative, pow_two,
    smul_eq_mul]

/-- Orthogonal exponential is a globally defined smooth deformation of K. -/
def gradientCurve (G : CV → ℝ) (p : ℝ × CV) : CV :=
  matrixAction (NormedSpace.exp (p.1 • negativeRotationMatrix G p.2)) p.2

lemma matrix_exp_contDiff : ContDiff ℝ ∞ (NormedSpace.exp : RM → RM) :=
  AnalyticOnNhd.contDiff (fun x _ ↦ NormedSpace.exp_analytic x)

lemma gradientCurve_contDiff (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (gradientCurve G) :=
  (matrixAction.contDiff.comp (matrix_exp_contDiff.comp
    (contDiff_fst.smul ((negativeRotationMatrix_contDiff G hG).comp contDiff_snd)))).clm_apply
      contDiff_snd

lemma gradientCurve_preserves (G : CV → ℝ) (t : ℝ) (z : UnitQuadric) :
    IsUnitQuadric (gradientCurve G (t, z)) :=
  act_unit (expCurve (negativeRotationMatrix G z) (negativeRotationMatrix_skew G z) t) z

@[simp] lemma gradientCurve_zero (G : CV → ℝ) (z : CV) : gradientCurve G (0, z) = z := by
  simp only [gradientCurve, zero_smul, NormedSpace.exp_zero, matrixAction_apply, act,
    complexMat_one, Matrix.one_mulVec]

lemma gradientCurve_derivative_zero (G : CV → ℝ) (z : CV) :
    HasDerivAt (fun t ↦ gradientCurve G (t, z))
      (matrixAction (negativeRotationMatrix G z) z) 0 := by
  have h := (matrixAction.flip z).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const (negativeRotationMatrix G z) 0)
  simpa only [zero_smul, NormedSpace.exp_zero, one_mul, Function.comp_def,
    ContinuousLinearMap.flip_apply, gradientCurve] using h

lemma gradientCurve_lyapunov_derivative (G : CV → ℝ) (hG : ContDiff ℝ ∞ G) (z : CV) :
    fderiv ℝ (fun p ↦ G (gradientCurve G p)) (0, z) (1, 0) = -gradientSquare G z := by
  have hc := (hG.differentiable (by simp) (gradientCurve G (0, z))).hasFDerivAt.comp_hasDerivAt 0
    (gradientCurve_derivative_zero G z)
  have hd := ((hG.comp (gradientCurve_contDiff G hG)).differentiable (by simp) (0, z)).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const 0 z))
  have heq := hd.unique hc
  convert! heq using 1; simp only [gradientCurve_zero, negativeRotationMatrix_derivative]

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

local instance : TopologicalSpace RM :=
  (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

lemma matrix_orbit_derivative_zero (X : RM) (z : CV) :
    HasDerivAt (fun t : ℝ ↦ matrixAction (NormedSpace.exp (t • X)) z)
      (matrixAction X z) 0 := by
  have h := (matrixAction.flip z).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_exp_smul_const X 0)
  simpa only [zero_smul, NormedSpace.exp_zero, one_mul, Function.comp_def,
    ContinuousLinearMap.flip_apply] using h

lemma rotationDerivative_phase (G : CV → ℝ) (hG : ContDiff ℝ ∞ G)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → G (a • (z : CV)) = G z)
    (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) (i j : Fin 5) :
    rotationDerivative G i j (a • (z : CV)) = rotationDerivative G i j z := by
  let c : ℝ → CV := fun t ↦ matrixAction (NormedSpace.exp (t • rotGen i j)) z
  have hc := matrix_orbit_derivative_zero (rotGen i j) (z : CV)
  have hc0 : c 0 = z := by
    simp [c, matrixAction_apply, act, complexMat_one]
  have hcu (t : ℝ) : IsUnitQuadric (c t) := act_unit (expCurve (rotGen i j) (rotGen_skew i j) t) z
  have hd := (hG.differentiable (by simp) (c 0)).hasFDerivAt.comp_hasDerivAt 0 hc
  have he := (hG.differentiable (by simp) (a • c 0)).hasFDerivAt.comp_hasDerivAt 0 (hc.const_smul a)
  have heq : (fun t : ℝ ↦ G (a • c t)) = (fun t ↦ G (c t)) :=
    funext (fun t ↦ hphase ⟨c t, hcu t⟩ a ha)
  have he' : HasDerivAt (fun t : ℝ ↦ G (a • c t))
      (fderiv ℝ G (a • c 0) (a • matrixAction (rotGen i j) z)) 0 := he
  rw [heq] at he'
  have h := he'.unique hd
  simpa only [hc0, rotationDerivative, matrixAction_apply, act_smul] using h

lemma negativeRotationMatrix_phase (G : CV → ℝ) (hG : ContDiff ℝ ∞ G)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → G (a • (z : CV)) = G z)
    (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    negativeRotationMatrix G (a • (z : CV)) = negativeRotationMatrix G z := by
  simp only [negativeRotationMatrix, rotationDerivative_phase G hG hphase z a ha]

lemma gradientSquare_phase (G : CV → ℝ) (hG : ContDiff ℝ ∞ G)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → G (a • (z : CV)) = G z)
    (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    gradientSquare G (a • (z : CV)) = gradientSquare G z := by
  simp only [gradientSquare, rotationDerivative_phase G hG hphase z a ha]

lemma gradientCurve_phase (G : CV → ℝ) (hG : ContDiff ℝ ∞ G)
    (hphase : ∀ z : UnitQuadric, ∀ a : ℂ, Complex.normSq a = 1 → G (a • (z : CV)) = G z)
    (t : ℝ) (z : UnitQuadric) (a : ℂ) (ha : Complex.normSq a = 1) :
    gradientCurve G (t, a • (z : CV)) = a • gradientCurve G (t, z) := by
  simp only [gradientCurve, negativeRotationMatrix_phase G hG hphase z a ha,
    matrixAction_apply, act_smul]

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open ArnoldCounterexample.Forms

/-- A literal real skew matrix lifting any horizontal vector. -/
def tangentMatrix (z v : CV) : RM := fun i j ↦ 2 * (v i * star (z j) - z i * star (v j)).re

lemma tangentMatrix_skew (z v : CV) : star (tangentMatrix z v) = -tangentMatrix z v := by
  ext i j
  simp [Matrix.star_apply, tangentMatrix, Complex.mul_re]
  ring

lemma complex_tangentMatrix (z v : CV) (i j : Fin 5) :
    complexMat (tangentMatrix z v) i j =
      v i * star (z j) + star (v i) * z j - z i * star (v j) - star (z i) * v j := by
  apply Complex.ext <;>
    simp [complexMat, tangentMatrix, Complex.mul_re, Complex.mul_im] <;> ring

lemma tangentMatrix_act (z : UnitQuadric) (v : CV) (hv : Horizontal z v) :
    act (tangentMatrix z v) z = v := by
  have hn : ∑ j, star ((z : CV) j) * (z : CV) j = (1 : ℂ) := by
    calc
      _ = ((∑ j, Complex.normSq ((z : CV) j) : ℝ) : ℂ) := by
        simp only [Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
        rfl
      _ = 1 := by exact_mod_cast z.property.1
  have hp : ∑ j, (z : CV) j * (z : CV) j = (0 : ℂ) := by
    simpa only [quadricPolynomial, ← pow_two] using z.property.2
  have hconj : ∑ j, star (v j) * (z : CV) j = (0 : ℂ) := by
    have h := congrArg star hv.1
    simpa only [star_sum, star_mul, star_star, star_zero, mul_comm] using h
  ext i
  simp only [act, Matrix.mulVec, dotProduct, complex_tangentMatrix]
  calc
    _ = v i * (∑ j, star ((z : CV) j) * (z : CV) j) +
      star (v i) * (∑ j, (z : CV) j * (z : CV) j) -
      (z : CV) i * (∑ j, star (v j) * (z : CV) j) -
      star ((z : CV) i) * (∑ j, (z : CV) j * v j) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = v i := by rw [hn, hp, hconj, hv.2]; ring

lemma skew_rotation_sum (M : RM) (hM : star M = -M) :
    (∑ a : Fin 5, ∑ b : Fin 5, M b a • rotGen a b) = (2 : ℝ) • M := by
  have hm (i j : Fin 5) : M j i = -M i j := by
    have h := congrFun (congrFun hM i) j
    simpa only [Matrix.star_apply, star_trivial, Matrix.neg_apply] using h
  ext i j
  change (∑ a : Fin 5, ∑ b : Fin 5, M b a * (rotGen a b) i j) = 2 * M i j
  simp [rotGen, Matrix.single_apply, mul_sub, Finset.sum_sub_distrib,
    mul_ite, ite_and]
  rw [hm]
  ring

/-- Vanishing of the finitely many rotation derivatives really implies
vanishing in every horizontal tangent direction. -/
lemma horizontal_derivative_of_rotation_zero (G : CV → ℝ) (z : UnitQuadric)
    (hzero : ∀ a b, rotationDerivative G a b z = 0)
    (v : CV) (hv : Horizontal z v) : fderiv ℝ G z v = 0 := by
  have heq := congrArg (fun M : RM ↦ fderiv ℝ G z (matrixAction M z))
    (skew_rotation_sum (tangentMatrix z v) (tangentMatrix_skew z v))
  have hzero' (a b : Fin 5) : fderiv ℝ G z (act (rotGen a b) z) = 0 := hzero a b
  simp only [map_sum, sum_apply, map_smul, smul_apply, matrixAction_apply,
    hzero', tangentMatrix_act z v hv,
    smul_eq_mul, mul_zero, Finset.sum_const_zero] at heq
  linarith

end ArnoldCounterexample.CriticalBound

end

end OAI
