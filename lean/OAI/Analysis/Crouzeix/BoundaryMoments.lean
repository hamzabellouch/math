import Mathlib
import OAI.Analysis.Crouzeix.ResolventMoments

namespace OAI

/-! Boundary Moments. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

open Boundary

lemma tensorOperator_smul_exchange
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator H) {m : ℕ} (c : ℂ) (B : Coeff m) :
    tensorOperator A (c • B) = tensorOperator (c • A) B := by
  exact ((tensorCoefficientCLM A m).map_smul c B).trans
    ((tensorOperatorCLM B).map_smul c A).symm

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H]

lemma matrixHolomorphicEval_scalar (A : Operator H) {V : Set ℂ} (hV : IsOpen V)
    (hKV : numericalClosure A ⊆ V) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f V)
    {m : ℕ} (B : Coeff m) :
    matrixHolomorphicEval A V (fun z => f z • B) = tensorOperator (holomorphicEval A V f) B := by
  unfold matrixHolomorphicEval
  convert sum_tensorOperator_entries (holomorphicEval A V f) B using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  simp only [Matrix.smul_apply, smul_eq_mul]
  simpa only [mul_comm] using holomorphicEval_smul A hV hKV hf (B i j)

end

namespace Boundary

lemma circleCoordinate_zpow (j : ℤ) (t : CircleSpace) :
    (circleCoordinate t)^j = fourier j t := by
  cases j with
  | ofNat k => exact circleCoordinate_pow k t
  | negSucc k =>
    rw [zpow_negSucc, ← inv_pow, circleCoordinate_inverse_pow]
    rfl

lemma boundaryStar_matrixLaurentMonomial {n : ℕ} (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    boundaryStar (matrixLaurentMonomial a c) =
      matrixLaurentMonomial (-a.1, a.2.2, a.2.1) (star c) := by
  ext t i j
  simp only [boundaryStar_apply, matrixLaurentMonomial, ContinuousMap.coe_mk,
    Matrix.conjTranspose_smul, star_mul, Matrix.conjTranspose_single, star_one,
    fourier_neg, Complex.star_def, mul_comm]

lemma tensorOperator_matrixLaurentMonomial
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : Operator H) {n : ℕ} (a : ℤ × (Fin n × Fin n)) (c : ℂ) (t : CircleSpace) :
    tensorOperator T (matrixLaurentMonomial a c t) =
      tensorOperatorCLM (Matrix.single a.2.1 a.2.2 1)
        (c • (circleCoordinate t)^a.1 • T) := by
  simpa only [matrixLaurentMonomial, ContinuousMap.coe_mk, tensorOperatorCLM_apply,
    mul_smul, circleCoordinate_zpow] using
    tensorOperator_smul_exchange T (c * fourier a.1 t) (Matrix.single a.2.1 a.2.2 1)

lemma integral_tensor_star {n : ℕ} (Q : C(CircleSpace, Coeff n)) (F : C(CircleSpace, Coeff n)) :
    (∫ t, tensorOperator (matrixOperatorMap n ((Q t)ᴴ)) (F t) ∂circleMeasure) =
      (tensorIntegral Q (boundaryStar F)).adjoint := by
  rw [tensorIntegral, integral_operator_adjoint]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    dsimp only
    rw [← ContinuousLinearMap.star_eq_adjoint, ← tensorOperator_star]
    simp only [boundaryStar_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose, matrixOperatorMap_apply]
    congr 1
    exact (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).map_star' (Q t)

lemma tensorIntegral_add_left {n : ℕ} (P Q F : C(CircleSpace, Coeff n)) :
    tensorIntegral (P+Q) F = tensorIntegral P F + tensorIntegral Q F := by
  simp only [tensorIntegral, ContinuousMap.add_apply, map_add,
    ← tensorOperatorCLM_apply]
  exact integral_add (integrable_tensor_field P F) (integrable_tensor_field Q F)

end Boundary

namespace Conformal.ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

variable {n : ℕ} (A : Operator (EuclideanSpace ℂ (Fin n)))
    (hKU : numericalClosure A ⊆ U) (hU : IsOpen U)

def matrixResolvent : C(CircleSpace, Coeff n) :=
  ⟨fun t => operatorToMatrix n (C.operatorResolvent A hKU hU t),
    (operatorToMatrix n).continuous.comp (C.operatorResolvent A hKU hU).continuous⟩

@[simp] lemma matrixResolvent_operator (t : CircleSpace) :
    matrixOperatorMap n (C.matrixResolvent A hKU hU t) = C.operatorResolvent A hKU hU t := by
  simp only [matrixResolvent, ContinuousMap.coe_mk, matrixOperatorMap_apply,
    operatorToMatrix_apply, StarAlgEquiv.apply_symm_apply]

def matrixResolventDensity : C(CircleSpace, Coeff n) :=
  C.matrixResolvent A hKU hU + boundaryStar (C.matrixResolvent A hKU hU)

lemma matrixResolventDensity_posSemidef (hc : Convex ℝ U) (t : CircleSpace) :
    (C.matrixResolventDensity A hKU hU t).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  let e := (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin n)).symm
  let Q := C.operatorResolvent A hKU hU t
  have he : e (Q + star Q) = (C.matrixResolventDensity A hKU hU t) := by
    rw [map_add]
    change e Q + e (star Q) = e Q + star (e Q)
    exact congrArg (e Q + ·) (e.map_star' Q)
  rw [← he]
  exact map_nonneg e (C.operatorResolvent_add_star_nonneg A hKU hU hc t)

variable [Nonempty (Fin n)]

include hKU in
lemma matrixHolomorphicEval_physicalRepresentative (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c) =
      tensorOperator (c • holomorphicEval A C.outerDomain (C.physicalCoefficient a.1))
        (Matrix.single a.2.1 a.2.2 1) := by
  rw [show C.physicalRepresentative a c =
      (fun z => (c * C.physicalCoefficient a.1 z) • Matrix.single a.2.1 a.2.2 1) from rfl,
    matrixHolomorphicEval_scalar A C.isOpen_outerDomain
      (hKU.trans (subset_closure.trans C.closure_subset_outerDomain))
      ((C.differentiableOn_physicalCoefficient a.1).const_mul c),
    holomorphicEval_smul A C.isOpen_outerDomain
      (hKU.trans (subset_closure.trans C.closure_subset_outerDomain))
      (C.differentiableOn_physicalCoefficient a.1)]

lemma tensorIntegral_matrixResolvent_moment (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    tensorIntegral (C.matrixResolvent A hKU hU) (matrixLaurentMonomial a c) =
      matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c) := by
  let : ContinuousSMul ℂ (EuclideanSpace ℂ (Fin n)) := IsBoundedSMul.continuousSMul
  let : CompleteSpace (Operator (EuclideanSpace ℂ (Fin n))) :=
    ContinuousLinearMap.instCompleteSpace
  rw [C.matrixHolomorphicEval_physicalRepresentative A hKU a c]
  simp only [tensorIntegral, C.matrixResolvent_operator,
    tensorOperator_matrixLaurentMonomial]
  have hi : Integrable (fun t => (circleCoordinate t)^a.1 • C.operatorResolvent A hKU hU t)
      circleMeasure :=
    ((circleCoordinate.continuous.zpow₀ a.1 (fun t => Or.inl (circleCoordinate_ne_zero t))).smul
      (C.operatorResolvent A hKU hU).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  refine ((tensorOperatorCLM (H := EuclideanSpace ℂ (Fin n))
    (Matrix.single a.2.1 a.2.2 1)).integral_comp_comm (hi.smul c)).trans ?_
  simp only [Pi.smul_apply, integral_smul, C.integral_operatorResolvent_moment A hKU hU,
    tensorOperatorCLM_apply]

lemma tensorIntegral_matrixResolventDensity (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    tensorIntegral (C.matrixResolventDensity A hKU hU) (matrixLaurentMonomial a c) =
      matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c) +
      (matrixHolomorphicEval A C.outerDomain
        (C.physicalRepresentative (-a.1,a.2.2,a.2.1) (star c))).adjoint := by
  rw [matrixResolventDensity, tensorIntegral_add_left,
    C.tensorIntegral_matrixResolvent_moment A hKU hU]
  congr 1
  change (∫ t, tensorOperator (matrixOperatorMap n
    ((C.matrixResolvent A hKU hU t)ᴴ)) (matrixLaurentMonomial a c t) ∂circleMeasure) = _
  rw [integral_tensor_star, boundaryStar_matrixLaurentMonomial,
    C.tensorIntegral_matrixResolvent_moment A hKU hU]

variable (R : InteriorCollar U)

omit [Nonempty (Fin n)] in
lemma tensorIntegral_matrixDensity_trace (D : Operator (EuclideanSpace ℂ (Fin n)))
    (hD : spectralRadius ℂ D < 1) {V : Set ℂ} (hUV : closure U ⊆ V)
    (F : ℂ → Coeff n) (hF : ContinuousOn F V) :
    tensorIntegral (C.matrixDensity R D hD) (C.matrixAnalyticTrace hUV F hF) =
      ∫ t, tensorOperator (C.operatorDensity R D hD t) (F (C.boundaryMap t)) ∂circleMeasure := by
  simp only [tensorIntegral, matrixDensity, matrixAnalyticTrace, ContinuousMap.coe_mk,
    matrixOperatorMap_apply, operatorToMatrix_apply, StarAlgEquiv.apply_symm_apply]

include hKU hU in
lemma physical_channel_intertwines (hc : Convex ℝ U)
    (D S : Operator (EuclideanSpace ℂ (Fin n)))
    (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    tensorOperator S (1 : Coeff n) *
        matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c) =
      tensorIntegral (C.matrixDensity R D hD) (c • C.physicalChannel a) *
        tensorOperator S (1 : Coeff n) := by
  rw [← C.physicalRepresentative_trace a c,
    C.tensorIntegral_matrixDensity_trace R D hD]
  exact C.physical_intertwines R hU hc A D S hKU hN hD hI
    C.isOpen_outerDomain C.closure_subset_outerDomain (C.physicalRepresentative_holomorphic a c)

lemma physical_laurent_tests (hc : Convex ℝ U)
    (D S : Operator (EuclideanSpace ℂ (Fin n)))
    (hN : ‖D‖ ≤ 1) (hD : spectralRadius ℂ D < 1)
    (hI : S * holomorphicEval A R.domain R.f = D * S)
    (a : ℤ × (Fin n × Fin n)) (c : ℂ) :
    ∃ (V W : C(CircleSpace, Coeff n))
      (B L : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)),
      boundaryCauchy (C.boundaryOperator hc n) (boundaryField (matrixLaurentMonomial a c)) = boundaryField V ∧
      boundaryCauchy (C.boundaryOperator hc n) (lpStar (boundaryField (matrixLaurentMonomial a c))) = boundaryField W ∧
      tensorIntegral (C.matrixResolventDensity A hKU hU) (matrixLaurentMonomial a c) = B + L.adjoint ∧
      tensorOperator S (1 : Coeff n) * B =
        tensorIntegral (C.matrixDensity R D hD) V * tensorOperator S (1 : Coeff n) ∧
      tensorOperator S (1 : Coeff n) * L =
        tensorIntegral (C.matrixDensity R D hD) W * tensorOperator S (1 : Coeff n) := by
  refine ⟨c • C.physicalChannel a, star c • C.physicalChannel (-a.1,a.2.2,a.2.1),
    matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative a c),
    matrixHolomorphicEval A C.outerDomain (C.physicalRepresentative (-a.1,a.2.2,a.2.1) (star c)),
    C.boundaryCauchy_matrixLaurentMonomial hU hc a c, ?_,
    C.tensorIntegral_matrixResolventDensity A hKU hU a c,
    C.physical_channel_intertwines A hKU hU R hc D S hN hD hI a c,
    C.physical_channel_intertwines A hKU hU R hc D S hN hD hI _ _⟩
  rw [← boundaryField_star, boundaryStar_matrixLaurentMonomial]
  exact C.boundaryCauchy_matrixLaurentMonomial hU hc _ _

end Conformal.ExteriorCollar

end CrouzeixHilbert

end

end OAI
