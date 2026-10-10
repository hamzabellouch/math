import Mathlib
import OAI.Analysis.Crouzeix.CauchyProjection

namespace OAI

/-! Similarity Representation. -/

noncomputable section

open MeasureTheory

open scoped InnerProductSpace TensorProduct Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace CrouzeixHilbert

namespace Endpoint

section Intertwining

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem intertwining_inner (S B D : E →L[ℂ] E) (hS : IsSelfAdjoint S)
    (hSB : S * B = D * S) (x y : E) (a b : ℝ) (hb : b ≠ 0)
    (hx : S x = (a : ℂ) • x) (hy : S y = (b : ℂ) • y) :
    ⟪y, B x⟫_ℂ = ((a / b : ℝ) : ℂ) * ⟪y, D x⟫_ℂ := by
  have he : (b : ℂ) * ⟪y, B x⟫_ℂ = (a : ℂ) * ⟪y, D x⟫_ℂ := by
    calc
      _ = ⟪S y, B x⟫_ℂ := by rw [hy, inner_smul_left]; simp
      _ = ⟪y, S (B x)⟫_ℂ := by
        simpa only [hS.adjoint_eq] using ContinuousLinearMap.adjoint_inner_left S (B x) y
      _ = ⟪y, D (S x)⟫_ℂ := by
        rw [← mul_apply_eq_comp, hSB, mul_apply_eq_comp]
      _ = _ := by rw [hx, map_smul, inner_smul_right]
  rw [Complex.ofReal_div, div_mul_eq_mul_div,
    eq_div_iff (by exact_mod_cast hb : (b : ℂ) ≠ 0), mul_comm]
  exact he

theorem intertwining_adjoint_inner (S B D : E →L[ℂ] E) (hS : IsSelfAdjoint S)
    (hSB : S * B = D * S) (x y : E) (a b : ℝ) (ha : a ≠ 0)
    (hx : S x = (a : ℂ) • x) (hy : S y = (b : ℂ) • y) :
    ⟪y, B.adjoint x⟫_ℂ = ((b / a : ℝ) : ℂ) * ⟪y, D.adjoint x⟫_ℂ := by
  have he := congrArg (starRingEnd ℂ) (intertwining_inner S B D hS hSB y x b a ha hy hx)
  simpa only [map_mul, inner_conj_symm, Complex.conj_ofReal,
    ContinuousLinearMap.adjoint_inner_right] using he

end Intertwining

end Endpoint

section OperatorIntegral

variable {α V : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem integral_operator_adjoint (T : α → V →L[ℂ] V) :
    (∫ t, T t ∂μ).adjoint = ∫ t, (T t).adjoint ∂μ := by
  simpa only [starL'_apply, ContinuousLinearMap.star_eq_adjoint] using
    ((starL' ℝ : (V →L[ℂ] V) ≃L[ℝ] (V →L[ℂ] V)).integral_comp_comm T).symm

end OperatorIntegral

namespace Boundary

def boundaryStar {n : ℕ} (U : C(CircleSpace, Coeff n)) : C(CircleSpace, Coeff n) :=
  ⟨fun t => (U t)ᴴ, U.continuous.star⟩

@[simp] theorem boundaryStar_apply {n : ℕ} (U : C(CircleSpace, Coeff n)) (t : CircleSpace) :
    boundaryStar U t = (U t)ᴴ := rfl

@[simp] theorem boundaryField_star {n : ℕ} (U : C(CircleSpace, Coeff n)) :
    boundaryField (boundaryStar U) = lpStar (boundaryField U) := by
  apply Lp.ext
  filter_upwards [boundaryField_apply_ae (boundaryStar U),
    boundaryField_apply_ae U, lpStar_apply_ae (boundaryField U)] with t hs hu hl
  rw [hs, hl, hu, ofHS_toHS]
  rfl

def tensorIntegral {n : ℕ} (E U : C(CircleSpace, Coeff n)) :
    Operator (Amplification (EuclideanSpace ℂ (Fin n)) n) :=
  ∫ t, tensorOperator (matrixOperatorMap n (E t)) (U t) ∂circleMeasure

@[simp] theorem tensorIntegral_star {n : ℕ} (E U : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) :
    tensorIntegral E (boundaryStar U) = (tensorIntegral E U).adjoint := by
  rw [tensorIntegral, tensorIntegral, integral_operator_adjoint]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change tensorOperator (matrixOperatorMap n (E t)) (U t)ᴴ =
      (tensorOperator (matrixOperatorMap n (E t)) (U t)).adjoint
    calc
      _ = tensorOperator (star (matrixOperatorMap n (E t))) (star (U t)) := by
        congr 1
        simp only [matrixOperatorMap_apply, ← map_star,
          Matrix.star_eq_conjTranspose, (hE t).eq]
      _ = star (tensorOperator (matrixOperatorMap n (E t)) (U t)) :=
        tensorOperator_star _ _
      _ = _ := ContinuousLinearMap.star_eq_adjoint _

theorem real_inner_densityLp_field {n : ℕ} (E U : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) (X Y : Coeff n) :
    ⟪densityLp E X Y, boundaryField U⟫_ℝ =
      (⟪vectorization Y, tensorIntegral E U (vectorization X)⟫_ℂ).re := by
  rw [boundary_real_inner, densityLp_inner_boundaryField E U hE]
  rfl

theorem real_inner_densityLp_star_field {n : ℕ} (E U : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) (X Y : Coeff n) :
    ⟪densityLp E X Y, lpStar (boundaryField U)⟫_ℝ =
      (⟪vectorization Y, (tensorIntegral E U).adjoint (vectorization X)⟫_ℂ).re := by
  rw [← boundaryField_star, real_inner_densityLp_field E (boundaryStar U) hE,
    tensorIntegral_star E U hE]

theorem lpStar_inner_right {n : ℕ} (u v : BoundaryL2 n) :
    ⟪u, lpStar v⟫_ℝ = ⟪lpStar u, v⟫_ℝ := by
  have h := (lpStar (k := n) (μ := circleMeasure)).inner_map_map (lpStar u) v
  simpa only [lpStar_lpStar] using h

def reflectedBoundaryCauchy {n : ℕ} (M : BoundaryL2 n →L[ℝ] BoundaryL2 n) :
    BoundaryL2 n →L[ℝ] BoundaryL2 n :=
  lpStar.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundaryCauchy M).comp lpStar.toContinuousLinearEquiv.toContinuousLinearMap)

theorem reflectedBoundaryCauchy_pairing {n : ℕ}
    (M : BoundaryL2 n →L[ℝ] BoundaryL2 n) (r u : BoundaryL2 n) :
    ⟪r, reflectedBoundaryCauchy M u⟫_ℝ =
      ⟪lpStar (boundaryCauchyAdjoint M (lpStar r)), u⟫_ℝ := by
  change ⟪r, lpStar (boundaryCauchy M (lpStar u))⟫_ℝ = _
  rw [lpStar_inner_right, ← ContinuousLinearMap.adjoint_inner_left,
    adjoint_boundaryCauchy, lpStar_inner_right]

theorem projected_density_of_laurent_testing {n : ℕ}
    (M : BoundaryL2 n →L[ℝ] BoundaryL2 n)
    (E Λ : C(CircleSpace, Coeff n))
    (hE : ∀ t, (E t).IsHermitian) (hΛ : ∀ t, (Λ t).IsHermitian)
    (S : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)) (hS : IsSelfAdjoint S)
    (X Y : Coeff n) (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : S (vectorization X) = (a : ℂ) • vectorization X)
    (hy : S (vectorization Y) = (b : ℂ) • vectorization Y)
    (htest : ∀ (j : ℤ × (Fin n × Fin n)) (c : ℂ),
      ∃ (V W : C(CircleSpace, Coeff n))
        (B L : Operator (Amplification (EuclideanSpace ℂ (Fin n)) n)),
        boundaryCauchy M (boundaryField (matrixLaurentMonomial j c)) = boundaryField V ∧
        boundaryCauchy M (lpStar (boundaryField (matrixLaurentMonomial j c))) = boundaryField W ∧
        tensorIntegral E (matrixLaurentMonomial j c) = B + L.adjoint ∧
        S * B = tensorIntegral Λ V * S ∧ S * L = tensorIntegral Λ W * S) :
    densityLp E X Y = (a / b) • boundaryCauchyAdjoint M (densityLp Λ X Y) +
      (b / a) • lpStar (boundaryCauchyAdjoint M (lpStar (densityLp Λ X Y))) := by
  apply eq_of_inner_matrixLaurentMonomial
  intro j c
  obtain ⟨V, W, B, L, hV, hW, hR, hB, hL⟩ := htest j c
  have hB' := Endpoint.intertwining_inner S B (tensorIntegral Λ V) hS hB
    (vectorization X) (vectorization Y) a b hb hx hy
  have hL' := Endpoint.intertwining_adjoint_inner S L (tensorIntegral Λ W) hS hL
    (vectorization X) (vectorization Y) a b ha hx hy
  rw [real_inner_densityLp_field E _ hE, hR, add_apply, inner_add_right,
    hB', hL', Complex.add_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [← real_inner_densityLp_field Λ V hΛ,
    ← real_inner_densityLp_star_field Λ W hΛ, ← hV, ← hW]
  rw [← ContinuousLinearMap.adjoint_inner_left, adjoint_boundaryCauchy]
  have hr := reflectedBoundaryCauchy_pairing M (densityLp Λ X Y)
    (boundaryField (matrixLaurentMonomial j c))
  change ⟪densityLp Λ X Y, lpStar (boundaryCauchy M
    (lpStar (boundaryField (matrixLaurentMonomial j c))))⟫_ℝ = _ at hr
  rw [hr, inner_add_left, real_inner_smul_left, real_inner_smul_left]

end Boundary

end CrouzeixHilbert

end

end OAI
