import OAI.Analysis.IrrationalRotation.Product.ProductCocycleWindow
import OAI.Analysis.IrrationalRotation.Rotation.CircleCocycleWindow
import OAI.Analysis.IrrationalRotation.Rotation.ProjectionDiagonalPropagation
import Mathlib.Analysis.CStarAlgebra.Basic

namespace OAI

noncomputable section
open scoped lp ComplexConjugate InnerProductSpace

namespace Invariant233.ProjectionCocycleWindow

def basisZero : ℓ²(ℤ, ℂ) := lp.single 2 (0 : ℤ) (1 : ℂ)

@[simp] theorem norm_basisZero : ‖basisZero‖ = 1 := by
  simp [basisZero, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

@[simp] theorem basisZero_zero : basisZero 0 = 1 := by
  simp [basisZero]

theorem projection_vector_norm_le (P : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) : ‖P basisZero‖ ≤ 1 := by
  calc
    ‖P basisZero‖ ≤ ‖P‖ * ‖basisZero‖ := P.le_opNorm basisZero
    _ = ‖P‖ := by simp
    _ ≤ 1 := IsStarProjection.norm_le P hP

theorem complement_vector_norm_le (Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hQ : IsStarProjection Q) : ‖(1 - Q) basisZero‖ ≤ 1 :=
  projection_vector_norm_le (1 - Q) hQ.one_sub

theorem projection_central_eq_norm_sq (P : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) :
    (P basisZero) 0 = ((‖P basisZero‖ ^ 2 : ℝ) : ℂ) := by
  have h := InvariantProjection.projection_inner_eq_inner_projected hP basisZero
  rw [basisZero, lp.inner_single_left] at h
  simpa [basisZero, inner_self_eq_norm_sq_to_K] using h

theorem central_lower_bounds (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (a : ℝ) (hP : a ≤ ((P basisZero) 0).re)
    (hQ : ((Q basisZero) 0).re ≤ 1 - a) :
    a ≤ ‖(P basisZero) 0‖ ∧ a ≤ ‖conj (((1 - Q) basisZero) 0)‖ := by
  constructor
  · exact hP.trans (Complex.re_le_norm _)
  · rw [Complex.norm_conj]
    apply le_trans _ (Complex.re_le_norm _)
    have hcoord : ((1 - Q) basisZero) 0 = 1 - (Q basisZero) 0 := by
      simp only [sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply, basisZero_zero]
    rw [hcoord, Complex.sub_re, Complex.one_re]
    linarith

theorem product_coefficient_properties {I : Type*} (s : Finset I)
    (θ c : I → ℝ) (K : ℕ) (x y : ProductCocycle.Space I)
    (hθ : ∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, ProductCocycle.representative (x i) + (K : ℝ) * θ i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * θ i ≤ ProductCocycle.representative (y i))
    (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (a : ℝ) (hPdiag : a ≤ ((P basisZero) 0).re)
    (hQdiag : ((Q basisZero) 0).re ≤ 1 - a) :
    (∀ v : ℤ, |v| ≤ (K : ℤ) →
      ‖(P basisZero) v / (ProductCocycle.cocycleVersion θ c v x : ℂ)‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i)) ∧
    (∀ v : ℤ, |v| ≤ (K : ℤ) →
      ‖(ProductCocycle.cocycleVersion θ c (-v) y : ℂ) *
        conj (((1 - Q) basisZero) (-v))‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i)) ∧
    a ≤ ‖(P basisZero) 0 / (ProductCocycle.cocycleVersion θ c 0 x : ℂ)‖ ∧
    a ≤ ‖(ProductCocycle.cocycleVersion θ c 0 y : ℂ) *
      conj (((1 - Q) basisZero) 0)‖ := by
  obtain ⟨hA, hB⟩ := ProductCocycle.finite_window_coefficients s θ c K x y hθ hc
    hleft hright (P basisZero) ((1 - Q) basisZero)
    (projection_vector_norm_le P hP) (complement_vector_norm_le Q hQ)
  obtain ⟨hA0, hB0⟩ := central_lower_bounds P Q a hPdiag hQdiag
  exact ⟨hA, hB, by simpa using hA0, by simpa using hB0⟩

theorem circle_coefficient_properties {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ) (hj : 1 ≤ j) (x y : Circle)
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < p.coordinate i y)
    (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (a : ℝ) (hPdiag : a ≤ ((P basisZero) 0).re)
    (hQdiag : ((Q basisZero) 0).re ≤ 1 - a) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(P basisZero) v / (ProductCocycle.cocycleVersion
        (fun n => p.alpha θ (n + 1)) p.flattenedCost v
        (fun n => p.q (n + 1) • x) : ℂ)‖ ≤ p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(ProductCocycle.cocycleVersion
        (fun n => p.alpha θ (n + 1)) p.flattenedCost (-v)
        (fun n => p.q (n + 1) • y) : ℂ) *
        conj (((1 - Q) basisZero) (-v))‖ ≤ p.coefficientBound j) ∧
    a ≤ ‖(P basisZero) 0 / (ProductCocycle.cocycleVersion
      (fun n => p.alpha θ (n + 1)) p.flattenedCost 0
      (fun n => p.q (n + 1) • x) : ℂ)‖ ∧
    a ≤ ‖(ProductCocycle.cocycleVersion
      (fun n => p.alpha θ (n + 1)) p.flattenedCost 0
      (fun n => p.q (n + 1) • y) : ℂ) * conj (((1 - Q) basisZero) 0)‖ := by
  obtain ⟨hA, hB⟩ := hp.finite_window_coefficients j hj x y hleft hright
    (P basisZero) ((1 - Q) basisZero)
    (projection_vector_norm_le P hP) (complement_vector_norm_le Q hQ)
  obtain ⟨hA0, hB0⟩ := central_lower_bounds P Q a hPdiag hQdiag
  exact ⟨hA, hB, by simpa using hA0, by simpa using hB0⟩

end Invariant233.ProjectionCocycleWindow

end

end OAI
