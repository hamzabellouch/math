import OAI.AlgebraicGeometry.PlaneCurves.RowData
import OAI.AlgebraicGeometry.PlaneCurves.SectionKernels
import OAI.AlgebraicGeometry.PlaneCurves.ThetaPolynomialBases

namespace OAI

/-!
# Polynomial basis expressions and coefficient-branch bases
-/

section

/-! Genuine first and high coefficient branches, including the zero-degree tip
as a special source degree of the high branch. Multiplication injectivity uses
actual analyticity and finite zero orders of the marked product. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.W08 Nagata.CoefficientSpaces

/-- The first branch is literally the common automorphic-section space. -/
def firstCoefficientEquiv (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ) (hj : j ≤ m) :
    automorphicSections τ (3 * (d - 3 * m))
      (γL ^ (d - 3 * m) * normalMinusMarkedMultiplier γL γP ^ (m - j)) ≃ₗ[ℂ]
      coefficientSpace τ γL γP d m j P :=
  LinearEquiv.ofEq _ _ (by simp only [coefficientSpace, ite_eq_left hj])

/-- The high-branch map is actual multiplication by the marked product power. -/
def highCoefficientMap (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ) (hj : m < j) :
    automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j)) →ₗ[ℂ]
      coefficientSpace τ γL γP d m j P where
  toFun f := ⟨multiplyPower P (j - m).toNat f.val,
    (mem_coefficientSpace_second hj).mpr ⟨f.val, f.property, rfl⟩⟩
  map_add' f g := by apply Subtype.ext; exact (multiplyPower P (j - m).toNat).map_add f.val g.val
  map_smul' a f := by apply Subtype.ext; exact (multiplyPower P (j - m).toNat).map_smul a f.val

@[simp] theorem highCoefficientMap_apply (τ γL γP : ℂ) (d m j : ℤ)
    (P : ℂ → ℂ) (hj : m < j)
    (f : automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j))) (z : ℂ) :
    (highCoefficientMap τ γL γP d m j P hj f).val z = P z ^ (j - m).toNat * f.val z := rfl

theorem highCoefficientMap_surjective (τ γL γP : ℂ) (d m j : ℤ)
    (P : ℂ → ℂ) (hj : m < j) :
    Function.Surjective (highCoefficientMap τ γL γP d m j P hj) := by
  intro g
  obtain ⟨f, hf, hfg⟩ := (mem_coefficientSpace_second hj).mp g.property
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Subtype.ext
  exact hfg

theorem highCoefficientMap_injective (τ γL γP : ℂ) (d m j : ℤ)
    (P : ℂ → ℂ) (hj : m < j)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤) :
    Function.Injective (highCoefficientMap τ γL γP d m j P hj) := by
  intro f g hfg
  apply multiplySection_injective τ (γL ^ (d - 3 * j)) (3 * (d - 3 * j))
    P (j - m).toNat hP hPfin
  exact congrArg Subtype.val hfg

/-- The high-branch image is linearly equivalent to its genuine source sections.
This applies equally when d-3j=0; no positive-degree assumption hides the tip. -/
def highCoefficientEquiv (τ γL γP : ℂ) (d m j : ℤ)
    (P : ℂ → ℂ) (hj : m < j)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤) :
    automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j)) ≃ₗ[ℂ]
      coefficientSpace τ γL γP d m j P :=
  LinearEquiv.ofBijective (highCoefficientMap τ γL γP d m j P hj)
    ⟨highCoefficientMap_injective τ γL γP d m j P hj hP hPfin,
      highCoefficientMap_surjective τ γL γP d m j P hj⟩

/-- A source basis constructed from checked coefficient data transports to the
literal Pi-power image; no independent basis hypothesis is needed. -/
def highCoefficientBasisFromCoefficients (τ γL γP : ℂ) (d m j : ℤ)
    (P : ℂ → ℂ) (hj : m < j)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
    (I : Type*) [Fintype I] [DecidableEq I]
    (c : automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j)) →ₗ[ℂ] (I → ℂ))
    (hc : Function.Injective c)
    (v : I → automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j)))
    (hv : ∀ i, c (v i) = Pi.single i 1) :
    Basis I ℂ (coefficientSpace τ γL γP d m j P) :=
  (basisFromCoefficients c hc v hv).map
    (highCoefficientEquiv τ γL γP d m j P hj hP hPfin)

end Nagata.Workers.W10

end
end

section

/-! Exact local scalar expressions for assembled genuine polynomial basis vectors. -/
noncomputable section
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces

theorem polynomialSectionBasis_localScalar (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (P : ℂ → ℂ)
    (I : Fin ((d / 3).toNat + 1) → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (c : ∀ j, coefficientSpace τ γL γP d (m : ℤ) (j.val : ℤ) P →ₗ[ℂ] (I j → ℂ))
    (hc : ∀ j, Function.Injective (c j))
    (v : ∀ j, I j → coefficientSpace τ γL γP d (m : ℤ) (j.val : ℤ) P)
    (hv : ∀ j i, c j (v j i) = Pi.single i 1)
    (j : Fin ((d / 3).toNat + 1)) (i : I j) (z₀ x y : ℂ) :
    Nagata.W20.localScalar
      (polynomialSectionBasisFromCoefficients τ γL γP d (m : ℤ) P I c hc v hv ⟨j, i⟩)
      z₀ x y =
        (v j i).val (z₀ * Complex.exp x) * Complex.exp ((j.val : ℂ) * y) := by
  unfold Nagata.W20.localScalar
  rw [polynomialSectionBasis_as_monomial]
  simp [scalarExpression, Polynomial.sum_monomial_index, Complex.exp_nat_mul]

end Nagata.Workers.W10

end
end

section

/-! Assembly of all literal coefficient branches into a basis indexed by the
actual exponent set. Analytic source coefficient injectivity and theta identities
remain explicit inputs. No basis or dimension is postulated. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents Nagata.W08

/-- The genuine source section space before high-branch multiplication by Pi. -/
def sourceBlock (τ γL γP : ℂ) (d m j : ℤ) : Submodule ℂ (ℂ → ℂ) :=
  if j ≤ m then
    automorphicSections τ (3 * (d - 3 * m))
      (γL ^ (d - 3 * m) * normalMinusMarkedMultiplier γL γP ^ (m - j))
  else automorphicSections τ (3 * (d - 3 * j)) (γL ^ (d - 3 * j))

/-- Both positive-degree branches and the degree-zero tip use the literal source
space and the actual injective marked-product multiplication. -/
def sourceCoefficientEquiv (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤) :
    sourceBlock τ γL γP d m j ≃ₗ[ℂ] coefficientSpace τ γL γP d m j P := by
  by_cases hj : j ≤ m
  · exact (LinearEquiv.ofEq _ _ (by simp only [sourceBlock, ite_eq_left hj])).trans
      (firstCoefficientEquiv τ γL γP d m j P hj)
  · exact (LinearEquiv.ofEq _ _ (by simp only [sourceBlock, ite_eq_right hj])).trans
      (highCoefficientEquiv τ γL γP d m j P (lt_of_not_ge hj) hP hPfin)

/-- Extract the source coordinates after the proved coefficient-image equivalence. -/
def blockCoordinateMap (τ γL γP : ℂ) (d m j : ℤ) (a Δ : ℝ) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
    (c : sourceBlock τ γL γP d m j →ₗ[ℂ] (ColumnFiber d m a Δ j → ℂ)) :
    coefficientSpace τ γL γP d m j P →ₗ[ℂ] (ColumnFiber d m a Δ j → ℂ) :=
  c.comp (sourceCoefficientEquiv τ γL γP d m j P hP hPfin).symm.toLinearMap

theorem blockCoordinateMap_injective (τ γL γP : ℂ) (d m j : ℤ) (a Δ : ℝ) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
    (c : sourceBlock τ γL γP d m j →ₗ[ℂ] (ColumnFiber d m a Δ j → ℂ))
    (hc : Function.Injective c) :
    Function.Injective (blockCoordinateMap τ γL γP d m j a Δ P hP hPfin c) :=
  hc.comp (sourceCoefficientEquiv τ γL γP d m j P hP hPfin).symm.injective

/-- A genuine basis on the literal polynomial-section space, conditional exactly
on the source Laurent-coordinate injectivity and theta coefficient identities.
Every index is an actual column in the manuscript's three-branch exponent set. -/
def literalPolynomialBasis (τ γL γP : ℂ) (d m : ℤ) (a Δ : ℝ) (P : ℂ → ℂ)
    (hm : 0 ≤ m) (hd : 3 * m < d)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
    (c : ∀ j : Fin ((d / 3).toNat + 1), sourceBlock τ γL γP d m (j.val : ℤ) →ₗ[ℂ]
      (ColumnFiber d m a Δ (j.val : ℤ) → ℂ))
    (hc : ∀ j, Function.Injective (c j))
    (theta : ∀ j : Fin ((d / 3).toNat + 1), ColumnFiber d m a Δ (j.val : ℤ) →
      sourceBlock τ γL γP d m (j.val : ℤ))
    (htheta : ∀ j K, c j (theta j K) = Pi.single K 1) :
    Basis (Column d m a Δ) ℂ (polynomialSections τ γL γP d m P) := by
  classical
  let I := fun j : Fin ((d / 3).toNat + 1) => ColumnFiber d m a Δ (j.val : ℤ)
  let e := fun j : Fin ((d / 3).toNat + 1) =>
    sourceCoefficientEquiv τ γL γP d m (j.val : ℤ) P hP hPfin
  let cc := fun j => blockCoordinateMap τ γL γP d m (j.val : ℤ) a Δ P hP hPfin (c j)
  have hinj : ∀ j, Function.Injective (cc j) := fun j =>
    blockCoordinateMap_injective τ γL γP d m (j.val : ℤ) a Δ P hP hPfin (c j) (hc j)
  let v := fun j K => e j (theta j K)
  have hv : ∀ j K, cc j (v j K) = Pi.single K 1 := by
    intro j K
    change c j ((e j).symm (e j (theta j K))) = _
    rw [LinearEquiv.symm_apply_apply, htheta]
  exact (polynomialSectionBasisFromCoefficients τ γL γP d m P I cc hinj v hv).reindex
    (columnFiberEquiv d m a Δ hm hd)

end Nagata.Workers.W10

end
end

section

/-! Exact monomials and covering-coordinate expressions for the basis indexed by
literal manuscript columns. Analytic coefficient completeness remains explicit. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents

variable (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (a Δ : ℝ) (P : ℂ → ℂ)
  (hd : 3 * (m : ℤ) < d)
  (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
  (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
  (c : ∀ j : Fin ((d / 3).toNat + 1), sourceBlock τ γL γP d (m : ℤ) (j.val : ℤ) →ₗ[ℂ]
    (ColumnFiber d (m : ℤ) a Δ (j.val : ℤ) → ℂ))
  (hc : ∀ j, Function.Injective (c j))
  (theta : ∀ j : Fin ((d / 3).toNat + 1), ColumnFiber d (m : ℤ) a Δ (j.val : ℤ) →
    sourceBlock τ γL γP d (m : ℤ) (j.val : ℤ))
  (htheta : ∀ j K, c j (theta j K) = Pi.single K 1)

/-- Every literal column basis element is exactly its fiber monomial. -/
theorem literalPolynomialBasis_as_monomial
    (j : Fin ((d / 3).toNat + 1)) (K : ColumnFiber d (m : ℤ) a Δ (j.val : ℤ)) :
    (literalPolynomialBasis τ γL γP d (m : ℤ) a Δ P (Int.natCast_nonneg m) hd hP hPfin
      c hc theta htheta (columnFiberEquiv d (m : ℤ) a Δ (Int.natCast_nonneg m) hd ⟨j, K⟩)).val =
    Polynomial.monomial j.val
      (sourceCoefficientEquiv τ γL γP d (m : ℤ) (j.val : ℤ) P hP hPfin (theta j K)).val := by
  classical
  unfold literalPolynomialBasis
  rw [Basis.reindex_apply, Equiv.symm_apply_apply]
  exact polynomialSectionBasis_as_monomial _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The actual scalar expression equals a coefficient function times the fiber
exponential. The equality is global, hence supplies every required local germ. -/
theorem literalPolynomialBasis_localScalar
    (j : Fin ((d / 3).toNat + 1)) (K : ColumnFiber d (m : ℤ) a Δ (j.val : ℤ))
    (z₀ x y : ℂ) :
    Nagata.W20.localScalar
      (literalPolynomialBasis τ γL γP d (m : ℤ) a Δ P (Int.natCast_nonneg m) hd hP hPfin
        c hc theta htheta (columnFiberEquiv d (m : ℤ) a Δ (Int.natCast_nonneg m) hd ⟨j, K⟩))
      z₀ x y =
    (sourceCoefficientEquiv τ γL γP d (m : ℤ) (j.val : ℤ) P hP hPfin (theta j K)).val
      (z₀ * Complex.exp x) * Complex.exp ((j.val : ℂ) * y) := by
  unfold Nagata.W20.localScalar
  rw [literalPolynomialBasis_as_monomial]
  simp [scalarExpression, Polynomial.sum_monomial_index, Complex.exp_nat_mul]

end Nagata.Workers.W10

end
end

end OAI
