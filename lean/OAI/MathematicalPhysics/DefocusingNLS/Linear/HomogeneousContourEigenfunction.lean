import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousEigenfunctionPDE
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousContourGenerator

namespace OAI

/-! # Classical eigenfunctions from the actual finite contour generator

The finite-dimensional semigroup generator supplies classical two-channel
solutions, and a nonzero contour vector supplies a nonzero physical pair.
-/

open Set
open scoped Laplacian ZeroAtInfty

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

/-- The physical coupled equation, with the actual odd-power coefficients. -/
def IsClassicalLinearizedPair (a b : ℝ) (m : ℕ) (q f g : E → ℂ) (lam : ℂ) : Prop :=
  ContDiff ℝ 2 f ∧ ContDiff ℝ 2 g ∧ ∀ x : E,
    (lam * f x = Complex.I * Δ f x - (1 / 2 : ℂ) * fderiv ℝ f x x +
      (-(a : ℂ) + Complex.I * (b : ℂ)) * f x - Complex.I *
        ((((m + 1 : ℕ) : ℂ) * q x ^ m * star (q x) ^ m) * f x +
          ((m : ℂ) * q x ^ (m + 1) * star (q x) ^ (m - 1)) * g x)) ∧
    (lam * g x = -Complex.I * Δ g x - (1 / 2 : ℂ) * fderiv ℝ g x x +
      (-(a : ℂ) - Complex.I * (b : ℂ)) * g x + Complex.I *
        (star (((m + 1 : ℕ) : ℂ) * q x ^ m * star (q x) ^ m) * g x +
          star ((m : ℂ) * q x ^ (m + 1) * star (q x) ^ (m - 1)) * f x))

theorem homogeneous_physical_pair_nonzero (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (w : HomogeneousY a k × HomogeneousY a k) (hw : w ≠ 0) :
    ∃ x : E, homogeneousPhysicalCLM a k ha ha1 hk w.1 x ≠ 0 ∨
      homogeneousPhysicalCLM a k ha ha1 hk w.2 x ≠ 0 := by
  by_contra! h
  have h₁ : w.1 = 0 := by
    apply homogeneousPhysicalCLM_injective a k ha ha1 hk
    apply DFunLike.ext
    intro x
    simpa only [map_zero, ZeroAtInftyContinuousMap.zero_apply] using (h x).1
  have h₂ : w.2 = 0 := by
    apply homogeneousPhysicalCLM_injective a k ha ha1 hk
    apply DFunLike.ext
    intro x
    simpa only [map_zero, ZeroAtInftyContinuousMap.zero_apply] using (h x).2
  exact hw (Prod.ext h₁ h₂)

/-- Every nonzero eigenvector of the finite contour generator gives a nonzero
classical solution of the actual linearized PDE. -/
theorem homogeneous_contour_generator_classical (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ) (q : HomogeneousY a k)
    (Q : (HomogeneousY a k × HomogeneousY a k) →L[ℂ]
      (HomogeneousY a k × HomogeneousY a k))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 hk m q t) Q)
    (hfin : FiniteDimensional ℂ Q.range) (G : Q.range →L[ℂ] Q.range)
    (hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep a b k ha ha1 hk m q) Q hcomm t =
        NormedSpace.exp ((t : ℝ) • G))
    (lam : ℂ) (w : Q.range) (hw : w ≠ 0) (he : G w = lam • w) :
    let P := fun f : HomogeneousY a k =>
      fun x : E => homogeneousPhysicalCLM a k ha ha1 hk f x
    IsClassicalLinearizedPair a b m (P q) (P (w : HomogeneousY a k × HomogeneousY a k).1)
        (P (w : HomogeneousY a k × HomogeneousY a k).2) lam ∧
      ∃ x : E, P (w : HomogeneousY a k × HomogeneousY a k).1 x ≠ 0 ∨
        P (w : HomogeneousY a k × HomogeneousY a k).2 x ≠ 0 := by
  dsimp only
  constructor
  · exact homogeneous_eigenvector_classical_channels a b k ha ha1 hk m q lam
      (w : HomogeneousY a k × HomogeneousY a k)
      (projectionSemigroup_eigenvector _ Q hcomm hfin G hG lam w he)
  · apply homogeneous_physical_pair_nonzero a k ha ha1 hk
    intro h
    apply hw
    exact Subtype.ext h

end DefocusingNLS

end OAI
