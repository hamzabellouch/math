import OAI.Algebra.AuslanderReiten.Coordinates.FiniteSourceCoordinates
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomShiftedIdentity
import OAI.Algebra.AuslanderReiten.Coordinates.IteratedShiftNaturality

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
open scoped ModuleCat.Algebra
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [Module.Finite k R]

structure FiniteCoverTower where
  obj : ℕ → FiniteLeftModule k R
  middle : ℕ → FiniteLeftModule k R
  inclusion : ∀ n, (obj (n+1)).carrier →ₗ[R] (middle n).carrier
  quotient : ∀ n, (middle n).carrier →ₗ[R] (obj n).carrier
  injective : ∀ n, Function.Injective (inclusion n)
  surjective : ∀ n, Function.Surjective (quotient n)
  exact : ∀ n, Function.Exact (inclusion n) (quotient n)
  projective : ∀ n, Module.Projective R (middle n).carrier

namespace FiniteCoverTower
variable (τ : FrobeniusTrace k R) (T : FiniteCoverTower (k := k) (R := R))
local notation "K" => FiniteLeftModule.completeCochain τ (T.obj 0)
local notation "Q" => HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

def stepIso (n : ℕ) : (Q).obj ((T.obj n).completeCochain τ) ≅
    ((Q).obj ((T.obj (n+1)).completeCochain τ))⟦(1 : ℤ)⟧ := by
  letI := T.projective n
  exact FiniteLeftModule.projectiveMiddleShiftIso τ (T.inclusion n) (T.quotient n)
    (T.injective n) (T.surjective n) (T.exact n)

def shiftIso (n : ℕ) : (Q).obj K ≅ ((Q).obj ((T.obj n).completeCochain τ))⟦(n : ℤ)⟧ :=
  iteratedShiftIso (fun n => (Q).obj ((T.obj n).completeCochain τ)) (T.stepIso τ) n

def boundaryClass (n : ℕ) :
    CohomologyClass ((T.obj n).completeCochain τ) ((T.obj (n+1)).completeCochain τ) 1 :=
  (fullHomShiftedHomotopyEquiv k _ _ 1).symm
    (FiniteLeftModule.resolutionConnecting τ (T.inclusion n) (T.quotient n)
      (T.injective n) (T.surjective n) (T.exact n))

def coverClass : (n : ℕ) → CohomologyClass K ((T.obj n).completeCochain τ) (n : ℤ)
  | 0 => fullHomIdentity K
  | n+1 => fullHomProduct (coverClass n) (boundaryClass τ T n)

omit [CharP k 2] in
theorem coverClass_hom (n : ℕ) :
    fullHomShiftedHomotopyEquiv k K ((T.obj n).completeCochain τ) (n : ℤ)
      (T.coverClass τ n) = (T.shiftIso τ n).hom := by
  induction n with
  | zero => exact fullHomShiftedHomotopyEquiv_identity k K
  | succ n ih =>
    change fullHomShiftedHomotopyEquiv k K ((T.obj (n+1)).completeCochain τ) ((n : ℤ)+1)
      (fullHomProduct (T.coverClass τ n) (T.boundaryClass τ n)) = _
    rw [fullHomShiftedHomotopyEquiv_product, ih]
    simp only [boundaryClass, LinearEquiv.apply_symm_apply]
    rfl

variable (S : FiniteLeftModule k R)
variable (u₀ : CohomologyClass (S.completeCochain τ) ((T.obj 0).completeCochain τ) 0)

def coverClassFrom : (n : ℕ) →
    CohomologyClass (S.completeCochain τ) ((T.obj n).completeCochain τ) (n : ℤ)
  | 0 => u₀
  | n+1 => fullHomProduct (coverClassFrom n) (boundaryClass τ T n)

variable (s : ∀ n : ℕ, RawCokernelAt (S.completeCochain τ) (n : ℤ) →ₗ[R] (T.obj n).carrier)
variable (A : ∀ n : ℕ, (S.completeCochain τ).X (-(n : ℤ)) →ₗ[R] (T.middle n).carrier)
variable (hzero : FiniteLeftModule.HasSourceCoordinates τ S (T.obj 0) 0 u₀ (s 0))
variable (hquotient : ∀ n : ℕ, FiniteLeftModule.SourceQuotientSquare τ S
  (T.middle n) (T.obj n) (n : ℤ) (T.quotient n) (s n) (A n))
variable (hinclusion : ∀ n : ℕ, FiniteLeftModule.SourceInclusionSquare τ S
  (T.obj (n+1)) (T.middle n) (n : ℤ) (T.inclusion n) (A n) (s (n+1)))

include hzero hquotient hinclusion in

theorem coverClassFrom_source (n : ℕ) :
    FiniteLeftModule.HasSourceCoordinates τ S (T.obj n) (n : ℤ)
      (T.coverClassFrom τ S u₀ n) (s n) := by
  induction n with
  | zero => exact hzero
  | succ n ih =>
    exact FiniteLeftModule.HasSourceCoordinates.connecting_product τ
      (T.inclusion n) (T.quotient n) (T.injective n) (T.surjective n) (T.exact n)
      (T.coverClassFrom τ S u₀ n) (s n) (A n) (s (n+1)) ih (hquotient n) (hinclusion n)

end FiniteCoverTower
end ArExplicit

end

end OAI
