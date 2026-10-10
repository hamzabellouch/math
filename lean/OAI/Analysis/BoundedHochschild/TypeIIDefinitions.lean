import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts

namespace OAI

/-! Central projections and the finite type-II condition. -/

noncomputable section

open scoped ComplexOrder
namespace FinitePathMain

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def CentralProjection (p : M) : Prop :=
  IsStarProjection p ∧ ∀ a : M, Commute p a

def AbelianProjection (p : M) : Prop :=
  IsStarProjection p ∧ ∀ a b : M, Commute (p * a * p) (p * b * p)

def TypeICentralSummand (z : M) : Prop :=
  CentralProjection z ∧ ∀ c : M, CentralProjection c → c ≤ z → c ≠ 0 →
    ∃ p : M, AbelianProjection p ∧ p ≤ c ∧ p ≠ 0

def TypeII1 (M : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M] : Prop :=
  (∀ a : M, star a * a = 1 → a * star a = 1) ∧
    ∀ z : M, TypeICentralSummand z → z = 0

def word {G : Type*} [Monoid G] {n : ℕ} (ω : Fin n → G) : G :=
  (List.ofFn ω).prod

def signedValue {A : Type*} (v : A → unitary M) (a : A × Bool) : unitary M :=
  if a.2 then v a.1 else (v a.1)⁻¹

def pathValue {A : Type*} {r n : ℕ} (v : A → unitary M)
    (w : Fin r × Fin n → A × Bool) (i : Fin r) : unitary M :=
  word (fun j => signedValue v (w (i,j)))

def FinitePathTests (τ : M →ₚ[ℂ] ℂ) : Prop :=
  ∀ (C D T : Type) [Fintype C] [Fintype D] [Fintype T],
    Nonempty D → ∀ (v : C → unitary M) (r n : T → ℕ)
      (w : ∀ t, Fin (r t) × Fin (n t) → (C ⊕ D) × Bool)
      (q : ∀ t, FreeGroup (Fin (r t))),
    (∀ t, q t ≠ 1) →
    (∀ t, ∃ (s : Fin (r t) → Fin (n t)) (a : Fin (r t) → D),
      (∀ i, (w t (i,s i)).1 = Sum.inr (a i)) ∧
      (∀ i z, (w t z).1 = Sum.inr (a i) → z=(i,s i))) →
    ∀ ε : ℝ, 0 < ε → ∃ u : D → unitary M,
      ∀ t, ‖τ (FreeGroup.lift (pathValue (Sum.elim v u) (w t)) (q t) : M)‖ < ε

def ProducerGoal : Prop :=
  ∀ (M X : Type*) [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ),
    TypeII1 M → τ 1 = 1 → (∀ a b : M, τ (a*b) = τ (b*a)) →
    (∃ z : X, ∀ a : M, τ a = star (e.symm a z)) →
    (∀ a : M, τ (star a*a) = 0 → a = 0) → FinitePathTests τ

end FinitePathMain

end

end OAI
