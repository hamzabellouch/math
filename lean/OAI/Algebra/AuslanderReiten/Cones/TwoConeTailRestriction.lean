import OAI.Algebra.AuslanderReiten.Cones.TwoConeTail
import OAI.Algebra.AuslanderReiten.Cones.TwoConeRestriction

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
universe u
variable {R S : Type u} [Ring R] [Ring S] (j : S →+* R) (D : Data R)
variable (Q : ℕ → ModuleCat.{u} R) (δ : (n : ℕ) → Q (n+1) →ₗ[R] Q n)
variable (φ : (n : ℕ) → Q (n+3) →ₗ[R] term D n)

abbrev restrictedSource (n : ℕ) : ModuleCat.{u} S := (ModuleCat.restrictScalars j).obj (Q n)

def restrictedDifferential (n : ℕ) : restrictedSource j Q (n+1) →ₗ[S] restrictedSource j Q n :=
  ((ModuleCat.restrictScalars j).map (ModuleCat.ofHom (δ n))).hom

def restrictedHighLift (n : ℕ) : restrictedSource j Q (n+3) →ₗ[S] term (D.restrict j) n :=
  (termRestrictionEquiv j D n).toLinearMap.comp
    ((ModuleCat.restrictScalars j).map (ModuleCat.ofHom (φ n))).hom

theorem restrictedHighLift_comm
    (hφ : ∀ n, (d D n).comp (φ (n+1)) = (φ n).comp (δ (n+3))) (n : ℕ) :
    (d (D.restrict j) n).comp (restrictedHighLift j D Q φ (n+1)) =
      (restrictedHighLift j D Q φ n).comp (restrictedDifferential j Q δ (n+3)) := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (hφ n) x

end ArExplicit.TwoCone

end

end OAI
