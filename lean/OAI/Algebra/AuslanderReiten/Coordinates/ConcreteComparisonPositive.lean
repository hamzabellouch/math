import OAI.Algebra.AuslanderReiten.Cones.ConcreteTwoTwistRows
import OAI.Algebra.AuslanderReiten.Fibers.TensorFiberCoordinateIso
import OAI.Algebra.AuslanderReiten.Complete.ConcreteTateModel

namespace OAI

noncomputable section
open CategoryTheory CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H₁ H₂ : kˣ)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.A k q))]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : Resolution.NoPositivePowerOne q)
variable (g : CohomologyClass (A.simpleComplete q) (fiberComplete q H₁ H₂) 0)
variable (hg : fiberFullRhoPair q H₁ H₂ 0 g =
  (CompleteComparison.fullHomIdentity (A.simpleComplete q),
    CompleteComparison.fullHomIdentity (A.simpleComplete q)))
variable (hrho : ∀ n : ℤ, 0 < n → Function.Bijective (fiberFullRhoPair q H₁ H₂ n))
variable (hsep : ∀ m : ℕ, 0 < m → (((H₁⁻¹ : kˣ) : k)^m) ≠ (((H₂⁻¹ : kˣ) : k)^m))
include hq hq1 hp hg hrho hsep

theorem tensorFiberComparison_positive_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (TriangularInduction.tensorComparison (tensorFiberMap q H₁ H₂ g) (n : ℤ)) := by
  by_cases hd : 3 ∣ n
  · obtain ⟨m,rfl⟩ := hd
    have hm : 0 < m := by omega
    apply TriangularInduction.tensorComparison_bijective_of_coordinates
      (tensorFiberMap q H₁ H₂ g) _
      (tensorFiberRhoEquiv q H₁ H₂ _ (hrho _ (by omega)))
      (((H₁⁻¹ : kˣ) : k)^m) (((H₂⁻¹ : kˣ) : k)^m) (hsep m hm)
    intro x
    exact (tensorFiberRhoEquiv_apply q H₁ H₂ _ (hrho _ (by omega)) _).trans
      (tensorFiberComparison_rows q H₁ H₂ hq hq1 hp g hg m hm x)
  · let : Subsingleton (CohomologyClass (A.simpleComplete q) (A.simpleComplete q) (n : ℤ)) :=
      (A.positiveTateModel q hq hq1 hp).outside (n : ℤ) (by omega) (by
        intro m hm
        apply hd
        exact ⟨m, by exact_mod_cast hm⟩)
    apply TriangularInduction.tensorComparison_bijective_of_coordinates
      (tensorFiberMap q H₁ H₂ g) _
      (tensorFiberRhoEquiv q H₁ H₂ _ (hrho _ (by omega)))
      (0 : k) 1 zero_ne_one
    intro x
    exact Subsingleton.elim _ _

end ArExplicit.T

end

end OAI
