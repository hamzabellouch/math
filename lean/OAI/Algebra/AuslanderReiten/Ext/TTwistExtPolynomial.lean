import OAI.Algebra.AuslanderReiten.Bar.ModuleBarTwistIdentity
import OAI.Algebra.AuslanderReiten.Ext.TExplicitPolynomial
import OAI.Algebra.AuslanderReiten.Homology.TTwistCompatibility

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k) (H : kˣ)
local notation "T" => ArExplicit.T k q
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]

def tInverseTwistExt (n : ℕ) : TSelfExt q n →ₗ[k] TSelfExt q n :=
  ModuleBar.twistExtAction k T (Simple q) (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (ArExplicit.T.inverseTwist_simple_compatible q H) n

theorem tInverseTwistExt_identity :
    tInverseTwistExt q H 0 (Ext.mk₀ (𝟙 (ModuleCat.of T (Simple q)))) =
      Ext.mk₀ (𝟙 (ModuleCat.of T (Simple q))) :=
  ModuleBar.twistExtAction_identity k T (Simple q) (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (ArExplicit.T.inverseTwist_simple_compatible q H)

theorem tInverseTwistExt_mul (n : ℕ) (x : TSelfExt q n) :
    tInverseTwistExt q H (n+3) ((tExplicitP q).comp x (by omega : 3+n=n+3)) =
      ((H⁻¹ : kˣ) : k) •
        (tExplicitP q).comp (tInverseTwistExt q H n x) (by omega : 3+n=n+3) := by
  have ht := ModuleBar.twistExtAction_cubic k T (Simple q) (TrivialExtension.twist H).symm
    (LinearEquiv.refl k _) (ArExplicit.T.inverseTwist_simple_compatible q H)
    (CocycleData.p q) (CocycleData.p_isCocycle3 q) ((H⁻¹ : kˣ) : k)
    (by
      intro a b d m
      simp only [LinearEquiv.refl_apply]
      convert ArExplicit.T.p_inverse_twist_simple q H a b d m using 1) n x
  change tInverseTwistExt q H (n+3) ((tExplicitP q).comp x (by omega : 3+n=n+3)) =
    ((H⁻¹ : kˣ) : k) • (tExplicitP q).comp (tInverseTwistExt q H n x)
      (by omega : 3+n=n+3) at ht
  exact ht

variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (hp : NoPositivePowerOne q)

theorem tInverseTwistExt_power (n : ℕ) :
    tInverseTwistExt q H (3*n) (tExplicitPower q hq hq1 hp n) =
      (((H⁻¹ : kˣ) : k)^n) • tExplicitPower q hq hq1 hp n := by
  induction n with
  | zero =>
    simp only [tExplicitPower_zero, pow_zero, one_smul, Nat.mul_zero]
    exact tInverseTwistExt_identity q H
  | succ n ih =>
    rw [tExplicitPower_succ]
    change tInverseTwistExt q H (3*n+3)
        ((tExplicitP q).comp (tExplicitPower q hq hq1 hp n) (by omega)) = _
    rw [tInverseTwistExt_mul, ih, Ext.comp_smul, smul_smul, pow_succ]
    congr 1
    exact mul_comm _ _

include hq hq1 hp in
theorem tInverseTwistExt_all (n : ℕ) (x : TSelfExt q (3*n)) :
    tInverseTwistExt q H (3*n) x = (((H⁻¹ : kˣ) : k)^n) • x := by
  obtain ⟨a, ha, _⟩ := tExplicit_coefficient q hq hq1 hp n x
  rw [← ha, map_smul, tInverseTwistExt_power q H hq hq1 hp n]
  exact smul_comm _ _ _

end ArExplicit.Resolution

end

end OAI
