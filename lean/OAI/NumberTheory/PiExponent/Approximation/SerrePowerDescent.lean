import OAI.NumberTheory.PiExponent.Approximation.ModuleLinePowerLaws
import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteGlobalPresentation

namespace OAI

namespace PiExponent.GeometrySupport.SerrePowerDescent
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

variable {X : Scheme.{0}}

theorem ext_zero_of_iso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : ∀ x : Ext.{1} (structureSheaf X) M q, x = 0) :
    ∀ x : Ext.{1} (structureSheaf X) N q, x = 0 := by
  let E := (extFunctorObj (structureSheaf X) q).mapIso e
  intro x
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso E.hom).surjective x
  exact (congrArg E.hom (h y)).trans E.hom.hom.map_zero

def moduleTwistLineIso {L N : LineBundle X} (e : L.sheaf ≅ N.sheaf) (M : X.Modules) :
    ∀ n : ℕ, (moduleTwistFunctor L n).obj M ≅ (moduleTwistFunctor N n).obj M
  | 0 => Iso.refl M
  | n + 1 => moduleTensorIso (moduleTwistLineIso e M n) e

theorem eventual_twist_ext_zero_of_lineIso {L N : LineBundle X}
    (e : L.sheaf ≅ N.sheaf) (M : X.Modules)
    (hN : ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X) ((moduleTwistFunctor N n).obj M) q, x = 0) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X) ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  obtain ⟨B, hB⟩ := hN
  refine ⟨B, fun n hn q hq => ?_⟩
  exact ext_zero_of_iso (moduleTwistLineIso e M n).symm q (hB n hn q hq)

def residueTwistIso (L : LineBundle X) (M : X.Modules) (d n r : ℕ) :
    (moduleTwistFunctor (L.pow d) n).obj ((moduleTwistFunctor L r).obj M) ≅
      (moduleTwistFunctor L (d * n + r)).obj M :=
  moduleTwistPowerMulIso L ((moduleTwistFunctor L r).obj M) d n ≪≫
    eqToIso (by
      rw [Nat.add_comm (d * n) r, moduleTwistFunctor_add]
      rfl)

theorem eventual_twist_ext_zero_of_power (L : LineBundle X) (d : ℕ) (hd : 0 < d)
    (hpower : ∀ (A : X.Modules) [A.IsFinitePresentation],
      ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
        ∀ x : Ext.{1} (structureSheaf X) ((moduleTwistFunctor (L.pow d) n).obj A) q,
          x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X) ((moduleTwistFunctor L n).obj M) q,
        x = 0 := by
  classical
  have hresidue (r : Fin d) : ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor (L.pow d) n).obj ((moduleTwistFunctor L r.val).obj M)) q,
        x = 0 := by
    let : ((moduleTwistFunctor L r.val).obj M).IsFinitePresentation :=
      FiniteGlobalPresentation.moduleTwist_isFinitePresentation L r.val M
    exact hpower ((moduleTwistFunctor L r.val).obj M)
  choose N hN using hresidue
  let B : ℕ := Finset.univ.sup N
  refine ⟨d * B, ?_⟩
  intro n hn q hq
  let r : Fin d := ⟨n % d, Nat.mod_lt n hd⟩
  have hNB : N r ≤ B := Finset.le_sup (Finset.mem_univ r)
  have hBn : B ≤ n / d := (Nat.le_div_iff_mul_le hd).mpr (by
    simpa only [Nat.mul_comm] using hn)
  have he : d * (n / d) + r.val = n := Nat.div_add_mod n d
  let e := residueTwistIso L M d (n / d) r.val ≪≫
    eqToIso (congrArg (fun a => (moduleTwistFunctor L a).obj M) he)
  exact ext_zero_of_iso e q (hN r (n / d) (hNB.trans hBn) q hq)

end
end PiExponent.GeometrySupport.SerrePowerDescent

end OAI
