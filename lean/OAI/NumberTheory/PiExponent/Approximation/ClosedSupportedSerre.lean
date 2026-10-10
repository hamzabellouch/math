import OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer
import OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula
import OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
variable {X Y : Scheme.{0}}
local instance (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _

theorem ext_zero_of_moduleIso {M N : X.Modules} (e : M ≅ N) (q : ℕ)
    (h : ∀ x : Abelian.Ext.{1} (structureSheaf X) N q, x = 0)
    (x : Abelian.Ext.{1} (structureSheaf X) M q) : x = 0 := by
  let E := (extFunctorObj (structureSheaf X) q).mapIso e
  apply (ConcreteCategory.bijective_of_isIso E.hom).injective
  change E.hom x = E.hom 0
  rw [map_zero]
  exact h (E.hom x)

theorem affine_closed_pushforward_ext_zero (i : Y ⟶ X) [IsClosedImmersion i]
    [IsAffine Y] [IsNoetherian Y] (M : X.Modules) (N : Y.Modules)
    [N.IsQuasicoherent] (e : M ≅ (Scheme.Modules.pushforward i).obj N)
    (q : ℕ) (hq : 0 < q) (x : Abelian.Ext.{1} (structureSheaf X) M q) : x = 0 := by
  apply ext_zero_of_moduleIso e q _ x
  apply (PiExponent.ClosedImmersionSerreTransfer.ext_zero_iff i N q).mp
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hq)
  exact AffineSchemeCohomology.affine_ext_zero Y N k

theorem eventual_twist_ext_zero_of_closed_pushforward
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (i : Y ⟶ X) [IsClosedImmersion i]
    (L : LineBundle X) (hL : (L.pullback i).IsAmple)
    (M : X.Modules) (N : Y.Modules) [N.IsFinitePresentation]
    (e : M ≅ (Scheme.Modules.pushforward i).obj N) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X) ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  obtain ⟨B,hB⟩ := PiExponent.GeometrySupport.NoetherianAmpleSerreVanishing.ample_serre_vanishing
    (i ≫ p) (L.pullback i) hL N
  refine ⟨B, fun n hn q hq x => ?_⟩
  let E := (moduleTwistFunctor L n).mapIso e ≪≫
    (PiExponent.ProjectionFormula.twistIso i N L n).symm
  apply ext_zero_of_moduleIso E q _ x
  exact (PiExponent.ClosedImmersionSerreTransfer.ext_zero_iff i
    ((moduleTwistFunctor (L.pullback i) n).obj N) q).mp (hB n hn q hq)

end
end PiExponentSeshadri.Geometry

end OAI
