import OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer
import OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula
import OAI.NumberTheory.PiExponent.Approximation.SerreAssembly

namespace OAI

namespace PiExponent.ClosedImmersionSerreTransfer
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
local instance : HasExt.{1} X.Modules := HasExt.standard _
local instance : HasExt.{1} Y.Modules := HasExt.standard _

theorem twist_ext_zero_iff (M : X.Modules) (L : LineBundle Y) (n q : ℕ) :
    (∀ x : Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor (L.pullback f) n).obj M) q, x = 0) ↔
    (∀ x : Ext.{1} (structureSheaf Y)
      ((moduleTwistFunctor L n).obj ((Scheme.Modules.pushforward f).obj M)) q, x = 0) := by
  refine (ext_zero_iff f ((moduleTwistFunctor (L.pullback f) n).obj M) q).trans ?_
  let e := (extFunctorObj (structureSheaf Y) q).mapIso (ProjectionFormula.twistIso f M L n)
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.hom).surjective x
    exact (congrArg e.hom (h y)).trans e.hom.hom.map_zero
  · intro h x
    apply (ConcreteCategory.bijective_of_isIso e.hom).injective
    exact (h _).trans e.hom.hom.map_zero.symm

theorem eventual_twist_ext_zero_of_ambient [IsLocallyNoetherian Y]
    (L : LineBundle Y)
    (hSerre : ∀ (N : Y.Modules) [N.IsFinitePresentation],
      ∃ N0, ∀ n, N0 ≤ n → ∀ q, 0 < q →
        ∀ x : Ext.{1} (structureSheaf Y) ((moduleTwistFunctor L n).obj N) q, x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N0, ∀ n, N0 ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor (L.pullback f) n).obj M) q, x = 0 := by
  obtain ⟨N0, hN0⟩ := hSerre ((Scheme.Modules.pushforward f).obj M)
  refine ⟨N0, fun n hn q hq => ?_⟩
  exact (twist_ext_zero_iff f M L n q).mpr (hN0 n hn q hq)

theorem eventual_twist_ext_zero_of_ambient_section_cover
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf Y) (modulePow Y L.sheaf n) q, x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N0, ∀ n, N0 ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor (L.pullback f) n).obj M) q, x = 0 := by
  apply eventual_twist_ext_zero_of_ambient f L _ M
  intro N hN
  exact PiExponent.GeometrySupport.SerreAssembly.eventual_twist_ext_zero_of_section_cover
    L l hl s hcover haffine hpow N

end
end PiExponent.ClosedImmersionSerreTransfer

end OAI
