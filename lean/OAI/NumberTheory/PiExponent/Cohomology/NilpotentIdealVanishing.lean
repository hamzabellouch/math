import OAI.NumberTheory.PiExponent.Approximation.ClosedSupportedSerre
import OAI.NumberTheory.PiExponent.Cohomology.IdealPowerCohomology
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPowerDescent

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.IdealModule
variable {X : Scheme.{0}}
local instance : HasExt.{1} X.Modules := HasExt.standard _
attribute [local irreducible] closedModule powerLayer moduleTwistFunctor

theorem fullSupport_ideal_ext_zero_of_isAffine [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) [IsAffine I.subscheme]
    (q : ℕ) (hq : 0 < q) (x : Abelian.Ext.{1} (structureSheaf X) (closedModule I) q) : x = 0 := by
  let : IsLocallyNoetherian I.subscheme := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  let : IsNoetherian I.subscheme := {}
  obtain ⟨N,hNpos,hN⟩ := powerModule_eventually_isZero I hI
  have hLayer (k : ℕ) (_hk : k < N)
      (z : Abelian.Ext.{1} (structureSheaf X) (powerLayer I k) q) : z = 0 := by
    let : (descendedPowerLayer I k).IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
        (descendedPowerLayer I k)).choose.isQuasicoherent
    exact affine_closed_pushforward_ext_zero I.subschemeι (powerLayer I k)
      (descendedPowerLayer I k) (powerLayerPushforwardIso I k).symm q hq z
  have h := powerModule_ext_zero_of_layers I N q hN hLayer 1 hNpos
  have h' : ∀ z : Abelian.Ext.{1} (structureSheaf X) (closedModule I) q, z = 0 :=
    (congrArg (fun J : X.IdealSheafData =>
      ∀ z : Abelian.Ext.{1} (structureSheaf X) (closedModule J) q, z = 0) (pow_one I)).mp h
  exact h' x

theorem isAffine_of_fullSupport [IsNoetherian X] (I : X.IdealSheafData)
    (hI : I.support = ⊤) [IsAffine I.subscheme] : IsAffine X :=
  isAffine_of_fullSupport_of_ideal_ext_one_zero I hI
    (fullSupport_ideal_ext_zero_of_isAffine I hI 1 (by decide))

theorem fullSupport_eventual_ideal_twist_ext_zero [IsNoetherian X]
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support = ⊤)
    (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) :
    ∃ B, ∀ n, B ≤ n → ∀ q, 0 < q →
      ∀ x : Abelian.Ext.{1} (structureSheaf X)
        ((moduleTwistFunctor L n).obj (closedModule I)) q, x = 0 := by
  apply eventual_ideal_twist_vanishing_of_layers I hI L
  intro k
  exact eventual_twist_ext_zero_of_closed_pushforward p I.subschemeι L hL
    (powerLayer I k) (descendedPowerLayer I k) (powerLayerPushforwardIso I k).symm

end
end PiExponentSeshadri.Geometry

end OAI
