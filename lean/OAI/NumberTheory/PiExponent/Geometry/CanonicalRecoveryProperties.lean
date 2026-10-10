import OAI.NumberTheory.PiExponent.Ampleness.ExceptionalRecoveryMap
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealPullbackOpenSquare

namespace OAI

noncomputable section
namespace PiExponent.CanonicalRecoveryProperties
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open GeometrySupport

def ComapBijective {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (U : X.Opens) : Prop :=
  Function.Bijective ((IdealPullbackMap.comap f I).app U)

def OrdinaryBijective {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)
    (n : ℕ) (U : X.Opens) : Prop :=
  Function.Bijective ((ExceptionalRecoveryMap.ordinaryMap f I E ι hE n).app U)

theorem ordinary_iff_comap {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)
    (n : ℕ) (U : X.Opens) :
    OrdinaryBijective f I E ι hE n U ↔ ComapBijective f (I^n) U := by
  have hb := ConcreteCategory.bijective_of_isIso
    ((PresentedIdealIso.powerIso I f E ι hE n).inv.app (f ⁻¹ᵁ U))
  change Function.Bijective
    (((PresentedIdealIso.powerIso I f E ι hE n).inv.app (f ⁻¹ᵁ U)) ∘
      ((IdealPullbackMap.comap f (I^n)).app U)) ↔ _
  exact hb.of_comp_iff' _

theorem comap_open_square {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X.Opens) (U' : X'.Opens) (V' : Y'.Opens)
    (hj : j ''ᵁ U' = U) (hk : k ''ᵁ V' = f ⁻¹ᵁ U)
    (hv : V' = f' ⁻¹ᵁ U') :
    ComapBijective f I U ↔ ComapBijective f' (I.comap j) U' :=
  IdealSectionRestriction.comap_app_bijective_iff_open_square f j k f' h I U U' V' hj hk hv

end PiExponent.CanonicalRecoveryProperties

end

end OAI
