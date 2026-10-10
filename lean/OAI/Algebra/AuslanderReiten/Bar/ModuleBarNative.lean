import OAI.Algebra.AuslanderReiten.Bar.ModuleBarCubic

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]

def nativeResolution : ProjectiveResolution (ModuleCat.of R M) := resolution k R M

instance nativeResolution_finite [Module.Finite k R] [Module.Finite k M] (n : ℕ) :
    Module.Finite R ((nativeResolution k R M).complex.X n) := finite k R M n

variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

def nativeCubicMap (n : ℕ) : (nativeResolution k R M).complex.X (n+3) ⟶
    (nativeResolution k R M).complex.X n := cubicMap k R M p n

include hp in
theorem nativeCubicMap_comm (n : ℕ) :
    nativeCubicMap k R M p (n+1) ≫ (nativeResolution k R M).complex.d (n+1) n =
      (nativeResolution k R M).complex.d (n+4) (n+3) ≫ nativeCubicMap k R M p n :=
  cubicMap_comm k R M p hp n

variable [HasDerivedCategory (ModuleCat.{u} R)]

theorem nativeCubicMap_class :
    ResolutionProducts.endExt (nativeResolution k R M)
      (ResolutionProducts.natCubicCocycle (k := k) (nativeResolution k R M)
        (nativeCubicMap k R M p) (nativeCubicMap_comm k R M p hp)) =
      (extClass3 k R M p hp : Ext (ModuleCat.of R M) (ModuleCat.of R M) 3) :=
  cubicCocycle_endExt k R M p hp

end ArExplicit.ModuleBar

end

end OAI
