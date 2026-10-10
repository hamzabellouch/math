import OAI.Algebra.AuslanderReiten.Ext.NatComparisonExt
import OAI.Algebra.AuslanderReiten.Resolutions.MapResolutionExtComparison

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u
variable {k R S : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
  [Ring S] [Algebra k S]
variable [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} S)]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} S) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X : ModuleCat.{u} R} {Y : ModuleCat.{u} S}
variable (P : ProjectiveResolution X) (Q : ProjectiveResolution Y)

theorem natComparisonEndExt_map (e : Y ≅ F.obj X)
    (φ : ProjectiveResolution.Hom Q (mapResolution F P) e.hom) (r : ℕ)
    (f : ∀ n, P.complex.X (r+n) ⟶ P.complex.X n)
    (hf : ∀ n, f (n+1) ≫ P.complex.d (n+1) n = P.complex.d (r+(n+1)) (r+n) ≫ f n)
    (g : ∀ n, Q.complex.X (r+n) ⟶ Q.complex.X n)
    (hg : ∀ n, g (n+1) ≫ Q.complex.d (n+1) n = Q.complex.d (r+(n+1)) (r+n) ≫ g n)
    (ha : natComparisonAugmentation Q r g =
      (φ.hom.f r ≫ F.map (natComparisonAugmentation P r f)) ≫ e.inv) :
    endExt Q (natComparisonCocycle (k := k) Q Q r g hg) =
      ((Ext.mk₀ e.hom).comp
        ((endExt P (natComparisonCocycle (k := k) P P r f hf)).mapExactFunctor F) (zero_add r)).comp
          (Ext.mk₀ e.inv) (add_zero r) := by
  rw [natComparison_endExt_eq, natComparison_endExt_eq]
  exact (map_extMk_comparison F P Q e φ
    (natComparisonAugmentation P r f) (natComparison_augmented_cycle P r f hf)
    (natComparisonAugmentation Q r g) (natComparison_augmented_cycle Q r g hg) ha).symm

end ArExplicit.ResolutionProducts

end

end OAI
