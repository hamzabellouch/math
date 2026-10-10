import OAI.Algebra.AuslanderReiten.Bar.ModuleBarSuffix
import OAI.Algebra.AuslanderReiten.Ext.NatCubicExt

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M] [CharP k 2]
variable (p : AbsoluteBar.Cochain3 k R) (hp : AbsoluteBar.IsCocycle3 k R p)

def cubicMap (n : ℕ) : (resolution k R M).complex.X (n+3) ⟶ (resolution k R M).complex.X n :=
  ModuleCat.ofHom (X := moduleObject k R M (n+4)) (Y := moduleObject k R M (n+1))
    (suffixComparisonMap k R M p n)

include hp in
theorem cubicMap_comm (n : ℕ) :
    cubicMap k R M p (n+1) ≫ (resolution k R M).complex.d (n+1) n =
      (resolution k R M).complex.d (n+4) (n+3) ≫ cubicMap k R M p n := by
  change cubicMap k R M p (n+1) ≫ (complex k R M).d (n+1) n =
    (complex k R M).d (n+3+1) (n+3) ≫ cubicMap k R M p n
  rw [complex_d, complex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact suffixComparison_boundary k R M p hp (n+1) x

def cubicCocycle : Cocycle (resolution k R M).cochainComplex (resolution k R M).cochainComplex 3 :=
  ResolutionProducts.natCubicCocycle (k := k) (resolution k R M) (cubicMap k R M p)
    (cubicMap_comm k R M p hp)

theorem cubicMap_augmentation :
    cubicMap k R M p 0 ≫ (resolution k R M).π.f 0 =
      ModuleCat.ofHom (X := moduleObject k R M 4) (Y := moduleObject k R M 0)
        (cochain3 k R M p) := by
  change cubicMap k R M p 0 ≫ (augmentation k R M).f 0 = _
  rw [augmentation_zero]
  apply ModuleCat.hom_ext
  exact suffixComparison_augmentation k R M p

variable [HasDerivedCategory (ModuleCat.{u} R)]

theorem cubicCocycle_endExt :
    ResolutionProducts.endExt (resolution k R M) (cubicCocycle k R M p hp) =
      extClass3 k R M p hp := by
  have h := ResolutionProducts.natCubic_endExt_eq (k := k) (resolution k R M)
    (cubicMap k R M p) (cubicMap_comm k R M p hp)
  simp only [cubicMap_augmentation] at h
  convert! h using 1

end ArExplicit.ModuleBar

end

end OAI
