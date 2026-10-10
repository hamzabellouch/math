import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedFreeColimit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.RepCofiber

namespace OAI

/-! # Normalized syzygies preserve sequential coefficient colimits -/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]
namespace SequentialRepresentationDiagram.ColimitCocone
variable {D : SequentialRepresentationDiagram G} {A : Rep.{0} ℤ G}
  (c : D.ColimitCocone A)

def normalizedSyzygy : (D.mapFunctor normalizedSyzygyFunctor).ColimitCocone
    (PolycyclicRecognition.normalizedSyzygy A) where
  ι i := normalizedSyzygyMap (c.ι i)
  comm i j h := by
    change normalizedSyzygyFunctor.map (D.map i j h) ≫ normalizedSyzygyFunctor.map (c.ι j) =
      normalizedSyzygyFunctor.map (c.ι i)
    rw [← CategoryTheory.Functor.map_comp, c.comm]
  surj x := by
    obtain ⟨i, y, hy⟩ := c.normalizedFree.surj
      ((kernel.ι (normalizedFreeAugmentation A)).hom x)
    change normalizedFreeRepresentation (D.obj i) at y
    change (normalizedFreeMap (c.ι i)).hom y =
      (kernel.ι (normalizedFreeAugmentation A)).hom x at hy
    have h0 : (c.ι i).hom ((normalizedFreeAugmentation (D.obj i)).hom y) = 0 := by
      have he := ConcreteCategory.congr_hom (normalizedFreeAugmentation_natural (c.ι i)) y
      change (normalizedFreeAugmentation A).hom ((normalizedFreeMap (c.ι i)).hom y) = _ at he
      rw [hy] at he
      have hk := ConcreteCategory.congr_hom (kernel.condition (normalizedFreeAugmentation A)) x
      exact he.symm.trans hk
    obtain ⟨j, hij, hj⟩ := c.zero_exact i ((normalizedFreeAugmentation (D.obj i)).hom y) h0
    let yj := (normalizedFreeMap (D.map i j hij)).hom y
    have h0j : (normalizedFreeAugmentation (D.obj j)).hom yj = 0 := by
      have he := ConcreteCategory.congr_hom (normalizedFreeAugmentation_natural (D.map i j hij)) y
      exact he.trans hj
    obtain ⟨z, hz⟩ := (rep_shortComplex_exact_iff
      (normalizedSyzygySequence (D.obj j))).mp
        (normalizedSyzygySequence_shortExact (D.obj j)).exact yj h0j
    change PolycyclicRecognition.normalizedSyzygy (D.obj j) at z
    change (kernel.ι (normalizedFreeAugmentation (D.obj j))).hom z = yj at hz
    refine ⟨j, z, ?_⟩
    apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation A))).mp inferInstance
    have he := ConcreteCategory.congr_hom (normalizedSyzygyMap_ι (c.ι j)) z
    change (kernel.ι (normalizedFreeAugmentation A)).hom
      ((normalizedSyzygyMap (c.ι j)).hom z) =
        (normalizedFreeMap (c.ι j)).hom ((kernel.ι (normalizedFreeAugmentation (D.obj j))).hom z) at he
    rw [hz] at he
    have hc : (normalizedFreeMap (c.ι j)).hom yj = (normalizedFreeMap (c.ι i)).hom y := by
      change (normalizedFreeMap (D.map i j hij) ≫ normalizedFreeMap (c.ι j)).hom y = _
      rw [← normalizedFreeMap_comp, c.comm]
    exact he.trans (hc.trans hy)
  zero_exact i x hx := by
    change PolycyclicRecognition.normalizedSyzygy (D.obj i) at x
    change (normalizedSyzygyMap (c.ι i)).hom x = 0 at hx
    have he := ConcreteCategory.congr_hom (normalizedSyzygyMap_ι (c.ι i)) x
    change (kernel.ι (normalizedFreeAugmentation A)).hom ((normalizedSyzygyMap (c.ι i)).hom x) =
      (normalizedFreeMap (c.ι i)).hom ((kernel.ι (normalizedFreeAugmentation (D.obj i))).hom x) at he
    rw [hx, map_zero] at he
    obtain ⟨j, hij, hj⟩ := c.normalizedFree.zero_exact i
      ((kernel.ι (normalizedFreeAugmentation (D.obj i))).hom x) he.symm
    refine ⟨j, hij, ?_⟩
    change (normalizedSyzygyMap (D.map i j hij)).hom x = 0
    apply (Rep.mono_iff_injective (kernel.ι (normalizedFreeAugmentation (D.obj j)))).mp inferInstance
    have hf := ConcreteCategory.congr_hom (normalizedSyzygyMap_ι (D.map i j hij)) x
    change (kernel.ι (normalizedFreeAugmentation (D.obj j))).hom
      ((normalizedSyzygyMap (D.map i j hij)).hom x) =
      (normalizedFreeMap (D.map i j hij)).hom
        ((kernel.ι (normalizedFreeAugmentation (D.obj i))).hom x) at hf
    exact (hf.trans hj).trans (map_zero
      (kernel.ι (normalizedFreeAugmentation (D.obj j))).hom).symm

def iteratedNormalizedSyzygy (n : ℕ) :
    (D.mapFunctor (PolycyclicRecognition.iteratedNormalizedSyzygy n)).ColimitCocone
      ((PolycyclicRecognition.iteratedNormalizedSyzygy n).obj A) := by
  induction n with
  | zero => exact c
  | succ n ih => exact ih.normalizedSyzygy

@[simp]
theorem iteratedNormalizedSyzygy_ι (n i : ℕ) :
    (c.iteratedNormalizedSyzygy n).ι i =
      (PolycyclicRecognition.iteratedNormalizedSyzygy n).map (c.ι i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change normalizedSyzygyMap ((c.iteratedNormalizedSyzygy n).ι i) =
      normalizedSyzygyMap ((PolycyclicRecognition.iteratedNormalizedSyzygy n).map (c.ι i))
    exact congrArg normalizedSyzygyMap ih

end SequentialRepresentationDiagram.ColimitCocone
end PolycyclicRecognition

end

end OAI
