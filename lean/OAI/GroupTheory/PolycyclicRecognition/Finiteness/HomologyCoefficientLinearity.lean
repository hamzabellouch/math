import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

namespace OAI

/-! # Integral linearity in the coefficient map -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {k : Type} [CommRing k] {G H : Type} [Group G] [Group H]

theorem chainsMap_coefficient_zsmul (f : G →* H) {A : Rep k G} {B : Rep k H}
    (φ : A ⟶ Rep.res f B) (r : ℤ) :
    groupHomology.chainsMap f (r • φ) = r • groupHomology.chainsMap f φ := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext
  intro v
  change (groupHomology.chainsMap f (r • φ)).f i (Finsupp.single x v) =
    r • (groupHomology.chainsMap f φ).f i (Finsupp.single x v)
  rw [groupHomology.chainsMap_f_single, groupHomology.chainsMap_f_single]
  change Finsupp.single (f ∘ x) (r • φ.hom v) = r • Finsupp.single (f ∘ x) (φ.hom v)
  exact map_zsmul (Finsupp.lsingle (R := k) (M := B.V) (f ∘ x)).toAddMonoidHom r (φ.hom v)

theorem homologyMap_coefficient_zsmul (f : G →* H) {A : Rep k G} {B : Rep k H}
    (φ : A ⟶ Rep.res f B) (r : ℤ) (i : ℕ) :
    groupHomology.map f (r • φ) i = r • groupHomology.map f φ i := by
  change homologyMap (groupHomology.chainsMap f (r • φ)) i = _
  rw [chainsMap_coefficient_zsmul]
  exact (homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).map_zsmul

end PolycyclicRecognition

end

end OAI
