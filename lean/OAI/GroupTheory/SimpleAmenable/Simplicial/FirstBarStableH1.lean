import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.FirstBarComponentsFinite
import OAI.GroupTheory.SimpleAmenable.Homology.ChainPositiveCokernel

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite AlgebraicTopology
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
noncomputable def linearStable : (homologyRow (C:=C) 1).X 1 ⟶ ComponentStable.object (C:=C) 1 :=
  SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1
instance linearStable_epi : Epi (linearStable (C:=C)) := by
  dsimp only [linearStable]
  exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _
    (NerveHomotopy.homologyMap_isIso (oneEval (C:=C)) Z 1))
    (ComponentStable.epi_toStable 1)
omit [SymmetricCategory C] in
lemma rowOne_d10 : (homologyRow (C:=C) 1).d 1 0=0 := by
  have hz:IsZero ((homologyRow (C:=C) 1).X 0) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply hom_ext
    intro p i
    exact Fin.elim0 i
  exact hz.eq_zero_of_tgt _
lemma linearStable_d : (homologyRow (C:=C) 1).d 2 1 ≫ linearStable=0 := by
  apply hom_ext
  intro p i
  change Fin 2 → Skeleton C at p
  change Fin 2 at i
  rw [SimplicialFirstFinite.d21]
  dsimp only [linearStable]
  simp only [Preadditive.add_comp,Preadditive.sub_comp]
  change primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 -
    primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 +
    primitive p i ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 = 0
  rw [binary_primitive_middle_stable]
  fin_cases i
  all_goals dsimp only at *
  · change primitive p 0 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 -
    ComponentStable.inclusion (p 0) 1 ≫ ComponentStable.toStable 1 +
    primitive p 0 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 = 0
    rw [binary_primitive_zero_other_assoc,zero_comp,
      binary_primitive_last_assoc]
    abel
  · change primitive p 1 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 -
    ComponentStable.inclusion (p 1) 1 ≫ ComponentStable.toStable 1 +
    primitive p 1 ≫ SSet.homologyMap (nerveMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)) Z 1 ≫
      SSet.homologyMap (nerveMap oneEval) Z 1 ≫ ComponentStable.toStable 1 = 0
    rw [binary_primitive_zero_assoc,
      binary_primitive_last_other_assoc,zero_comp]
    abel
noncomputable def stableOneπ : (homologyRow (C:=C) 1).homology 1 ⟶ ComponentStable.object (C:=C) 1 :=
  ChainComplex.positiveDesc _ 0 rowOne_d10 linearStable linearStable_d
instance stableOneπ_epi : Epi (stableOneπ (C:=C)) := by
  have hh:ChainComplex.positiveπ _ 0 rowOne_d10 ≫ stableOneπ (C:=C)=linearStable :=
    ChainComplex.positiveπ_desc _ 0 rowOne_d10 linearStable linearStable_d
  have :Epi (ChainComplex.positiveπ _ 0 rowOne_d10 ≫ stableOneπ (C:=C)):=by rw [hh]; infer_instance
  exact epi_of_epi (ChainComplex.positiveπ _ 0 rowOne_d10) _
lemma stableH1_finite
    [Module.Finite ℤ ((bar (C:=C)).homology Z 1 : A)]
    [Module.Finite ℤ ((bar (C:=C)).homology Z 2 : A)] :
    Module.Finite ℤ (ComponentStable.object (C:=C) 1 : A) := by
  have :=first_row_one_finite (C:=C)
  exact Module.Finite.of_surjective (stableOneπ (C:=C)).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
end MarkedH1

end OAI
