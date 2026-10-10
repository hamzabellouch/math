import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.NestedPosReindex
import OAI.GroupTheory.SimpleAmenable.Simplicial.FinitePowerGeneral
import OAI.GroupTheory.SimpleAmenable.Simplicial.LowerBarComposition

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram
open BarFinitePower SimplicialDiagonal StageProductColimit

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
lemma outer_project (i:Fin 2) : outerFunctor (C:=C) ⋙ project _ i = reindex (outerOrder i) := rfl
lemma outer_project_ε (i:Fin 2) : Functor.LaxMonoidal.ε (outerFunctor (C:=C) ⋙ project _ i) = 𝟙 _ := by
  rw [Functor.LaxMonoidal.comp_ε]
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp
lemma outer_project_μ (i:Fin 2) (A B:Diagram C (Fin 3)) :
    Functor.LaxMonoidal.μ (outerFunctor (C:=C) ⋙ project _ i) A B = 𝟙 _ := by
  rw [Functor.LaxMonoidal.comp_μ]
  change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
  simp
instance outer_project_monoidal (i:Fin 2) : NatTrans.IsMonoidal (eqToHom (outer_project (C:=C) i)) where
  unit := by
    rw [outer_project_ε, reindex_ε]
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    simp
  tensor A B := by
    rw [outer_project_μ,reindex_μ]
    change 𝟙 _ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
    simp
variable {D:Type} [Groupoid.{0} D] [MonoidalCategory D] [SymmetricCategory D]
omit [SymmetricCategory C] [SymmetricCategory D] in
lemma barMap_congr {F G:C⥤D} [hF:F.Monoidal] [hG:G.Monoidal] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) : barMap F=barMap G := by
  have hm := monoidal_congr e h
  cases e
  have hh : hF=hG := eq_of_heq hm
  cases hh
  rfl
lemma bar₂Map_congr {F G:C⥤D} [hF:F.Braided] [hG:G.Braided] (e:F=G)
    (h:NatTrans.IsMonoidal (eqToHom e)) : bar₂Map F=bar₂Map G := by
  have hm := monoidal_congr e h
  cases e
  have hh : hF.toMonoidal=hG.toMonoidal := eq_of_heq hm
  have hb : hF = hG := Functor.Braided.ext
    (congrArg (fun t : F.Monoidal => t.ε) hh)
    (congrArg (fun t : F.Monoidal => t.μ) hh)
    (congrArg (fun t : F.Monoidal => t.η) hh)
    (congrArg (fun t : F.Monoidal => t.δ) hh)
  cases hb
  rfl
lemma rows₂_segal : segalTwo (rows₂ (C:=C)) = barMap (outerFunctor (C:=C)) ≫
    singlePowerComparison (Fin 2) ≫ (powerTwoIso _).hom := by
  ext n x
  · change (barMap (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)).app n x =
      (barMap (outerFunctor (C:=C)) ≫ barMap (project (Fin 2) (0:Fin 2))).app n x
    rw [←barMap_comp,barMap_congr (outer_project _) inferInstance]
    rfl
  · change (barMap (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)).app n x =
      (barMap (outerFunctor (C:=C)) ≫ barMap (project (Fin 2) (1:Fin 2))).app n x
    rw [←barMap_comp,barMap_congr (outer_project _) inferInstance]
    rfl
lemma rows₃_segal : segalTwo (rows₃ (C:=C)) = bar₂Map (outerFunctor (C:=C)) ≫
    doublePowerComparison (Fin 2) ≫ (powerTwoIso _).hom := by
  ext n x
  · change (bar₂Map (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom)).app n x =
      (bar₂Map (outerFunctor (C:=C)) ≫ bar₂Map (project (Fin 2) (0:Fin 2))).app n x
    rw [←bar₂Map_comp,bar₂Map_congr (outer_project _) inferInstance]
    rfl
  · change (bar₂Map (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom)).app n x =
      (bar₂Map (outerFunctor (C:=C)) ≫ bar₂Map (project (Fin 2) (1:Fin 2))).app n x
    rw [←bar₂Map_comp,bar₂Map_congr (outer_project _) inferInstance]
    rfl
lemma rows₂_segal_homology_isIso (q:ℕ) : IsIso (SSet.homologyMap (segalTwo (rows₂ (C:=C))) DiagonalResolution.Z q) := by
  rw [rows₂_segal]
  change IsIso (SSet.homologyMap (barMap (outerFunctor (C:=C)) ≫
    singlePowerComparison (Fin 2) ≫ (powerTwoIso _).hom) DiagonalResolution.Z q)
  rw [SSet.homologyMap_comp,SSet.homologyMap_comp]
  have := barMap_homology_isIso (outerFunctor (C:=C)) q
  have := singlePowerComparison_homology_isIso (C:=Diagram C (Fin 2)) (Fin 2) q
  infer_instance
lemma rows₃_segal_homology_isIso (q:ℕ) : IsIso (SSet.homologyMap (segalTwo (rows₃ (C:=C))) DiagonalResolution.Z q) := by
  rw [rows₃_segal]
  change IsIso (SSet.homologyMap (bar₂Map (outerFunctor (C:=C)) ≫
    doublePowerComparison (Fin 2) ≫ (powerTwoIso _).hom) DiagonalResolution.Z q)
  rw [SSet.homologyMap_comp,SSet.homologyMap_comp]
  have := bar₂Map_homology_isIso (outerFunctor (C:=C)) q
  have := doublePowerComparison_homology_isIso (C:=Diagram C (Fin 2)) (Fin 2) q
  infer_instance
end IntervalBar.Diagram

end

end OAI
