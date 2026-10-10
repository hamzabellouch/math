import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.Id

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram NerveHomology
variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_1_0 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 5)).toOrderHom) 1 =
      primitive ![b,d,e] 0 := by
  have hh := face_recognition ![a,b,d,e] 1 0 ![b,d,e] 0 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d,e] 0 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d,e] 0 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d,e] 0 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_1_1 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate a b (a*b) rfl) 1 ≫ primitive ![(a*b),d,e] 0 := by
  have hh := face_recognition ![a,b,d,e] 1 1 ![(a*b),d,e] 0 (translate a b (a*b) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (pairAt (0:Fin 4) (1:Fin 4)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d,e] 0 1 (by decide)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  exact hh
@[reassoc] lemma face_4_1_2 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate d b (b*d) (mul_comm _ _)) 1 ≫ primitive ![a,(b*d),e] 1 := by
  have hh := face_recognition ![a,b,d,e] 1 2 ![a,(b*d),e] 1 (translate d b (b*d) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (pairAt (1:Fin 4) (2:Fin 4)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d,e] 1 2 (by decide) ≪≫
        Functor.isoWhiskerLeft (property b).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr d)).symm
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_1_3 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,(d*e)] 1 := by
  have hh := face_recognition ![a,b,d,e] 1 3 ![a,b,(d*e)] 1 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,(d*e)] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,(d*e)] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (pairAt (2:Fin 4) (3:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,(d*e)] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 2 3 1 (by decide) (by decide) ≪≫
        (Functor.const (Fiber b)).mapIso (reprMul d e)
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_1_4 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (4:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,d] 1 := by
  have hh := face_recognition ![a,b,d,e] 1 4 ![a,b,d] 1 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,d] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,d] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 1 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b,d] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_2_0 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 5)).toOrderHom) 1 =
      primitive ![b,d,e] 1 := by
  have hh := face_recognition ![a,b,d,e] 2 0 ![b,d,e] 1 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d,e] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d,e] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d,e] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_2_1 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 5)).toOrderHom) 1 =
      primitive ![(a*b),d,e] 1 := by
  have hh := face_recognition ![a,b,d,e] 2 1 ![(a*b),d,e] 1 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (pairAt (0:Fin 4) (1:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d,e] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 0 1 2 (by decide) (by decide) ≪≫
        (Functor.const (Fiber d)).mapIso (reprMul a b)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d,e] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d,e] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_2_2 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate b d (b*d) rfl) 1 ≫ primitive ![a,(b*d),e] 1 := by
  have hh := face_recognition ![a,b,d,e] 2 2 ![a,(b*d),e] 1 (translate b d (b*d) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (pairAt (1:Fin 4) (2:Fin 4)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d,e] 1 2 (by decide)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d),e] 1 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    )
  exact hh
@[reassoc] lemma face_4_2_3 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate e d (d*e) (mul_comm _ _)) 1 ≫ primitive ![a,b,(d*e)] 2 := by
  have hh := face_recognition ![a,b,d,e] 2 3 ![a,b,(d*e)] 2 (translate e d (d*e) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (translate e d (d*e) (mul_comm _ _)) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (translate e d (d*e) (mul_comm _ _)) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (pairAt (2:Fin 4) (3:Fin 4)) ≅
        (translate e d (d*e) (mul_comm _ _)) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d,e] 2 3 (by decide) ≪≫
        Functor.isoWhiskerLeft (property d).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr e)).symm
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_2_4 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (4:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,d] 2 := by
  have hh := face_recognition ![a,b,d,e] 2 4 ![a,b,d] 2 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![a,b,d] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![a,b,d] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 2 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![a,b,d] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_0 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 5)).toOrderHom) 1 =
      primitive ![b,d,e] 2 := by
  have hh := face_recognition ![a,b,d,e] 3 0 ![b,d,e] 2 (𝟭 (Fiber e)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![b,d,e] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![b,d,e] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![b,d,e] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    )
  erw [NerveHomology.id (D:=Fiber e)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_1 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 5)).toOrderHom) 1 =
      primitive ![(a*b),d,e] 2 := by
  have hh := face_recognition ![a,b,d,e] 3 1 ![(a*b),d,e] 2 (𝟭 (Fiber e)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (pairAt (0:Fin 4) (1:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![(a*b),d,e] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 0 1 3 (by decide) (by decide) ≪≫
        (Functor.const (Fiber e)).mapIso (reprMul a b)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![(a*b),d,e] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![(a*b),d,e] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    )
  erw [NerveHomology.id (D:=Fiber e)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_2 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 5)).toOrderHom) 1 =
      primitive ![a,(b*d),e] 2 := by
  have hh := face_recognition ![a,b,d,e] 3 2 ![a,(b*d),e] 2 (𝟭 (Fiber e)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![a,(b*d),e] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (pairAt (1:Fin 4) (2:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![a,(b*d),e] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 1 2 3 (by decide) (by decide) ≪≫
        (Functor.const (Fiber e)).mapIso (reprMul b d)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber e)) ⋙ (wordInclude ![a,(b*d),e] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
    )
  erw [NerveHomology.id (D:=Fiber e)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_3 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate d e (d*e) rfl) 1 ≫ primitive ![a,b,(d*e)] 2 := by
  have hh := face_recognition ![a,b,d,e] 3 3 ![a,b,(d*e)] 2 (translate d e (d*e) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (translate d e (d*e) rfl) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (translate d e (d*e) rfl) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 3 ⋙ (pairAt (2:Fin 4) (3:Fin 4)) ≅
        (translate d e (d*e) rfl) ⋙ (wordInclude ![a,b,(d*e)] 2 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d,e] 2 3 (by decide)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_3_4 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 3 ≫ NerveHomology.map (reindex (SimplexCategory.δ (4:Fin 5)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b,d,e] 3 4 (fun j=>repr (![a,b,d] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (0:Fin 4)) ≅ (Functor.const (Fiber e)).obj (repr a)
    exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (1:Fin 4)) ≅ (Functor.const (Fiber e)).obj (repr b)
    exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 3 ⋙ (Pi.eval _ (2:Fin 4)) ≅ (Functor.const (Fiber e)).obj (repr d)
    exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
end MarkedH1

end OAI
