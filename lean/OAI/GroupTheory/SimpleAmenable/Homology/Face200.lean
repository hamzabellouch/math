import Mathlib
import OAI.GroupTheory.SimpleAmenable.Simplicial.Id

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram NerveHomology

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_0_0 (a b:Skeleton C) :
    primitive ![a,b] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b] 0 0 (fun j=>repr (![b] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b] 0 ⋙ (Pi.eval _ (1:Fin 2)) ≅ (Functor.const (Fiber a)).obj (repr b)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
@[reassoc] lemma face_2_0_1 (a b:Skeleton C) :
    primitive ![a,b] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom) 1 =
      NerveHomology.map (translate b a (a*b) (mul_comm _ _)) 1 ≫ primitive ![(a*b)] 0 := by
  have hh := face_recognition ![a,b] 0 1 ![(a*b)] 0 (translate b a (a*b) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b] 0 ⋙ (pairAt (0:Fin 2) (1:Fin 2)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b)] 0 ⋙ Pi.eval _ (0:Fin 1))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b] 0 1 (by decide) ≪≫
        Functor.isoWhiskerLeft (property a).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr b)).symm
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_0_2 (a b:Skeleton C) :
    primitive ![a,b] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom) 1 =
      primitive ![a] 0 := by
  have hh := face_recognition ![a,b] 0 2 ![a] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b] 0 ⋙ (Pi.eval _ (0:Fin 2)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a] 0 ⋙ Pi.eval _ (0:Fin 1))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_1_0 (a b:Skeleton C) :
    primitive ![a,b] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 3)).toOrderHom) 1 =
      primitive ![b] 0 := by
  have hh := face_recognition ![a,b] 1 0 ![b] 0 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b] 1 ⋙ (Pi.eval _ (1:Fin 2)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b] 0 ⋙ Pi.eval _ (0:Fin 1))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_1_1 (a b:Skeleton C) :
    primitive ![a,b] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 3)).toOrderHom) 1 =
      NerveHomology.map (translate a b (a*b) rfl) 1 ≫ primitive ![(a*b)] 0 := by
  have hh := face_recognition ![a,b] 1 1 ![(a*b)] 0 (translate a b (a*b) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b] 1 ⋙ (pairAt (0:Fin 2) (1:Fin 2)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b)] 0 ⋙ Pi.eval _ (0:Fin 1))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b] 0 1 (by decide)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_2_1_2 (a b:Skeleton C) :
    primitive ![a,b] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 3)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b] 1 2 (fun j=>repr (![a] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b] 1 ⋙ (Pi.eval _ (0:Fin 2)) ≅ (Functor.const (Fiber b)).obj (repr a)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_0_0 (a b d:Skeleton C) :
    primitive ![a,b,d] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 4)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b,d] 0 0 (fun j=>repr (![b,d] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (1:Fin 3)) ≅ (Functor.const (Fiber a)).obj (repr b)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (2:Fin 3)) ≅ (Functor.const (Fiber a)).obj (repr d)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
@[reassoc] lemma face_3_0_1 (a b d:Skeleton C) :
    primitive ![a,b,d] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 4)).toOrderHom) 1 =
      NerveHomology.map (translate b a (a*b) (mul_comm _ _)) 1 ≫ primitive ![(a*b),d] 0 := by
  have hh := face_recognition ![a,b,d] 0 1 ![(a*b),d] 0 (translate b a (a*b) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (pairAt (0:Fin 3) (1:Fin 3)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d] 0 ⋙ Pi.eval _ (0:Fin 2))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d] 0 1 (by decide) ≪≫
        Functor.isoWhiskerLeft (property a).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr b)).symm
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d] 0 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_0_2 (a b d:Skeleton C) :
    primitive ![a,b,d] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 4)).toOrderHom) 1 =
      primitive ![a,(b*d)] 0 := by
  have hh := face_recognition ![a,b,d] 0 2 ![a,(b*d)] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d)] 0 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (pairAt (1:Fin 3) (2:Fin 3)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d)] 0 ⋙ Pi.eval _ (1:Fin 2))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d] 1 2 0 (by decide) (by decide) ≪≫
        (Functor.const (Fiber a)).mapIso (reprMul b d)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_0_3 (a b d:Skeleton C) :
    primitive ![a,b,d] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 4)).toOrderHom) 1 =
      primitive ![a,b] 0 := by
  have hh := face_recognition ![a,b,d] 0 3 ![a,b] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b] 0 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 0 ⋙ (Pi.eval _ (1:Fin 3)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b] 0 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_1_0 (a b d:Skeleton C) :
    primitive ![a,b,d] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 4)).toOrderHom) 1 =
      primitive ![b,d] 0 := by
  have hh := face_recognition ![a,b,d] 1 0 ![b,d] 0 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (1:Fin 3)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d] 0 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![b,d] 0 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_1_1 (a b d:Skeleton C) :
    primitive ![a,b,d] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 4)).toOrderHom) 1 =
      NerveHomology.map (translate a b (a*b) rfl) 1 ≫ primitive ![(a*b),d] 0 := by
  have hh := face_recognition ![a,b,d] 1 1 ![(a*b),d] 0 (translate a b (a*b) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (pairAt (0:Fin 3) (1:Fin 3)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d] 0 ⋙ Pi.eval _ (0:Fin 2))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d] 0 1 (by decide)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (translate a b (a*b) rfl) ⋙ (wordInclude ![(a*b),d] 0 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  exact hh
@[reassoc] lemma face_3_1_2 (a b d:Skeleton C) :
    primitive ![a,b,d] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 4)).toOrderHom) 1 =
      NerveHomology.map (translate d b (b*d) (mul_comm _ _)) 1 ≫ primitive ![a,(b*d)] 1 := by
  have hh := face_recognition ![a,b,d] 1 2 ![a,(b*d)] 1 (translate d b (b*d) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d)] 1 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (pairAt (1:Fin 3) (2:Fin 3)) ≅
        (translate d b (b*d) (mul_comm _ _)) ⋙ (wordInclude ![a,(b*d)] 1 ⋙ Pi.eval _ (1:Fin 2))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d] 1 2 (by decide) ≪≫
        Functor.isoWhiskerLeft (property b).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr d)).symm
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_1_3 (a b d:Skeleton C) :
    primitive ![a,b,d] 1 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 4)).toOrderHom) 1 =
      primitive ![a,b] 1 := by
  have hh := face_recognition ![a,b,d] 1 3 ![a,b] 1 (𝟭 (Fiber b)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b] 1 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 1 ⋙ (Pi.eval _ (1:Fin 3)) ≅
        (𝟭 (Fiber b)) ⋙ (wordInclude ![a,b] 1 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber b)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_2_0 (a b d:Skeleton C) :
    primitive ![a,b,d] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 4)).toOrderHom) 1 =
      primitive ![b,d] 1 := by
  have hh := face_recognition ![a,b,d] 2 0 ![b,d] 1 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (1:Fin 3)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d] 1 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![b,d] 1 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_2_1 (a b d:Skeleton C) :
    primitive ![a,b,d] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 4)).toOrderHom) 1 =
      primitive ![(a*b),d] 1 := by
  have hh := face_recognition ![a,b,d] 2 1 ![(a*b),d] 1 (𝟭 (Fiber d)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (pairAt (0:Fin 3) (1:Fin 3)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d] 1 ⋙ Pi.eval _ (0:Fin 2))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d] 0 1 2 (by decide) (by decide) ≪≫
        (Functor.const (Fiber d)).mapIso (reprMul a b)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (2:Fin 3)) ≅
        (𝟭 (Fiber d)) ⋙ (wordInclude ![(a*b),d] 1 ⋙ Pi.eval _ (1:Fin 2))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber d)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_2_2 (a b d:Skeleton C) :
    primitive ![a,b,d] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 4)).toOrderHom) 1 =
      NerveHomology.map (translate b d (b*d) rfl) 1 ≫ primitive ![a,(b*d)] 1 := by
  have hh := face_recognition ![a,b,d] 2 2 ![a,(b*d)] 1 (translate b d (b*d) rfl) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (0:Fin 3)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d)] 1 ⋙ Pi.eval _ (0:Fin 2))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d] 2 ⋙ (pairAt (1:Fin 3) (2:Fin 3)) ≅
        (translate b d (b*d) rfl) ⋙ (wordInclude ![a,(b*d)] 1 ⋙ Pi.eval _ (1:Fin 2))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_right ![a,b,d] 1 2 (by decide)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_3_2_3 (a b d:Skeleton C) :
    primitive ![a,b,d] 2 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 4)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b,d] 2 3 (fun j=>repr (![a,b] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (0:Fin 3)) ≅ (Functor.const (Fiber d)).obj (repr a)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d] 2 ⋙ (Pi.eval _ (1:Fin 3)) ≅ (Functor.const (Fiber d)).obj (repr b)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_0_0 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (0:Fin 5)).toOrderHom) 1 =
      0 := by
  apply face_recognition_const ![a,b,d,e] 0 0 (fun j=>repr (![b,d,e] j))
  intro j
  apply Classical.choice
  fin_cases j
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (1:Fin 4)) ≅ (Functor.const (Fiber a)).obj (repr b)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (2:Fin 4)) ≅ (Functor.const (Fiber a)).obj (repr d)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
  · refine ⟨?_⟩
    change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (3:Fin 4)) ≅ (Functor.const (Fiber a)).obj (repr e)
    exact eqToIso (by rw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
@[reassoc] lemma face_4_0_1 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (1:Fin 5)).toOrderHom) 1 =
      NerveHomology.map (translate b a (a*b) (mul_comm _ _)) 1 ≫ primitive ![(a*b),d,e] 0 := by
  have hh := face_recognition ![a,b,d,e] 0 1 ![(a*b),d,e] 0 (translate b a (a*b) (mul_comm _ _)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (pairAt (0:Fin 4) (1:Fin 4)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (0:Fin 3))
      erw [wordInclude_proj,ite_eq_left rfl]
      exact wordPair_left ![a,b,d,e] 0 1 (by decide) ≪≫
        Functor.isoWhiskerLeft (property a).ι
          (BraidedCategory.tensorLeftIsoTensorRight (repr b)).symm
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (1:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (translate b a (a*b) (mul_comm _ _)) ⋙ (wordInclude ![(a*b),d,e] 0 ⋙ Pi.eval _ (2:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  exact hh
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_0_2 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (2:Fin 5)).toOrderHom) 1 =
      primitive ![a,(b*d),e] 0 := by
  have hh := face_recognition ![a,b,d,e] 0 2 ![a,(b*d),e] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d),e] 0 ⋙ Pi.eval _ (0:Fin 3))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (pairAt (1:Fin 4) (2:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d),e] 0 ⋙ Pi.eval _ (1:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 1 2 0 (by decide) (by decide) ≪≫
        (Functor.const (Fiber a)).mapIso (reprMul b d)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (3:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,(b*d),e] 0 ⋙ Pi.eval _ (2:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_0_3 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (3:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,(d*e)] 0 := by
  have hh := face_recognition ![a,b,d,e] 0 3 ![a,b,(d*e)] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,(d*e)] 0 ⋙ Pi.eval _ (0:Fin 3))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,(d*e)] 0 ⋙ Pi.eval _ (1:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (pairAt (2:Fin 4) (3:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,(d*e)] 0 ⋙ Pi.eval _ (2:Fin 3))
      erw [wordInclude_proj,ite_eq_right (by decide)]
      exact wordPair_other ![a,b,d,e] 2 3 0 (by decide) (by decide) ≪≫
        (Functor.const (Fiber a)).mapIso (reprMul d e)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)
omit [SymmetricCategory C] in
@[reassoc] lemma face_4_0_4 (a b d e:Skeleton C) :
    primitive ![a,b,d,e] 0 ≫ NerveHomology.map (reindex (SimplexCategory.δ (4:Fin 5)).toOrderHom) 1 =
      primitive ![a,b,d] 0 := by
  have hh := face_recognition ![a,b,d,e] 0 4 ![a,b,d] 0 (𝟭 (Fiber a)) (by
    intro j
    apply Classical.choice
    fin_cases j
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (0:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,d] 0 ⋙ Pi.eval _ (0:Fin 3))
      rw [wordInclude_proj,ite_eq_left rfl]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_left rfl]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (1:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,d] 0 ⋙ Pi.eval _ (1:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    · refine ⟨?_⟩
      change wordInclude ![a,b,d,e] 0 ⋙ (Pi.eval _ (2:Fin 4)) ≅
        (𝟭 (Fiber a)) ⋙ (wordInclude ![a,b,d] 0 ⋙ Pi.eval _ (2:Fin 3))
      rw [wordInclude_proj,ite_eq_right (by decide)]
      exact eqToIso (by erw [wordInclude_proj,ite_eq_right (by decide)]; rfl)
    )
  erw [NerveHomology.id (D:=Fiber a)] at hh
  exact hh.trans (Category.id_comp _)

end MarkedH1
end

end OAI
