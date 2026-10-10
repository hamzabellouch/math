import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.MarkedSigns
import OAI.GroupTheory.SimpleAmenable.Homology.Face200
import OAI.GroupTheory.SimpleAmenable.Homology.Face410
import OAI.GroupTheory.SimpleAmenable.Simplicial.FirstBarComponentsFinite

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram RegularLabels RegularCoordinates MonoidNerveCoordinates RegularFiniteFaces

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
noncomputable def T (r p s:Skeleton C) (h:r*p=s) : H p ⟶ H s := NerveHomology.map (translate r p s h) 1
noncomputable def R (n:ℕ) (k:Fin (n+2)) : (homologyRow (C:=C) 1).X (n+1) ⟶ (homologyRow (C:=C) 1).X n :=
  NerveHomology.map (reindex (SimplexCategory.δ k).toOrderHom) 1
noncomputable def P10 (a:Skeleton C) : H a ⟶ (homologyRow (C:=C) 1).X 1 := primitive ![a] 0
noncomputable def P20 (a b:Skeleton C) : H a ⟶ (homologyRow (C:=C) 1).X 2 := primitive ![a,b] 0
noncomputable def P21 (a b:Skeleton C) : H b ⟶ (homologyRow (C:=C) 1).X 2 := primitive ![a,b] 1
noncomputable def P30 (a b d:Skeleton C) : H a ⟶ (homologyRow (C:=C) 1).X 3 := primitive ![a,b,d] 0
noncomputable def P31 (a b d:Skeleton C) : H b ⟶ (homologyRow (C:=C) 1).X 3 := primitive ![a,b,d] 1
noncomputable def P32 (a b d:Skeleton C) : H d ⟶ (homologyRow (C:=C) 1).X 3 := primitive ![a,b,d] 2
noncomputable def P40 (a b d e:Skeleton C) : H a ⟶ (homologyRow (C:=C) 1).X 4 := primitive ![a,b,d,e] 0
noncomputable def P41 (a b d e:Skeleton C) : H b ⟶ (homologyRow (C:=C) 1).X 4 := primitive ![a,b,d,e] 1
noncomputable def P42 (a b d e:Skeleton C) : H d ⟶ (homologyRow (C:=C) 1).X 4 := primitive ![a,b,d,e] 2
noncomputable def P43 (a b d e:Skeleton C) : H e ⟶ (homologyRow (C:=C) 1).X 4 := primitive ![a,b,d,e] 3
@[reassoc] lemma Pface_2_0_0 (a b:Skeleton C) :
    P20 a b ≫ R 1 0 = 0 :=
  face_2_0_0 a b
@[reassoc] lemma Pface_2_0_1 [SymmetricCategory C] (a b:Skeleton C) :
    P20 a b ≫ R 1 1 = T b a (a*b) (mul_comm _ _) ≫ P10 (a*b) :=
  face_2_0_1 a b
@[reassoc] lemma Pface_2_0_2 (a b:Skeleton C) :
    P20 a b ≫ R 1 2 = P10 a :=
  face_2_0_2 a b
@[reassoc] lemma Pface_2_1_0 (a b:Skeleton C) :
    P21 a b ≫ R 1 0 = P10 b :=
  face_2_1_0 a b
@[reassoc] lemma Pface_2_1_1 (a b:Skeleton C) :
    P21 a b ≫ R 1 1 = T a b (a*b) rfl ≫ P10 (a*b) :=
  face_2_1_1 a b
@[reassoc] lemma Pface_2_1_2 (a b:Skeleton C) :
    P21 a b ≫ R 1 2 = 0 :=
  face_2_1_2 a b
@[reassoc] lemma Pface_3_0_0 (a b d:Skeleton C) :
    P30 a b d ≫ R 2 0 = 0 :=
  face_3_0_0 a b d
@[reassoc] lemma Pface_3_0_1 [SymmetricCategory C] (a b d:Skeleton C) :
    P30 a b d ≫ R 2 1 = T b a (a*b) (mul_comm _ _) ≫ P20 (a*b) d :=
  face_3_0_1 a b d
@[reassoc] lemma Pface_3_0_2 (a b d:Skeleton C) :
    P30 a b d ≫ R 2 2 = P20 a (b*d) :=
  face_3_0_2 a b d
@[reassoc] lemma Pface_3_0_3 (a b d:Skeleton C) :
    P30 a b d ≫ R 2 3 = P20 a b :=
  face_3_0_3 a b d
@[reassoc] lemma Pface_3_1_0 (a b d:Skeleton C) :
    P31 a b d ≫ R 2 0 = P20 b d :=
  face_3_1_0 a b d
@[reassoc] lemma Pface_3_1_1 (a b d:Skeleton C) :
    P31 a b d ≫ R 2 1 = T a b (a*b) rfl ≫ P20 (a*b) d :=
  face_3_1_1 a b d
@[reassoc] lemma Pface_3_1_2 [SymmetricCategory C] (a b d:Skeleton C) :
    P31 a b d ≫ R 2 2 = T d b (b*d) (mul_comm _ _) ≫ P21 a (b*d) :=
  face_3_1_2 a b d
@[reassoc] lemma Pface_3_1_3 (a b d:Skeleton C) :
    P31 a b d ≫ R 2 3 = P21 a b :=
  face_3_1_3 a b d
@[reassoc] lemma Pface_3_2_0 (a b d:Skeleton C) :
    P32 a b d ≫ R 2 0 = P21 b d :=
  face_3_2_0 a b d
@[reassoc] lemma Pface_3_2_1 (a b d:Skeleton C) :
    P32 a b d ≫ R 2 1 = P21 (a*b) d :=
  face_3_2_1 a b d
@[reassoc] lemma Pface_3_2_2 (a b d:Skeleton C) :
    P32 a b d ≫ R 2 2 = T b d (b*d) rfl ≫ P21 a (b*d) :=
  face_3_2_2 a b d
@[reassoc] lemma Pface_3_2_3 (a b d:Skeleton C) :
    P32 a b d ≫ R 2 3 = 0 :=
  face_3_2_3 a b d
@[reassoc] lemma Pface_4_0_0 (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 0 = 0 :=
  face_4_0_0 a b d e
@[reassoc] lemma Pface_4_0_1 [SymmetricCategory C] (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 1 = T b a (a*b) (mul_comm _ _) ≫ P30 (a*b) d e :=
  face_4_0_1 a b d e
@[reassoc] lemma Pface_4_0_2 (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 2 = P30 a (b*d) e :=
  face_4_0_2 a b d e
@[reassoc] lemma Pface_4_0_3 (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 3 = P30 a b (d*e) :=
  face_4_0_3 a b d e
@[reassoc] lemma Pface_4_0_4 (a b d e:Skeleton C) :
    P40 a b d e ≫ R 3 4 = P30 a b d :=
  face_4_0_4 a b d e
@[reassoc] lemma Pface_4_1_0 (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 0 = P30 b d e :=
  face_4_1_0 a b d e
@[reassoc] lemma Pface_4_1_1 (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 1 = T a b (a*b) rfl ≫ P30 (a*b) d e :=
  face_4_1_1 a b d e
@[reassoc] lemma Pface_4_1_2 [SymmetricCategory C] (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 2 = T d b (b*d) (mul_comm _ _) ≫ P31 a (b*d) e :=
  face_4_1_2 a b d e
@[reassoc] lemma Pface_4_1_3 (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 3 = P31 a b (d*e) :=
  face_4_1_3 a b d e
@[reassoc] lemma Pface_4_1_4 (a b d e:Skeleton C) :
    P41 a b d e ≫ R 3 4 = P31 a b d :=
  face_4_1_4 a b d e
@[reassoc] lemma Pface_4_2_0 (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 0 = P31 b d e :=
  face_4_2_0 a b d e
@[reassoc] lemma Pface_4_2_1 (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 1 = P31 (a*b) d e :=
  face_4_2_1 a b d e
@[reassoc] lemma Pface_4_2_2 (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 2 = T b d (b*d) rfl ≫ P31 a (b*d) e :=
  face_4_2_2 a b d e
@[reassoc] lemma Pface_4_2_3 [SymmetricCategory C] (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 3 = T e d (d*e) (mul_comm _ _) ≫ P32 a b (d*e) :=
  face_4_2_3 a b d e
@[reassoc] lemma Pface_4_2_4 (a b d e:Skeleton C) :
    P42 a b d e ≫ R 3 4 = P32 a b d :=
  face_4_2_4 a b d e
@[reassoc] lemma Pface_4_3_0 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 0 = P32 b d e :=
  face_4_3_0 a b d e
@[reassoc] lemma Pface_4_3_1 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 1 = P32 (a*b) d e :=
  face_4_3_1 a b d e
@[reassoc] lemma Pface_4_3_2 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 2 = P32 a (b*d) e :=
  face_4_3_2 a b d e
@[reassoc] lemma Pface_4_3_3 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 3 = T d e (d*e) rfl ≫ P32 a b (d*e) :=
  face_4_3_3 a b d e
@[reassoc] lemma Pface_4_3_4 (a b d e:Skeleton C) :
    P43 a b d e ≫ R 3 4 = 0 :=
  face_4_3_4 a b d e
end MarkedH1

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram RegularLabels RegularCoordinates MonoidNerveCoordinates RegularFiniteFaces

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C]
@[reassoc] lemma Pd_2_0 [SymmetricCategory C] (a b:Skeleton C) :
    P20 a b ≫ (homologyRow (C:=C) 1).d 2 1 = -(T b a (a*b) (mul_comm _ _) ≫ P10 (a*b)) + (P10 a) := by
  have hd : (homologyRow (C:=C) 1).d 2 1 = (R 1 0) + -(R 1 1) + (R 1 2) := by
    calc
      _ = ∑k:Fin 3,(-1:ℤ)^k.val • R 1 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_2_0_0,Pface_2_0_1,Pface_2_0_2]
  try abel
@[reassoc] lemma Pd_2_1 (a b:Skeleton C) :
    P21 a b ≫ (homologyRow (C:=C) 1).d 2 1 = (P10 b) + -(T a b (a*b) rfl ≫ P10 (a*b)) := by
  have hd : (homologyRow (C:=C) 1).d 2 1 = (R 1 0) + -(R 1 1) + (R 1 2) := by
    calc
      _ = ∑k:Fin 3,(-1:ℤ)^k.val • R 1 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_2_1_0,Pface_2_1_1,Pface_2_1_2]
  try abel
@[reassoc] lemma Pd_3_0 [SymmetricCategory C] (a b d:Skeleton C) :
    P30 a b d ≫ (homologyRow (C:=C) 1).d 3 2 = -(T b a (a*b) (mul_comm _ _) ≫ P20 (a*b) d) + (P20 a (b*d)) + -(P20 a b) := by
  have hd : (homologyRow (C:=C) 1).d 3 2 = (R 2 0) + -(R 2 1) + (R 2 2) + -(R 2 3) := by
    calc
      _ = ∑k:Fin 4,(-1:ℤ)^k.val • R 2 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_3_0_0,Pface_3_0_1,Pface_3_0_2,Pface_3_0_3]
  try abel
@[reassoc] lemma Pd_3_1 [SymmetricCategory C] (a b d:Skeleton C) :
    P31 a b d ≫ (homologyRow (C:=C) 1).d 3 2 = (P20 b d) + -(T a b (a*b) rfl ≫ P20 (a*b) d) + (T d b (b*d) (mul_comm _ _) ≫ P21 a (b*d)) + -(P21 a b) := by
  have hd : (homologyRow (C:=C) 1).d 3 2 = (R 2 0) + -(R 2 1) + (R 2 2) + -(R 2 3) := by
    calc
      _ = ∑k:Fin 4,(-1:ℤ)^k.val • R 2 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_3_1_0,Pface_3_1_1,Pface_3_1_2,Pface_3_1_3]
  try abel
@[reassoc] lemma Pd_3_2 (a b d:Skeleton C) :
    P32 a b d ≫ (homologyRow (C:=C) 1).d 3 2 = (P21 b d) + -(P21 (a*b) d) + (T b d (b*d) rfl ≫ P21 a (b*d)) := by
  have hd : (homologyRow (C:=C) 1).d 3 2 = (R 2 0) + -(R 2 1) + (R 2 2) + -(R 2 3) := by
    calc
      _ = ∑k:Fin 4,(-1:ℤ)^k.val • R 2 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_3_2_0,Pface_3_2_1,Pface_3_2_2,Pface_3_2_3]
  try abel
@[reassoc] lemma Pd_4_0 [SymmetricCategory C] (a b d e:Skeleton C) :
    P40 a b d e ≫ (homologyRow (C:=C) 1).d 4 3 = -(T b a (a*b) (mul_comm _ _) ≫ P30 (a*b) d e) + (P30 a (b*d) e) + -(P30 a b (d*e)) + (P30 a b d) := by
  have hd : (homologyRow (C:=C) 1).d 4 3 = (R 3 0) + -(R 3 1) + (R 3 2) + -(R 3 3) + (R 3 4) := by
    calc
      _ = ∑k:Fin 5,(-1:ℤ)^k.val • R 3 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_4_0_0,Pface_4_0_1,Pface_4_0_2,Pface_4_0_3,Pface_4_0_4]
  try abel
@[reassoc] lemma Pd_4_1 [SymmetricCategory C] (a b d e:Skeleton C) :
    P41 a b d e ≫ (homologyRow (C:=C) 1).d 4 3 = (P30 b d e) + -(T a b (a*b) rfl ≫ P30 (a*b) d e) + (T d b (b*d) (mul_comm _ _) ≫ P31 a (b*d) e) + -(P31 a b (d*e)) + (P31 a b d) := by
  have hd : (homologyRow (C:=C) 1).d 4 3 = (R 3 0) + -(R 3 1) + (R 3 2) + -(R 3 3) + (R 3 4) := by
    calc
      _ = ∑k:Fin 5,(-1:ℤ)^k.val • R 3 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_4_1_0,Pface_4_1_1,Pface_4_1_2,Pface_4_1_3,Pface_4_1_4]
  try abel
@[reassoc] lemma Pd_4_2 [SymmetricCategory C] (a b d e:Skeleton C) :
    P42 a b d e ≫ (homologyRow (C:=C) 1).d 4 3 = (P31 b d e) + -(P31 (a*b) d e) + (T b d (b*d) rfl ≫ P31 a (b*d) e) + -(T e d (d*e) (mul_comm _ _) ≫ P32 a b (d*e)) + (P32 a b d) := by
  have hd : (homologyRow (C:=C) 1).d 4 3 = (R 3 0) + -(R 3 1) + (R 3 2) + -(R 3 3) + (R 3 4) := by
    calc
      _ = ∑k:Fin 5,(-1:ℤ)^k.val • R 3 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_4_2_0,Pface_4_2_1,Pface_4_2_2,Pface_4_2_3,Pface_4_2_4]
  try abel
@[reassoc] lemma Pd_4_3 (a b d e:Skeleton C) :
    P43 a b d e ≫ (homologyRow (C:=C) 1).d 4 3 = (P32 b d e) + -(P32 (a*b) d e) + (P32 a (b*d) e) + -(T d e (d*e) rfl ≫ P32 a b (d*e)) := by
  have hd : (homologyRow (C:=C) 1).d 4 3 = (R 3 0) + -(R 3 1) + (R 3 2) + -(R 3 3) + (R 3 4) := by
    calc
      _ = ∑k:Fin 5,(-1:ℤ)^k.val • R 3 k := AlternatingFaceMapComplex.obj_d_eq _ _
      _ = _ := by simp [Fin.sum_univ_succ,add_assoc]
  rw [hd]
  simp only [Preadditive.comp_add,Preadditive.comp_neg,Pface_4_3_0,Pface_4_3_1,Pface_4_3_2,Pface_4_3_3,Pface_4_3_4]
  try abel
end MarkedH1

end

end OAI
