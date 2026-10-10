import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.MarkedGradedFinite
import OAI.GroupTheory.SimpleAmenable.Homology.MarkedPrimitiveFaces
import OAI.GroupTheory.SimpleAmenable.Homology.RegularTotalFiniteDifferentials

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial SimplicialObject Opposite AlgebraicTopology HomologicalComplex
namespace MarkedH1
open FreeChains ComponentTranslation IntervalBar.Diagram RegularLabels RegularCoordinates MonoidNerveCoordinates RegularFiniteFaces

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
@[reassoc] lemma imageP00 (a:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,0),rfl⟩,![],a,![]⟩ ≫ (gradedIso 0).hom = P10 a := image00 a
@[reassoc] lemma imageP01 (a b:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫ (gradedIso 1).hom = P21 a b := image01 a b
@[reassoc] lemma imageP10 (a b:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫ (gradedIso 1).hom = P20 a b := image10 a b
@[reassoc] lemma imageP02 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫ (gradedIso 2).hom = P32 a b d := image02 a b d
@[reassoc] lemma imageP11 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫ (gradedIso 2).hom = -P31 a b d := image11 a b d
@[reassoc] lemma imageP20 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩ ≫ (gradedIso 2).hom = -P30 a b d := image20 a b d
@[reassoc] lemma imageP03 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫ (gradedIso 3).hom = P43 a b d e := image03 a b d e
@[reassoc] lemma imageP12 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫ (gradedIso 3).hom = P42 a b d e := image12 a b d e
@[reassoc] lemma imageP21 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩ ≫ (gradedIso 3).hom = -P41 a b d e := image21 a b d e
@[reassoc] lemma imageP30 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩ ≫ (gradedIso 3).hom = -P40 a b d e := image30 a b d e
@[reassoc] lemma map_arrow_T (r p:Skeleton C) :
    (homologyDiagram (C:=C) 1).map (arrow r p) = T r p (r*p) rfl := rfl
omit [SymmetricCategory C] in
lemma T_comp_congr {M:A} (r p q q':Skeleton C) (h:r*p=q) (h':r*p=q')
    (e:q=q') (f:∀s:Skeleton C,H s ⟶ M) : T r p q h ≫ f q = T r p q' h' ≫ f q' := by
  cases e
  rfl
lemma compat01 (a b:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 1 0 ≫ (gradedIso 0).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫ (gradedIso 1).hom ≫ (homologyRow (C:=C) 1).d 2 1 := by
  erw [imageP01_assoc]
  erw [Pd_2_1]
  erw [block_d01_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP00 b]
  erw [imageP00 (a*b)]
  simp only [map_arrow_T]
  try erw [mul_comm b a]
  try abel
lemma compat10 (a b:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 1 0 ≫ (gradedIso 0).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫ (gradedIso 1).hom ≫ (homologyRow (C:=C) 1).d 2 1 := by
  erw [imageP10_assoc]
  erw [Pd_2_0]
  erw [block_d10_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP00 a]
  erw [imageP00 (b*a)]
  simp only [map_arrow_T]
  erw [T_comp_congr b a (b*a) (a*b) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P10 t)]
  try erw [mul_comm b a]
  try abel
lemma compat02 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 2 1 ≫ (gradedIso 1).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫ (gradedIso 2).hom ≫ (homologyRow (C:=C) 1).d 3 2 := by
  erw [imageP02_assoc]
  erw [Pd_3_2]
  erw [block_d02_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP01 b d]
  erw [imageP01 (a*b) d]
  erw [imageP01 a (b*d)]
  simp only [map_arrow_T]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm d b]
  try abel
lemma compat11 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 2 1 ≫ (gradedIso 1).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫ (gradedIso 2).hom ≫ (homologyRow (C:=C) 1).d 3 2 := by
  erw [imageP11_assoc]
  erw [Preadditive.neg_comp,Pd_3_1]
  erw [block_d11_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP01 a b]
  erw [imageP01 a (d*b)]
  erw [imageP10 b d]
  erw [imageP10 (a*b) d]
  simp only [map_arrow_T]
  erw [T_comp_congr d b (d*b) (b*d) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P21 a t)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm d b]
  try abel
lemma compat20 (a b d:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 2 1 ≫ (gradedIso 1).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩ ≫ (gradedIso 2).hom ≫ (homologyRow (C:=C) 1).d 3 2 := by
  erw [imageP20_assoc]
  erw [Preadditive.neg_comp,Pd_3_0]
  erw [block_d20_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP10 a b]
  erw [imageP10 a (d*b)]
  erw [imageP10 (b*a) d]
  simp only [map_arrow_T]
  erw [T_comp_congr b a (b*a) (a*b) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P20 t d)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm d b]
  try abel
lemma compat03 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫ (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  erw [imageP03_assoc]
  erw [Pd_4_3]
  erw [block_d03_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP02 b d e]
  erw [imageP02 (a*b) d e]
  erw [imageP02 a (b*d) e]
  erw [imageP02 a b (d*e)]
  simp only [map_arrow_T]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm e a]
  try erw [mul_comm d b]
  try erw [mul_comm e b]
  try erw [mul_comm e d]
  try abel
lemma compat12 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫ (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  erw [imageP12_assoc]
  erw [Pd_4_2]
  erw [block_d12_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP02 a b d]
  erw [imageP02 a b (e*d)]
  erw [imageP11 b d e]
  erw [imageP11 (a*b) d e]
  erw [imageP11 a (b*d) e]
  simp only [map_arrow_T]
  repeat erw [Preadditive.comp_neg]
  erw [T_comp_congr e d (e*d) (d*e) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P32 a b t)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm e a]
  try erw [mul_comm d b]
  try erw [mul_comm e b]
  try erw [mul_comm e d]
  try abel
lemma compat21 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩ ≫ (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  erw [imageP21_assoc]
  erw [Preadditive.neg_comp,Pd_4_1]
  erw [block_d21_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP11 a b d]
  erw [imageP11 a b (e*d)]
  erw [imageP11 a (d*b) e]
  erw [imageP20 b d e]
  erw [imageP20 (a*b) d e]
  simp only [map_arrow_T]
  repeat erw [Preadditive.comp_neg]
  erw [T_comp_congr d b (d*b) (b*d) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P31 a t e)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm e a]
  try erw [mul_comm d b]
  try erw [mul_comm e b]
  try erw [mul_comm e d]
  try abel
lemma compat30 (a b d e:Skeleton C) :
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩ ≫ ((RegularCoefficient.double (homologyDiagram (C:=C) 1)).total c).d 3 2 ≫ (gradedIso 2).hom =
    totalInj (homologyDiagram (C:=C) 1) ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩ ≫ (gradedIso 3).hom ≫ (homologyRow (C:=C) 1).d 4 3 := by
  erw [imageP30_assoc]
  erw [Preadditive.neg_comp,Pd_4_0]
  erw [block_d30_assoc]
  simp only [Preadditive.add_comp,Preadditive.neg_comp,Category.assoc]
  erw [imageP20 a b d]
  erw [imageP20 a b (e*d)]
  erw [imageP20 a (d*b) e]
  erw [imageP20 (b*a) d e]
  simp only [map_arrow_T]
  repeat erw [Preadditive.comp_neg]
  erw [T_comp_congr b a (b*a) (a*b) rfl (mul_comm _ _) (mul_comm _ _) (fun t=>P30 t d e)]
  try erw [mul_comm b a]
  try erw [mul_comm d a]
  try erw [mul_comm e a]
  try erw [mul_comm d b]
  try erw [mul_comm e b]
  try erw [mul_comm e d]
  try abel
end MarkedH1

end

end OAI
