import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.RegularTotalDifferential

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits Simplicial Opposite HomologicalComplex AlgebraicTopology
namespace RegularLabels
open FreeChains RegularCoordinates MonoidNerveCoordinates RegularFiniteFaces

variable {P:Type} [CommMonoid P] (F:ActionCategory P P ⥤ A)
@[reassoc] lemma block_d01 (a b:P) :
    totalInj F ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫ ((RegularCoefficient.double F).total c).d 1 0 =
      (totalInj F ⟨⟨(0,0),rfl⟩,![],b,![]⟩) + -(F.map (arrow a b) ≫ totalInj F ⟨⟨(0,0),rfl⟩,![],(a*b),![]⟩) := by
  rw [totalInj_d_ver]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels1_0 a]
  try erw [labels1_1 a]
  try erw [weight1_0 a]
  try erw [weight1_1 a]
  try erw [one_totalInj F (h:=0) (v:=0) rfl ![] b ![]]
  try abel
@[reassoc] lemma block_d10 (a b:P) :
    totalInj F ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫ ((RegularCoefficient.double F).total c).d 1 0 =
      (totalInj F ⟨⟨(0,0),rfl⟩,![],a,![]⟩) + -(F.map (arrow b a) ≫ totalInj F ⟨⟨(0,0),rfl⟩,![],(b*a),![]⟩) := by
  rw [totalInj_d_hor]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels1_0 b]
  try erw [labels1_1 b]
  try erw [weight1_0 b]
  try erw [weight1_1 b]
  try erw [one_totalInj F (h:=0) (v:=0) rfl ![] a ![]]
  try abel
@[reassoc] lemma block_d02 (a b d:P) :
    totalInj F ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫ ((RegularCoefficient.double F).total c).d 2 1 =
      (totalInj F ⟨⟨(0,1),rfl⟩,![b],d,![]⟩) + -(totalInj F ⟨⟨(0,1),rfl⟩,![(a*b)],d,![]⟩) + (F.map (arrow b d) ≫ totalInj F ⟨⟨(0,1),rfl⟩,![a],(b*d),![]⟩) := by
  rw [totalInj_d_ver]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels2_0 a b]
  try erw [labels2_1 a b]
  try erw [labels2_2 a b]
  try erw [weight2_0 a b]
  try erw [weight2_1 a b]
  try erw [weight2_2 a b]
  try erw [one_totalInj F (h:=0) (v:=1) rfl ![b] d ![]]
  try erw [one_totalInj F (h:=0) (v:=1) rfl ![(a*b)] d ![]]
  try abel
@[reassoc] lemma block_d11 (a b d:P) :
    totalInj F ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫ ((RegularCoefficient.double F).total c).d 2 1 =
      (totalInj F ⟨⟨(0,1),rfl⟩,![a],b,![]⟩) + -(F.map (arrow d b) ≫ totalInj F ⟨⟨(0,1),rfl⟩,![a],(d*b),![]⟩) + -(totalInj F ⟨⟨(1,0),rfl⟩,![],b,![d]⟩) + (F.map (arrow a b) ≫ totalInj F ⟨⟨(1,0),rfl⟩,![],(a*b),![d]⟩) := by
  rw [totalInj_d_both]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels1_0 d]
  try erw [labels1_1 d]
  try erw [labels1_0 a]
  try erw [labels1_1 a]
  try erw [weight1_0 d]
  try erw [weight1_1 d]
  try erw [weight1_0 a]
  try erw [weight1_1 a]
  try erw [one_totalInj F (h:=0) (v:=1) rfl ![a] b ![]]
  try erw [one_totalInj F (h:=1) (v:=0) rfl ![] b ![d]]
  try abel
@[reassoc] lemma block_d20 (a b d:P) :
    totalInj F ⟨⟨(2,0),rfl⟩,![],a,![b,d]⟩ ≫ ((RegularCoefficient.double F).total c).d 2 1 =
      (totalInj F ⟨⟨(1,0),rfl⟩,![],a,![d]⟩) + -(totalInj F ⟨⟨(1,0),rfl⟩,![],a,![(b*d)]⟩) + (F.map (arrow d a) ≫ totalInj F ⟨⟨(1,0),rfl⟩,![],(d*a),![b]⟩) := by
  rw [totalInj_d_hor]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels2_0 b d]
  try erw [labels2_1 b d]
  try erw [labels2_2 b d]
  try erw [weight2_0 b d]
  try erw [weight2_1 b d]
  try erw [weight2_2 b d]
  try erw [one_totalInj F (h:=1) (v:=0) rfl ![] a ![d]]
  try erw [one_totalInj F (h:=1) (v:=0) rfl ![] a ![(b*d)]]
  try abel
@[reassoc] lemma block_d03 (a b d e:P) :
    totalInj F ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫ ((RegularCoefficient.double F).total c).d 3 2 =
      (totalInj F ⟨⟨(0,2),rfl⟩,![b,d],e,![]⟩) + -(totalInj F ⟨⟨(0,2),rfl⟩,![(a*b),d],e,![]⟩) + (totalInj F ⟨⟨(0,2),rfl⟩,![a,(b*d)],e,![]⟩) + -(F.map (arrow d e) ≫ totalInj F ⟨⟨(0,2),rfl⟩,![a,b],(d*e),![]⟩) := by
  rw [totalInj_d_ver]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels3_0 a b d]
  try erw [labels3_1 a b d]
  try erw [labels3_2 a b d]
  try erw [labels3_3 a b d]
  try erw [weight3_0 a b d]
  try erw [weight3_1 a b d]
  try erw [weight3_2 a b d]
  try erw [weight3_3 a b d]
  try erw [one_totalInj F (h:=0) (v:=2) rfl ![b,d] e ![]]
  try erw [one_totalInj F (h:=0) (v:=2) rfl ![(a*b),d] e ![]]
  try erw [one_totalInj F (h:=0) (v:=2) rfl ![a,(b*d)] e ![]]
  try abel
@[reassoc] lemma block_d12 (a b d e:P) :
    totalInj F ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫ ((RegularCoefficient.double F).total c).d 3 2 =
      (totalInj F ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩) + -(F.map (arrow e d) ≫ totalInj F ⟨⟨(0,2),rfl⟩,![a,b],(e*d),![]⟩) + -(totalInj F ⟨⟨(1,1),rfl⟩,![b],d,![e]⟩) + (totalInj F ⟨⟨(1,1),rfl⟩,![(a*b)],d,![e]⟩) + -(F.map (arrow b d) ≫ totalInj F ⟨⟨(1,1),rfl⟩,![a],(b*d),![e]⟩) := by
  rw [totalInj_d_both]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels1_0 e]
  try erw [labels1_1 e]
  try erw [labels2_0 a b]
  try erw [labels2_1 a b]
  try erw [labels2_2 a b]
  try erw [weight1_0 e]
  try erw [weight1_1 e]
  try erw [weight2_0 a b]
  try erw [weight2_1 a b]
  try erw [weight2_2 a b]
  try erw [one_totalInj F (h:=0) (v:=2) rfl ![a,b] d ![]]
  try erw [one_totalInj F (h:=1) (v:=1) rfl ![b] d ![e]]
  try erw [one_totalInj F (h:=1) (v:=1) rfl ![(a*b)] d ![e]]
  try abel
@[reassoc] lemma block_d21 (a b d e:P) :
    totalInj F ⟨⟨(2,1),rfl⟩,![a],b,![d,e]⟩ ≫ ((RegularCoefficient.double F).total c).d 3 2 =
      (totalInj F ⟨⟨(1,1),rfl⟩,![a],b,![e]⟩) + -(totalInj F ⟨⟨(1,1),rfl⟩,![a],b,![(d*e)]⟩) + (F.map (arrow e b) ≫ totalInj F ⟨⟨(1,1),rfl⟩,![a],(e*b),![d]⟩) + (totalInj F ⟨⟨(2,0),rfl⟩,![],b,![d,e]⟩) + -(F.map (arrow a b) ≫ totalInj F ⟨⟨(2,0),rfl⟩,![],(a*b),![d,e]⟩) := by
  rw [totalInj_d_both]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels2_0 d e]
  try erw [labels2_1 d e]
  try erw [labels2_2 d e]
  try erw [labels1_0 a]
  try erw [labels1_1 a]
  try erw [weight2_0 d e]
  try erw [weight2_1 d e]
  try erw [weight2_2 d e]
  try erw [weight1_0 a]
  try erw [weight1_1 a]
  try erw [one_totalInj F (h:=1) (v:=1) rfl ![a] b ![e]]
  try erw [one_totalInj F (h:=1) (v:=1) rfl ![a] b ![(d*e)]]
  try erw [one_totalInj F (h:=2) (v:=0) rfl ![] b ![d,e]]
  try abel
@[reassoc] lemma block_d30 (a b d e:P) :
    totalInj F ⟨⟨(3,0),rfl⟩,![],a,![b,d,e]⟩ ≫ ((RegularCoefficient.double F).total c).d 3 2 =
      (totalInj F ⟨⟨(2,0),rfl⟩,![],a,![d,e]⟩) + -(totalInj F ⟨⟨(2,0),rfl⟩,![],a,![(b*d),e]⟩) + (totalInj F ⟨⟨(2,0),rfl⟩,![],a,![b,(d*e)]⟩) + -(F.map (arrow e a) ≫ totalInj F ⟨⟨(2,0),rfl⟩,![],(e*a),![b,d]⟩) := by
  rw [totalInj_d_hor]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  norm_num
  try erw [labels3_0 b d e]
  try erw [labels3_1 b d e]
  try erw [labels3_2 b d e]
  try erw [labels3_3 b d e]
  try erw [weight3_0 b d e]
  try erw [weight3_1 b d e]
  try erw [weight3_2 b d e]
  try erw [weight3_3 b d e]
  try erw [one_totalInj F (h:=2) (v:=0) rfl ![] a ![d,e]]
  try erw [one_totalInj F (h:=2) (v:=0) rfl ![] a ![(b*d),e]]
  try erw [one_totalInj F (h:=2) (v:=0) rfl ![] a ![b,(d*e)]]
  try abel
end RegularLabels

end

end OAI
