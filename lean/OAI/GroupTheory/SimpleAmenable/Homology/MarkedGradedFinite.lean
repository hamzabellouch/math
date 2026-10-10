import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.MarkedSigns

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory Simplicial Opposite
namespace MarkedH1
open FreeChains ComponentTranslation

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
omit [SymmetricCategory C] in
lemma primitive_transport {n:ℕ} {a b:Σ_:Fin n,Fin n→Skeleton C} (e:a=b) :
    eqToHom (congrArg (fun z:Σ_:Fin n,Fin n→Skeleton C=>H (z.2 z.1)) e.symm) ≫
      primitive a.2 a.1 = primitive b.2 b.1 := by
  subst b
  simp
def s00 (a:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 0 := ⟨⟨(0,0),rfl⟩,![],a,![]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words00 (a:Skeleton C) : DoubleCoordinates.words _ 0 (s00 a)=⟨0,![a]⟩ := by
  dsimp [s00,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j
  rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label00 (a:Skeleton C) : (labelIso (s00 a)).hom = (-1:ℤ)^0 • 𝟙 (H a) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s00]
  rw [show MarkedSigns.exponent 0 0=0 from by decide]
  change ((-1:ℤ)^0 • 𝟙 (H a)) ≫ eqToHom (rfl: H a=H a) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive00 (a:Skeleton C) :
    primitive (DoubleCoordinates.words _ 0 (s00 a)).2 (DoubleCoordinates.words _ 0 (s00 a)).1 =
      primitive ![a] 0 := by
  have hh:=primitive_transport (words00 a)
  change (𝟙 (H a)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image00 (a:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,0),rfl⟩,![],a,![]⟩ ≫
      (gradedIso 0).hom = primitive ![a] 0 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s00 a) ≫ _ = _
  rw [totalInj_gradedIso,label00,primitive00]
  norm_num
  try exact Category.id_comp _
def s10 (a b:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 1 := ⟨⟨(1,0),rfl⟩,![],a,![b]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words10 (a b:Skeleton C) : DoubleCoordinates.words _ 1 (s10 a b)=⟨0,![a,b]⟩ := by
  dsimp [s10,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label10 (a b:Skeleton C) : (labelIso (s10 a b)).hom = (-1:ℤ)^2 • 𝟙 (H a) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s10]
  rw [show MarkedSigns.exponent 1 0=2 from by decide]
  change ((-1:ℤ)^2 • 𝟙 (H a)) ≫ eqToHom (rfl: H a=H a) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive10 (a b:Skeleton C) :
    primitive (DoubleCoordinates.words _ 1 (s10 a b)).2 (DoubleCoordinates.words _ 1 (s10 a b)).1 =
      primitive ![a,b] 0 := by
  have hh:=primitive_transport (words10 a b)
  change (𝟙 (H a)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image10 (a b:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,0),rfl⟩,![],a,![b]⟩ ≫
      (gradedIso 1).hom = primitive ![a,b] 0 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s10 a b) ≫ _ = _
  rw [totalInj_gradedIso,label10,primitive10]
  norm_num
  try exact Category.id_comp _
def s01 (a b:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 1 := ⟨⟨(0,1),rfl⟩,![a],b,![]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words01 (a b:Skeleton C) : DoubleCoordinates.words _ 1 (s01 a b)=⟨1,![a,b]⟩ := by
  dsimp [s01,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label01 (a b:Skeleton C) : (labelIso (s01 a b)).hom = (-1:ℤ)^0 • 𝟙 (H b) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s01]
  rw [show MarkedSigns.exponent 0 1=0 from by decide]
  change ((-1:ℤ)^0 • 𝟙 (H b)) ≫ eqToHom (rfl: H b=H b) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive01 (a b:Skeleton C) :
    primitive (DoubleCoordinates.words _ 1 (s01 a b)).2 (DoubleCoordinates.words _ 1 (s01 a b)).1 =
      primitive ![a,b] 1 := by
  have hh:=primitive_transport (words01 a b)
  change (𝟙 (H b)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image01 (a b:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,1),rfl⟩,![a],b,![]⟩ ≫
      (gradedIso 1).hom = primitive ![a,b] 1 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s01 a b) ≫ _ = _
  rw [totalInj_gradedIso,label01,primitive01]
  norm_num
  try exact Category.id_comp _
def s20 (a b d:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 2 := ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words20 (a b d:Skeleton C) : DoubleCoordinates.words _ 2 (s20 a b d)=⟨0,![a,b,d]⟩ := by
  dsimp [s20,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label20 (a b d:Skeleton C) : (labelIso (s20 a b d)).hom = (-1:ℤ)^5 • 𝟙 (H a) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s20]
  rw [show MarkedSigns.exponent 2 0=5 from by decide]
  change ((-1:ℤ)^5 • 𝟙 (H a)) ≫ eqToHom (rfl: H a=H a) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive20 (a b d:Skeleton C) :
    primitive (DoubleCoordinates.words _ 2 (s20 a b d)).2 (DoubleCoordinates.words _ 2 (s20 a b d)).1 =
      primitive ![a,b,d] 0 := by
  have hh:=primitive_transport (words20 a b d)
  change (𝟙 (H a)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image20 (a b d:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,0),rfl⟩,![],a,![d,b]⟩ ≫
      (gradedIso 2).hom = -primitive ![a,b,d] 0 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s20 a b d) ≫ _ = _
  rw [totalInj_gradedIso,label20,primitive20]
  norm_num
  erw [Preadditive.neg_comp, Category.id_comp]
  rfl
def s11 (a b d:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 2 := ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words11 (a b d:Skeleton C) : DoubleCoordinates.words _ 2 (s11 a b d)=⟨1,![a,b,d]⟩ := by
  dsimp [s11,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label11 (a b d:Skeleton C) : (labelIso (s11 a b d)).hom = (-1:ℤ)^3 • 𝟙 (H b) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s11]
  rw [show MarkedSigns.exponent 1 1=3 from by decide]
  change ((-1:ℤ)^3 • 𝟙 (H b)) ≫ eqToHom (rfl: H b=H b) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive11 (a b d:Skeleton C) :
    primitive (DoubleCoordinates.words _ 2 (s11 a b d)).2 (DoubleCoordinates.words _ 2 (s11 a b d)).1 =
      primitive ![a,b,d] 1 := by
  have hh:=primitive_transport (words11 a b d)
  change (𝟙 (H b)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image11 (a b d:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,1),rfl⟩,![a],b,![d]⟩ ≫
      (gradedIso 2).hom = -primitive ![a,b,d] 1 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s11 a b d) ≫ _ = _
  rw [totalInj_gradedIso,label11,primitive11]
  norm_num
  erw [Preadditive.neg_comp, Category.id_comp]
  rfl
def s02 (a b d:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 2 := ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words02 (a b d:Skeleton C) : DoubleCoordinates.words _ 2 (s02 a b d)=⟨2,![a,b,d]⟩ := by
  dsimp [s02,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label02 (a b d:Skeleton C) : (labelIso (s02 a b d)).hom = (-1:ℤ)^0 • 𝟙 (H d) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s02]
  rw [show MarkedSigns.exponent 0 2=0 from by decide]
  change ((-1:ℤ)^0 • 𝟙 (H d)) ≫ eqToHom (rfl: H d=H d) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive02 (a b d:Skeleton C) :
    primitive (DoubleCoordinates.words _ 2 (s02 a b d)).2 (DoubleCoordinates.words _ 2 (s02 a b d)).1 =
      primitive ![a,b,d] 2 := by
  have hh:=primitive_transport (words02 a b d)
  change (𝟙 (H d)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image02 (a b d:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,2),rfl⟩,![a,b],d,![]⟩ ≫
      (gradedIso 2).hom = primitive ![a,b,d] 2 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s02 a b d) ≫ _ = _
  rw [totalInj_gradedIso,label02,primitive02]
  norm_num
  try exact Category.id_comp _
def s30 (a b d e:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 3 := ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words30 (a b d e:Skeleton C) : DoubleCoordinates.words _ 3 (s30 a b d e)=⟨0,![a,b,d,e]⟩ := by
  dsimp [s30,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label30 (a b d e:Skeleton C) : (labelIso (s30 a b d e)).hom = (-1:ℤ)^9 • 𝟙 (H a) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s30]
  rw [show MarkedSigns.exponent 3 0=9 from by decide]
  change ((-1:ℤ)^9 • 𝟙 (H a)) ≫ eqToHom (rfl: H a=H a) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive30 (a b d e:Skeleton C) :
    primitive (DoubleCoordinates.words _ 3 (s30 a b d e)).2 (DoubleCoordinates.words _ 3 (s30 a b d e)).1 =
      primitive ![a,b,d,e] 0 := by
  have hh:=primitive_transport (words30 a b d e)
  change (𝟙 (H a)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image30 (a b d e:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(3,0),rfl⟩,![],a,![e,d,b]⟩ ≫
      (gradedIso 3).hom = -primitive ![a,b,d,e] 0 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s30 a b d e) ≫ _ = _
  rw [totalInj_gradedIso,label30,primitive30]
  norm_num
  erw [Preadditive.neg_comp, Category.id_comp]
  rfl
def s21 (a b d e:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 3 := ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words21 (a b d e:Skeleton C) : DoubleCoordinates.words _ 3 (s21 a b d e)=⟨1,![a,b,d,e]⟩ := by
  dsimp [s21,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label21 (a b d e:Skeleton C) : (labelIso (s21 a b d e)).hom = (-1:ℤ)^7 • 𝟙 (H b) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s21]
  rw [show MarkedSigns.exponent 2 1=7 from by decide]
  change ((-1:ℤ)^7 • 𝟙 (H b)) ≫ eqToHom (rfl: H b=H b) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive21 (a b d e:Skeleton C) :
    primitive (DoubleCoordinates.words _ 3 (s21 a b d e)).2 (DoubleCoordinates.words _ 3 (s21 a b d e)).1 =
      primitive ![a,b,d,e] 1 := by
  have hh:=primitive_transport (words21 a b d e)
  change (𝟙 (H b)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image21 (a b d e:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(2,1),rfl⟩,![a],b,![e,d]⟩ ≫
      (gradedIso 3).hom = -primitive ![a,b,d,e] 1 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s21 a b d e) ≫ _ = _
  rw [totalInj_gradedIso,label21,primitive21]
  norm_num
  erw [Preadditive.neg_comp, Category.id_comp]
  rfl
def s12 (a b d e:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 3 := ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words12 (a b d e:Skeleton C) : DoubleCoordinates.words _ 3 (s12 a b d e)=⟨2,![a,b,d,e]⟩ := by
  dsimp [s12,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label12 (a b d e:Skeleton C) : (labelIso (s12 a b d e)).hom = (-1:ℤ)^4 • 𝟙 (H d) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s12]
  rw [show MarkedSigns.exponent 1 2=4 from by decide]
  change ((-1:ℤ)^4 • 𝟙 (H d)) ≫ eqToHom (rfl: H d=H d) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive12 (a b d e:Skeleton C) :
    primitive (DoubleCoordinates.words _ 3 (s12 a b d e)).2 (DoubleCoordinates.words _ 3 (s12 a b d e)).1 =
      primitive ![a,b,d,e] 2 := by
  have hh:=primitive_transport (words12 a b d e)
  change (𝟙 (H d)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image12 (a b d e:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(1,2),rfl⟩,![a,b],d,![e]⟩ ≫
      (gradedIso 3).hom = primitive ![a,b,d,e] 2 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s12 a b d e) ≫ _ = _
  rw [totalInj_gradedIso,label12,primitive12]
  norm_num
  try exact Category.id_comp _
def s03 (a b d e:Skeleton C) : DoubleCoordinates.Index (Skeleton C) 3 := ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma words03 (a b d e:Skeleton C) : DoubleCoordinates.words _ 3 (s03 a b d e)=⟨3,![a,b,d,e]⟩ := by
  dsimp [s03,DoubleCoordinates.words,DoubleCoordinates.equiv,DoubleCoordinates.toSplit,MarkedCoordinates.equiv]
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  funext j
  fin_cases j <;> rfl
omit [MonoidalCategory C] [SymmetricCategory C] in
lemma label03 (a b d e:Skeleton C) : (labelIso (s03 a b d e)).hom = (-1:ℤ)^0 • 𝟙 (H e) := by
  dsimp only [labelIso,Iso.trans_hom,signIso,s03]
  rw [show MarkedSigns.exponent 0 3=0 from by decide]
  change ((-1:ℤ)^0 • 𝟙 (H e)) ≫ eqToHom (rfl: H e=H e) = _
  exact Category.comp_id _
omit [SymmetricCategory C] in
lemma primitive03 (a b d e:Skeleton C) :
    primitive (DoubleCoordinates.words _ 3 (s03 a b d e)).2 (DoubleCoordinates.words _ 3 (s03 a b d e)).1 =
      primitive ![a,b,d,e] 3 := by
  have hh:=primitive_transport (words03 a b d e)
  change (𝟙 (H e)) ≫ _ = _ at hh
  erw [Category.id_comp] at hh
  exact hh
@[reassoc] lemma image03 (a b d e:Skeleton C) :
    RegularLabels.totalInj (homologyDiagram (C:=C) 1) ⟨⟨(0,3),rfl⟩,![a,b,d],e,![]⟩ ≫
      (gradedIso 3).hom = primitive ![a,b,d,e] 3 := by
  change RegularLabels.totalInj (homologyDiagram (C:=C) 1) (s03 a b d e) ≫ _ = _
  rw [totalInj_gradedIso,label03,primitive03]
  norm_num
  try exact Category.id_comp _
end MarkedH1

end OAI
