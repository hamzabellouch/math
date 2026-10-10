import Mathlib
import OAI.Analysis.Conductivity.Branching.ChildCentralL2

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceCollarTime_ge_iff (y : Fin 3 → ℝ) (b : ℝ) :
    b ≤ sourceCollarTime y ↔
      |y 2| ≤ 1-b ∧ sourceHole+sourceRadialWidth*b ≤ sourceRadial y ∧
        sourceRadial y ≤ 1-sourceRadialWidth*b := by
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hd : sourceRadialCenter-sourceRadialWidth=sourceHole := by
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole]
  have hd' : sourceRadialCenter+sourceRadialWidth=1 := by
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole]
  simp only [sourceCollarTime,sourceCrossCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [le_sub_iff_add_le,←le_sub_iff_add_le',max_le_iff,abs_le]
  constructor
  · rintro ⟨⟨hl,hr⟩,hz⟩
    refine ⟨hz,?_,?_⟩
    · have h := (le_div_iff₀ hw).mp hl
      nlinarith
    · have h := (div_le_iff₀ hw).mp hr
      nlinarith
  · rintro ⟨hz,hl,hr⟩
    refine ⟨⟨(le_div_iff₀ hw).mpr ?_,(div_le_iff₀ hw).mpr ?_⟩,hz⟩ <;> nlinarith

lemma sourceCollarTime_le_iff (y : Fin 3 → ℝ) (b : ℝ) :
    sourceCollarTime y ≤ b ↔
      1-b ≤ |y 2| ∨ sourceRadial y ≤ sourceHole+sourceRadialWidth*b ∨
        1-sourceRadialWidth*b ≤ sourceRadial y := by
  have hw : 0<sourceRadialWidth := by norm_num [sourceRadialWidth,sourceHole]
  have hd : sourceRadialCenter-sourceRadialWidth=sourceHole := by
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole]
  have hd' : sourceRadialCenter+sourceRadialWidth=1 := by
    norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole]
  simp only [sourceCollarTime,sourceCrossCoordinates,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [sub_le_iff_le_add,←sub_le_iff_le_add',le_max_iff,le_abs]
  constructor
  · rintro ((hr|hl)|hz)
    · exact Or.inr (Or.inr (by have h := (le_div_iff₀ hw).mp hr; nlinarith))
    · exact Or.inr (Or.inl (by have h := (div_le_iff₀ hw).mp (show (sourceRadial y-sourceRadialCenter)/sourceRadialWidth ≤  -(1-b) by linarith); nlinarith))
    · exact Or.inl hz
  · rintro (hz|hl|hr)
    · exact Or.inr hz
    · exact Or.inl (Or.inr (by have h : (sourceRadial y-sourceRadialCenter)/sourceRadialWidth ≤  -(1-b) := (div_le_iff₀ hw).mpr (by nlinarith); linarith))
    · exact Or.inl (Or.inl ((le_div_iff₀ hw).mpr (by nlinarith)))

lemma centralParent_time_iff (y : Fin 3 → ℝ) :
    centralThickness ≤ sourceCollarTime y ↔
      centralParentFootprint (sourcePairCoordinates y).1 ∧ |y 2| ≤ centralHeight := by
  rw [sourceCollarTime_ge_iff]
  have hL : 0<sourceLength := by norm_num [sourceLength]
  simp only [sourceRadial,max_le_iff,le_max_iff,centralParentFootprint,sourcePairCoordinates,
    centralHeight,centralOuterX,centralInnerX,centralOuterY,centralInnerY]
  rw [div_le_iff₀ hL,le_div_iff₀ hL]
  constructor
  · rintro ⟨hz,hi,ho⟩
    exact ⟨⟨by nlinarith [ho.1],ho.2,hi.imp (fun h => by nlinarith [h]) id⟩,hz⟩
  · rintro ⟨⟨hx,hy,hi⟩,hz⟩
    exact ⟨hz,hi.imp (fun h => by nlinarith [h]) id,⟨by nlinarith [hx],hy⟩⟩

lemma centralChild_time_iff (σ : ℝ) (y : Fin 3 → ℝ) :
    sourceCollarTime ((sourceChildHomeomorph σ).symm y) ≤  -centralThickness ↔
      centralChildHeight ≤ |y 2| ∨ centralAvoidChild σ (sourcePairCoordinates y).1 := by
  change sourceCollarTime ![y 1/sourceScale,(y 0-σ*sourceOffset)/sourceScale,y 2/sourceScale] ≤ -centralThickness ↔ _
  rw [sourceCollarTime_le_iff]
  have hs : 0<sourceScale := by norm_num [sourceScale]
  have hL : 0<sourceLength := by norm_num [sourceLength]
  simp only [sourceRadial,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    abs_div,abs_of_pos hs,max_le_iff,le_max_iff,centralAvoidChild,sourcePairCoordinates,
    centralChildHeight,centralChildOuterX,centralChildOuterY,centralChildInnerX,centralChildInnerY,
    div_le_iff₀ hs,le_div_iff₀ hs,div_le_iff₀ hL,le_div_iff₀ hL]
  constructor
  · rintro (hz|⟨hy,hx⟩|hy|hx)
    · left; nlinarith
    · right; right; right; constructor <;> nlinarith
    · right; right; left; nlinarith
    · right; left; nlinarith
  · rintro (hz|hx|hy|⟨hx,hy⟩)
    · left; nlinarith
    · right; right; right; nlinarith
    · right; right; left; nlinarith
    · right; left; constructor <;> nlinarith

theorem centralPhysical_time_iff (y : Fin 3 → ℝ) :
    y∈centralPhysical ↔ centralThickness ≤ sourceCollarTime y ∧
      (∀ k : Fin 2,sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y) ≤  -centralThickness) := by
  simp only [centralParent_time_iff,centralChild_time_iff,centralPhysical,mem_preimage,
    centralClosed,mem_ofPred_eq,sourcePairCoordinates,actualChildSign,Fin.forall_fin_two,
    ite_true,Fin.isValue,one_ne_zero,ite_false]
  tauto

end ScalarConductivity

end

end OAI
