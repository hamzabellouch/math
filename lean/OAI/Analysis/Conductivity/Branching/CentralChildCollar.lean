import Mathlib
import OAI.Analysis.Conductivity.Geometry.ExtendedCollar

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

def sourceChildCoordinates (σ : ℝ) (y : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![sourceScale*y 1+σ*sourceOffset,sourceScale*y 0,sourceScale*y 2]

lemma sourceRadius_child_bounds (j : Fin 4) {t b : ℝ}
    (ht : -2*centralThickness≤t ∧ t≤ -centralThickness) (hb : |b|≤1) :
    (29:ℝ)/1000≤ sourceCollarRadius j t b ∧ sourceCollarRadius j t b≤1001/1000 := by
  have hq := squareFace_abs_le j hb 0
  have hqt : |(1-t)*squareFace j b 0|≤1+2*centralThickness := by
    have ht0 : 0≤1-t := by norm_num [centralThickness] at ht; linarith
    rw [abs_mul,abs_of_nonneg ht0]
    have hh := mul_le_mul_of_nonneg_left hq ht0
    linarith [ht.1]
  have hh := abs_le.mp hqt
  dsimp [sourceCollarRadius,sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at *
  constructor <;> linarith

lemma sourceChildCollar_bounds (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    |(sourceCollarPiece i j x) 0|≤(1602:ℝ)/1000 ∧
    |(sourceCollarPiece i j x) 1|≤(1001:ℝ)/1000 ∧
    |(sourceCollarPiece i j x) 2|≤(1002:ℝ)/1000 := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have hr := sourceRadius_child_bounds j ht hb
  have hr0 : 0≤ sourceCollarRadius j (x 0) (x 2) := by linarith
  have ht0 : 0≤1-x 0 := by norm_num [centralThickness] at ht; linarith
  have h0 := squareFace_abs_le i ha 0
  have h1 := squareFace_abs_le i ha 1
  have h2 := squareFace_abs_le j hb 1
  have hh0 := mul_le_mul_of_nonneg_left h0 hr0
  have hh1 := mul_le_mul_of_nonneg_left h1 hr0
  have hh2 := mul_le_mul_of_nonneg_left h2 ht0
  change |sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0|≤_ ∧
    |sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1|≤_ ∧
    |(1-x 0)*squareFace j (x 2) 1|≤_
  simp only [abs_mul,abs_of_nonneg hr0,abs_of_nonneg ht0]
  norm_num [sourceLength,centralThickness] at ht ⊢
  constructor
  · nlinarith
  · constructor <;> linarith

lemma sourceChildCoordinates_offset (σ : ℝ) (y : Fin 3 → ℝ) :
    sourceChildCoordinates σ y 0-σ*sourceOffset=sourceScale*y 1 := by
  simp [sourceChildCoordinates]

lemma sourceChildCollar_parent (i j : Fin 4) {σ : ℝ} (hσ : |σ|=1) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    centralParentFootprint (sourcePairCoordinates (sourceChildCoordinates σ (sourceCollarPiece i j x))).1 ∧
      |(sourceChildCoordinates σ (sourceCollarPiece i j x)) 2|≤centralHeight := by
  have hb := sourceChildCollar_bounds i j hx
  let y := sourceCollarPiece i j x
  have ha : |σ*sourceOffset|=sourceOffset := by rw [abs_mul,hσ,one_mul]; norm_num [sourceOffset]
  have hs : 0<sourceScale := by norm_num [sourceScale]
  have hxa := abs_add_le (sourceScale*y 1) (σ*sourceOffset)
  rw [abs_mul,abs_of_pos hs,ha] at hxa
  have hxb := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+σ*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+σ*sourceOffset)=σ*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos hs] at hxb
  change (|sourceScale*y 1+σ*sourceOffset|≤centralOuterX ∧
    |sourceScale*y 0|≤centralOuterY ∧ (centralInnerX≤|sourceScale*y 1+σ*sourceOffset| ∨
      centralInnerY≤|sourceScale*y 0|)) ∧ |sourceScale*y 2|≤centralHeight
  simp only [abs_mul,abs_of_pos hs]
  constructor
  · refine ⟨?_,?_,Or.inl ?_⟩
    · dsimp [centralOuterX,sourceLength,sourceRadialWidth,sourceHole,centralThickness,sourceScale,sourceOffset]
      dsimp [sourceScale,sourceOffset] at hxa
      linarith [hb.2.1]
    · norm_num [centralOuterY,sourceRadialWidth,sourceHole,centralThickness,sourceScale]
      linarith [hb.1]
    · norm_num [centralInnerX,sourceLength,sourceHole,sourceRadialWidth,centralThickness,sourceScale,sourceOffset]
      dsimp [sourceScale,sourceOffset] at hxb
      linarith [hb.2.1]
  · norm_num [sourceScale,centralHeight,centralThickness]
    linarith [hb.2.2]

lemma sourceChildCollar_other (i j : Fin 4) {σ : ℝ} (hσ : |σ|=1) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    centralAvoidChild (-σ) (sourcePairCoordinates (sourceChildCoordinates σ (sourceCollarPiece i j x))).1 := by
  apply Or.inl
  have hb := (sourceChildCollar_bounds i j hx).2.1
  let y := sourceCollarPiece i j x
  have ha : |2*σ*sourceOffset|=2*sourceOffset := by rw [abs_mul,abs_mul,hσ]; norm_num [sourceOffset]
  have ht := abs_add_le (-sourceScale*y 1) (sourceScale*y 1+2*σ*sourceOffset)
  have he : -sourceScale*y 1+(sourceScale*y 1+2*σ*sourceOffset)=2*σ*sourceOffset := by ring
  rw [he,ha,abs_mul,abs_neg,abs_of_pos (show 0<sourceScale by norm_num [sourceScale])] at ht
  change centralChildOuterX≤|sourceScale*y 1+σ*sourceOffset-(-σ)*sourceOffset|
  have he' : sourceScale*y 1+σ*sourceOffset-(-σ)*sourceOffset=sourceScale*y 1+2*σ*sourceOffset := by ring
  rw [he']
  norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset]
  dsimp [sourceScale,sourceOffset] at ht
  linarith

lemma sourceChildCollar_same (i j : Fin 4) (σ : ℝ) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    centralChildHeight≤|(sourceChildCoordinates σ (sourceCollarPiece i j x)) 2| ∨
      centralAvoidChild σ (sourcePairCoordinates (sourceChildCoordinates σ (sourceCollarPiece i j x))).1 := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have hr := sourceRadius_child_bounds j ht hb
  have hr0 : 0≤ sourceCollarRadius j (x 0) (x 2) := by linarith
  have hL : 0<sourceLength := by norm_num [sourceLength]
  have hs : 0<sourceScale := by norm_num [sourceScale]
  have ht0 : 0≤1-x 0 := by norm_num [centralThickness] at ht; linarith
  have hcoord : (sourceChildCoordinates σ (sourceCollarPiece i j x)) 0-σ*sourceOffset=
      sourceScale*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1 := by
    rw [sourceChildCoordinates_offset]
    change sourceScale*(sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1)=_
    ring
  change centralChildHeight≤|sourceScale*((1-x 0)*squareFace j (x 2) 1)| ∨
    (centralChildOuterX≤|(sourceChildCoordinates σ (sourceCollarPiece i j x)) 0-σ*sourceOffset| ∨
      centralChildOuterY≤|sourceScale*(sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0)| ∨
      (|(sourceChildCoordinates σ (sourceCollarPiece i j x)) 0-σ*sourceOffset|≤centralChildInnerX ∧
        |sourceScale*(sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0)|≤centralChildInnerY))
  rw [hcoord]
  simp only [abs_mul,abs_of_pos hs,abs_of_pos hL,abs_of_nonneg hr0,abs_of_nonneg ht0]
  fin_cases j
  · right
    have hrad : 1+sourceRadialWidth*centralThickness≤ sourceCollarRadius 0 (x 0) (x 2) := by
      norm_num [sourceCollarRadius,squareFace,squareFaceBase,squareFaceDirection,Matrix.cons_val_succ,
        sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at ht ⊢
      linarith
    have hm := squareFace_max i ha
    rcases max_cases |squareFace i (x 1) 0| |squareFace i (x 1) 1| with h|h
    · right; left
      rw [←h.1,hm,mul_one]
      dsimp [centralChildOuterY]
      nlinarith [mul_nonneg hs.le hL.le]
    · left
      rw [←h.1,hm,mul_one]
      dsimp [centralChildOuterX]
      exact mul_le_mul_of_nonneg_left hrad hs.le
  · left
    norm_num [squareFace,squareFaceBase,squareFaceDirection,Matrix.cons_val_succ,centralChildHeight,centralThickness,sourceScale] at ht ⊢
    linarith
  · right; right; right
    have hrad : sourceCollarRadius 2 (x 0) (x 2)≤ sourceHole-sourceRadialWidth*centralThickness := by
      change sourceRadialCenter+sourceRadialWidth*(1-x 0)*((-1:ℝ)+x 2*0)≤_
      norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at ht ⊢
      linarith
    have h0 := squareFace_abs_le i ha 0
    have h1 := squareFace_abs_le i ha 1
    change 0≤ sourceCollarRadius 2 (x 0) (x 2) at hr0
    have hh0 := mul_le_mul_of_nonneg_left h0 hr0
    have hh1 := mul_le_mul_of_nonneg_left h1 hr0
    constructor
    · dsimp [centralChildInnerX,sourceScale,sourceHole,sourceRadialWidth,centralThickness] at *
      nlinarith
    · dsimp [centralChildInnerY,sourceScale,sourceLength,sourceHole,sourceRadialWidth,centralThickness] at *
      nlinarith
  · left
    norm_num [squareFace,squareFaceBase,squareFaceDirection,Matrix.cons_val_succ,centralChildHeight,centralThickness,sourceScale] at ht ⊢
    linarith

theorem sourceChildCollar_central (i j : Fin 4) {σ : ℝ} (hσ : σ=1 ∨ σ= -1)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox (-2*centralThickness) (-centralThickness)) :
    sourcePairCoordinates (sourceChildCoordinates σ (sourceCollarPiece i j x))∈centralClosed := by
  have ha : |σ|=1 := by rcases hσ with rfl|rfl <;> norm_num
  have hp := sourceChildCollar_parent i j ha hx
  refine ⟨hp.1,hp.2,?_⟩
  rcases sourceChildCollar_same i j σ hx with ht|hs
  · exact Or.inl ht
  · right
    have ho := sourceChildCollar_other i j ha hx
    rcases hσ with rfl|rfl
    · exact ⟨hs,ho⟩
    · exact ⟨by simpa using ho,hs⟩

end ScalarConductivity

end

end OAI
