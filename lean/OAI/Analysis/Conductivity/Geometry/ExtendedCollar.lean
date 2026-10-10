import Mathlib
import OAI.Analysis.Conductivity.Fourier.RectangularTorusInverse
import OAI.Analysis.Conductivity.Geometry.BoxEnergyPoincare

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

lemma sourceCollarPiece_radial_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hr : 0≤ sourceCollarRadius j (x 0) (x 2)) (ha : |x 1|≤1) :
    sourceRadial (sourceCollarPiece i j x)=sourceCollarRadius j (x 0) (x 2) := by
  have hL : 0<sourceLength := by norm_num [sourceLength]
  simp only [sourceRadial,sourceCollarPiece,Matrix.cons_val_zero,Matrix.cons_val_one,
    abs_mul,abs_of_pos hL,abs_of_nonneg hr]
  have he : sourceLength*sourceCollarRadius j (x 0) (x 2)*|squareFace i (x 1) 0|/sourceLength =
      sourceCollarRadius j (x 0) (x 2)*|squareFace i (x 1) 0| := by field_simp
  rw [he,←mul_max_of_nonneg _ _ hr,squareFace_max i ha,mul_one]

lemma sourceCollarPiece_cross_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hr : 0≤ sourceCollarRadius j (x 0) (x 2)) (ha : |x 1|≤1) :
    sourceCrossCoordinates (sourceCollarPiece i j x)=(1-x 0) • squareFace j (x 2) := by
  ext k; fin_cases k
  · change (sourceRadial (sourceCollarPiece i j x)-sourceRadialCenter)/sourceRadialWidth=
      (1-x 0)*squareFace j (x 2) 0
    rw [sourceCollarPiece_radial_pos i j hr ha,sourceCollarRadius]
    simp only [add_sub_cancel_left]
    have hw : sourceRadialWidth≠0 := by norm_num [sourceRadialWidth,sourceHole]
    field_simp
  · simp [sourceCrossCoordinates,sourceCollarPiece]

lemma sourceCollarPiece_time_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hr : 0≤ sourceCollarRadius j (x 0) (x 2)) (ht : x 0≤1)
    (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceCollarTime (sourceCollarPiece i j x)=x 0 := by
  rw [sourceCollarTime,sourceCollarPiece_cross_pos i j hr ha]
  simp only [Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (sub_nonneg.mpr ht)]
  rw [←mul_max_of_nonneg _ _ (sub_nonneg.mpr ht),squareFace_max j hb]
  ring

lemma sourceCollarInverse_left_pos (i j : Fin 4) {x : Fin 3 → ℝ}
    (hr : 0<sourceCollarRadius j (x 0) (x 2)) (ht : x 0<1)
    (ha : |x 1|≤1) (hb : |x 2|≤1) :
    sourceCollarInverse i j (sourceCollarPiece i j x)=x := by
  have hq : 1-x 0≠0 := (sub_pos.mpr ht).ne'
  ext k; fin_cases k
  · exact sourceCollarPiece_time_pos i j hr.le ht.le ha hb
  · change squareFaceParameter i ![sourceCollarPiece i j x 0/sourceLength,
        sourceCollarPiece i j x 1]/sourceRadial (sourceCollarPiece i j x)=x 1
    rw [sourceCollarPiece_angular,squareFace_parameter,sourceCollarPiece_radial_pos i j hr.le ha]
    exact mul_div_cancel_left₀ _ hr.ne'
  · change squareFaceParameter j (sourceCrossCoordinates (sourceCollarPiece i j x))/
        (1-sourceCollarTime (sourceCollarPiece i j x))=x 2
    rw [sourceCollarPiece_cross_pos i j hr.le ha,squareFace_parameter,
      sourceCollarPiece_time_pos i j hr.le ht.le ha hb]
    exact mul_div_cancel_left₀ _ hq

def sourceExtendedBox (l r : ℝ) : Set (Fin 3 → ℝ) := Icc ![l,-1,-1] ![r,1,1]

lemma mem_sourceExtendedBox {l r : ℝ} {x : Fin 3 → ℝ} :
    x∈sourceExtendedBox l r ↔ x 0∈Icc l r ∧ |x 1| ≤ 1 ∧ |x 2| ≤ 1 := by
  simp [sourceExtendedBox,mem_Icc,Pi.le_def,Fin.forall_fin_succ,abs_le]
  tauto

lemma sourceCollarRadius_extended (j : Fin 4) {t b : ℝ}
    (ht : t∈Icc (-(1:ℝ)/100) (1/100)) (hb : |b|≤1) :
    (1:ℝ)/50≤ sourceCollarRadius j t b ∧ sourceCollarRadius j t b≤2 := by
  have hq : |squareFace j b 0|≤1 := (le_max_left _ _).trans (squareFace_max j hb).le
  have hh := abs_le.mp hq
  have hprod : |(1-t)*squareFace j b 0|≤101/100 := by
    rw [abs_mul,abs_of_nonneg (by linarith [ht.2] : 0≤1-t)]
    nlinarith [ht.1,ht.2]
  have hh' := abs_le.mp hprod
  dsimp [sourceCollarRadius,sourceRadialCenter,sourceRadialWidth,sourceHole]
  constructor <;> linarith

lemma sourceExtendedBox_injOn (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    InjOn (sourceCollarPiece i j) (sourceExtendedBox l r) := by
  have hi (x : Fin 3 → ℝ) (hx : x∈sourceExtendedBox l r) :
      sourceCollarInverse i j (sourceCollarPiece i j x)=x := by
    obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
    exact sourceCollarInverse_left_pos i j
      (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/50)
        (sourceCollarRadius_extended j ⟨hl.trans ht.1,ht.2.trans hr⟩ hb).1)
      (by linarith [ht.2]) ha hb
  intro x hx y hy he
  apply_fun sourceCollarInverse i j at he
  rwa [hi x hx,hi y hy] at he

lemma sourceExtended_jacobian_lower (i j : Fin 4) {l r : ℝ}
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    {x : Fin 3 → ℝ} (hx : x∈sourceExtendedBox l r) :
    (1:ℝ)/100≤abs ((sourceCollarDerivative i j x).det) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have ht' : x 0∈Icc (-(1:ℝ)/100) (1/100) := ⟨hl.trans ht.1,ht.2.trans hr⟩
  have hR := (sourceCollarRadius_extended j ht' hb).1
  rw [sourceCollarDerivative_det]
  have he : -sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)=
      -(sourceLength*sourceCollarRadius j (x 0) (x 2)*sourceRadialWidth*(1-x 0)) := by ring
  rw [he,abs_neg,abs_of_nonneg (by
    have : 0≤ sourceCollarRadius j (x 0) (x 2) := by linarith
    have : 0≤1-x 0 := by linarith [ht'.2]
    norm_num [sourceLength,sourceRadialWidth,sourceHole]; positivity)]
  have hh := mul_le_mul hR (show (99:ℝ)/100≤1-x 0 by linarith [ht'.2])
    (by norm_num : (0:ℝ)≤99/100) (by linarith : 0≤ sourceCollarRadius j (x 0) (x 2))
  norm_num [sourceLength,sourceRadialWidth,sourceHole]
  nlinarith

theorem sourceExtended_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (i j : Fin 4) {l r : ℝ} (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (g : (Fin 3 → ℝ) → F) :
    (∫ y in sourceCollarPiece i j '' sourceExtendedBox l r,g y)=
      ∫ x in sourceExtendedBox l r,abs ((sourceCollarDerivative i j x).det) •
        g (sourceCollarPiece i j x) := by
  exact integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_Icc
    (fun x _ => (sourceCollarPiece_hasFDeriv i j x).hasFDerivWithinAt)
    (sourceExtendedBox_injOn i j hl hr) g

lemma squareFace_abs_le (i : Fin 4) {a : ℝ} (ha : |a|≤1) (k : Fin 2) :
    |squareFace i a k|≤1 := by
  fin_cases k
  · exact (le_max_left _ _).trans (squareFace_max i ha).le
  · exact (le_max_right _ _).trans (squareFace_max i ha).le

lemma sourceRadius_trim_bounds (j : Fin 4) {t b : ℝ}
    (ht : centralThickness≤t ∧ t≤2*centralThickness) (hb : |b|≤1) :
    centralInnerY≤ sourceCollarRadius j t b ∧ sourceCollarRadius j t b≤centralOuterY := by
  have hq := squareFace_abs_le j hb 0
  have hqt : |(1-t)*squareFace j b 0|≤1-centralThickness := by
    have ht0 : 0≤1-t := by norm_num [centralThickness] at ht; linarith
    rw [abs_mul,abs_of_nonneg ht0]
    have hh := mul_le_mul_of_nonneg_left hq ht0
    linarith [ht.1]
  have hh := abs_le.mp hqt
  dsimp [sourceCollarRadius,centralInnerY,centralOuterY,sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at *
  constructor <;> linarith

def sourcePairCoordinates (y : Fin 3 → ℝ) : Box3 := ((y 0,y 1),y 2)

lemma sourceParentCollar_parent (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox centralThickness (2*centralThickness)) :
    centralParentFootprint (sourcePairCoordinates (sourceCollarPiece i j x)).1 ∧
      |(sourcePairCoordinates (sourceCollarPiece i j x)).2|≤centralHeight := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have hr := sourceRadius_trim_bounds j ht hb
  have hr0 : 0≤ sourceCollarRadius j (x 0) (x 2) := by
    have hh : 0<centralInnerY := by norm_num [centralInnerY,sourceHole,sourceRadialWidth,centralThickness]
    linarith
  have hL : 0<sourceLength := by norm_num [sourceLength]
  have ht0 : 0≤1-x 0 := by norm_num [centralThickness] at ht; linarith
  have hq0 := squareFace_abs_le i ha 0
  have hq1 := squareFace_abs_le i ha 1
  have hq2 := squareFace_abs_le j hb 1
  have hx0 : |sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0|≤centralOuterX := by
    rw [abs_mul,abs_mul,abs_of_pos hL,abs_of_nonneg hr0]
    have hh := mul_le_mul_of_nonneg_left hq0 (mul_nonneg hL.le hr0)
    dsimp [centralOuterX,centralOuterY] at *
    nlinarith
  have hx1 : |sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1|≤centralOuterY := by
    rw [abs_mul,abs_of_nonneg hr0]
    nlinarith
  have hin : centralInnerX≤|sourceLength*sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 0| ∨
      centralInnerY≤|sourceCollarRadius j (x 0) (x 2)*squareFace i (x 1) 1| := by
    have hm := squareFace_max i ha
    rcases max_cases |squareFace i (x 1) 0| |squareFace i (x 1) 1| with h|h
    · left
      rw [abs_mul,abs_mul,abs_of_pos hL,abs_of_nonneg hr0,←h.1,hm,mul_one]
      dsimp [centralInnerX,centralInnerY] at *
      nlinarith
    · right
      rw [abs_mul,abs_of_nonneg hr0,←h.1,hm,mul_one]
      exact hr.1
  have ht1 : |(1-x 0)*squareFace j (x 2) 1|≤centralHeight := by
    rw [abs_mul,abs_of_nonneg ht0]
    dsimp [centralHeight]
    nlinarith [ht.1]
  exact ⟨⟨hx0,hx1,hin⟩,ht1⟩

lemma sourceParentCollar_avoids (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox centralThickness (2*centralThickness)) :
    centralChildHeight≤|(sourceCollarPiece i j x) 2| ∨
      (centralAvoidChild 1 ((sourceCollarPiece i j x) 0,(sourceCollarPiece i j x) 1) ∧
        centralAvoidChild (-1) ((sourceCollarPiece i j x) 0,(sourceCollarPiece i j x) 1)) := by
  obtain ⟨ht,ha,hb⟩ := mem_sourceExtendedBox.mp hx
  have hr := sourceRadius_trim_bounds j ht hb
  have hr0 : 0≤ sourceCollarRadius j (x 0) (x 2) := by
    have hh : 0<centralInnerY := by norm_num [centralInnerY,sourceHole,sourceRadialWidth,centralThickness]
    linarith
  have hL : 0<sourceLength := by norm_num [sourceLength]
  fin_cases j
  · right
    change 0≤ sourceCollarRadius 0 (x 0) (x 2) at hr0
    have hlarge : (999:ℝ)/1000≤ sourceCollarRadius 0 (x 0) (x 2) := by
      norm_num [sourceCollarRadius,squareFace,squareFaceBase,squareFaceDirection,Matrix.cons_val_succ,sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at ht ⊢
      linarith
    have hm := squareFace_max i ha
    rcases max_cases |squareFace i (x 1) 0| |squareFace i (x 1) 1| with h|h
    · have he : |(sourceCollarPiece i 0 x) 0|=sourceLength*sourceCollarRadius 0 (x 0) (x 2) := by
        simp only [sourceCollarPiece,Matrix.cons_val_zero,abs_mul,abs_of_pos hL,abs_of_nonneg hr0]
        rw [←h.1,hm,mul_one]
      have hbig : (1598:ℝ)/1000≤|(sourceCollarPiece i 0 x) 0| := by rw [he]; norm_num [sourceLength]; linarith
      have hb1 := abs_sub_le ((sourceCollarPiece i 0 x) 0) sourceOffset
      have hb2 := abs_sub_le ((sourceCollarPiece i 0 x) 0) (-sourceOffset)
      have hlow1 := abs_add_le ((sourceCollarPiece i 0 x) 0-sourceOffset) sourceOffset
      have hlow2 := abs_add_le ((sourceCollarPiece i 0 x) 0+sourceOffset) (-sourceOffset)
      simp only [sub_add_cancel,add_neg_cancel_right] at hlow1 hlow2
      constructor <;> apply Or.inl
      · norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset] at *
        linarith
      · norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset] at *
        linarith
    · have he : |(sourceCollarPiece i 0 x) 1|=sourceCollarRadius 0 (x 0) (x 2) := by
        simp only [sourceCollarPiece,Matrix.cons_val_one,Matrix.cons_val_zero,abs_mul,abs_of_nonneg hr0]
        rw [←h.1,hm,mul_one]
      have hh : centralChildOuterY≤|(sourceCollarPiece i 0 x) 1| := by
        rw [he]
        norm_num [centralChildOuterY,sourceScale,sourceLength,sourceRadialWidth,sourceHole,centralThickness]
        linarith
      exact ⟨Or.inr (Or.inl hh),Or.inr (Or.inl hh)⟩
  · left
    simp only [sourceCollarPiece,Matrix.cons_val_two,squareFace,squareFaceBase,squareFaceDirection,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    norm_num [centralChildHeight,sourceScale,centralThickness] at ht ⊢
    linarith [le_abs_self (1-x 0),neg_le_abs (x 0-1)]
  · right
    change 0≤ sourceCollarRadius 2 (x 0) (x 2) at hr0
    have hsmall : sourceCollarRadius 2 (x 0) (x 2)≤(31:ℝ)/1000 := by
      change sourceRadialCenter+sourceRadialWidth*(1-x 0)*((-1:ℝ)+x 2*0)≤31/1000
      norm_num [sourceRadialCenter,sourceRadialWidth,sourceHole,centralThickness] at ht ⊢
      linarith
    have hq := squareFace_abs_le i ha 0
    have hsmall' : |(sourceCollarPiece i 2 x) 0|≤(1:ℝ)/20 := by
      simp only [sourceCollarPiece,Matrix.cons_val_zero,abs_mul,abs_of_pos hL,abs_of_nonneg hr0]
      norm_num [sourceLength]
      nlinarith
    have hlow1 := abs_sub_le sourceOffset ((sourceCollarPiece i 2 x) 0)
    have hlow2 := abs_sub_le (-sourceOffset) ((sourceCollarPiece i 2 x) 0)
    have htri1 := abs_add_le (sourceOffset-(sourceCollarPiece i 2 x) 0) ((sourceCollarPiece i 2 x) 0)
    have htri2 := abs_add_le (-sourceOffset-(sourceCollarPiece i 2 x) 0) ((sourceCollarPiece i 2 x) 0)
    simp only [sub_add_cancel,abs_sub_comm sourceOffset,abs_sub_comm (-sourceOffset)] at htri1 htri2
    have hc1 : centralChildOuterX≤|(sourceCollarPiece i 2 x) 0-sourceOffset| := by
      norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset] at *
      linarith
    have hc2 : centralChildOuterX≤|(sourceCollarPiece i 2 x) 0+sourceOffset| := by
      norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset] at *
      linarith
    exact ⟨Or.inl (by simpa using hc1),Or.inl (by simpa using hc2)⟩
  · left
    simp only [sourceCollarPiece,Matrix.cons_val_two,squareFace,squareFaceBase,squareFaceDirection,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    norm_num [centralChildHeight,sourceScale,centralThickness] at ht ⊢
    linarith [le_abs_self (1-x 0),neg_le_abs (x 0-1)]

theorem sourceParentCollar_central (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox centralThickness (2*centralThickness)) :
    sourcePairCoordinates (sourceCollarPiece i j x)∈centralClosed :=
  ⟨(sourceParentCollar_parent i j hx).1,(sourceParentCollar_parent i j hx).2,
    sourceParentCollar_avoids i j hx⟩

end ScalarConductivity

end

end OAI
