import Mathlib
import OAI.Analysis.Conductivity.Fourier.RectangularTorusAtlas
import OAI.Analysis.Conductivity.Geometry.AffineBoxPoincare
import OAI.Analysis.Conductivity.Variational.OverlapPoincare

namespace OAI

noncomputable section

namespace ScalarConductivity
open Set MeasureTheory

def cubeEnergyDensity (f : Box3 → ℝ) (z : Box3) : ℝ :=
  (cubePartial f ((1,0),0) z)^2+(cubePartial f ((0,1),0) z)^2+
    (cubePartial f ((0,0),1) z)^2

lemma continuous_cubeEnergyDensity {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) : Continuous (cubeEnergyDensity f) :=
  (((continuous_cubePartial hf _).pow 2).add ((continuous_cubePartial hf _).pow 2)).add
    ((continuous_cubePartial hf _).pow 2)

lemma cubeEnergyDensity_nonneg (f : Box3 → ℝ) (z : Box3) : 0≤cubeEnergyDensity f z := by
  unfold cubeEnergyDensity; positivity

theorem smooth_box_volume_poincare {f : Box3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a r : Box3)
    (h₁ : 0<r.1.1) (h₂ : 0<r.1.2) (h₃ : 0<r.2) :
    localVariance volume (closedBox a r) f (boxAverage a r f) ≤
      (4*(r.1.1^2+r.1.2^2+r.2^2))*(∫ z in closedBox a r, cubeEnergyDensity f z) := by
  let R := r.1.1^2+r.1.2^2+r.2^2
  let e : Box3 → ℝ := fun z => r.1.1^2*(cubePartial f ((1,0),0) z)^2+
    r.1.2^2*(cubePartial f ((0,1),0) z)^2+r.2^2*(cubePartial f ((0,0),1) z)^2
  have he : Continuous e :=
    ((continuous_const.mul ((continuous_cubePartial hf _).pow 2)).add
      (continuous_const.mul ((continuous_cubePartial hf _).pow 2))).add
        (continuous_const.mul ((continuous_cubePartial hf _).pow 2))
  have hP := smooth_box_poincare hf a r
  rw [boxAverage_eq_integral (f := fun z => (f z-boxAverage a r f)^2) ((hf.continuous.sub continuous_const).pow 2) a r h₁ h₂ h₃,
    boxAverage_eq_integral (f := e) he a r h₁ h₂ h₃] at hP
  have hV : 0<r.1.1*r.1.2*r.2 := by positivity
  have hPi : localVariance volume (closedBox a r) f (boxAverage a r f) ≤
      4*(∫ z in closedBox a r, e z) := by
    apply (mul_le_mul_iff_right₀ (inv_pos.mpr hV)).mp
    change _ ≤ _ at hP
    dsimp [localVariance]
    nlinarith [hP]
  have hi := integral_mono (μ := volume.restrict (closedBox a r))
    (f := e) (g := fun z => R*cubeEnergyDensity f z)
    (he.continuousOn.integrableOn_compact (isCompact_closedBox a r))
    ((continuous_const.mul (continuous_cubeEnergyDensity hf)).continuousOn.integrableOn_compact
      (isCompact_closedBox a r))
    (fun z => show e z ≤ R*cubeEnergyDensity f z by
      dsimp [e,R,cubeEnergyDensity]
      have hx := mul_nonneg (sq_nonneg r.1.1)
        (add_nonneg (sq_nonneg (cubePartial f ((0,1),0) z)) (sq_nonneg (cubePartial f ((0,0),1) z)))
      have hy := mul_nonneg (sq_nonneg r.1.2)
        (add_nonneg (sq_nonneg (cubePartial f ((1,0),0) z)) (sq_nonneg (cubePartial f ((0,0),1) z)))
      have ht := mul_nonneg (sq_nonneg r.2)
        (add_nonneg (sq_nonneg (cubePartial f ((1,0),0) z)) (sq_nonneg (cubePartial f ((0,1),0) z)))
      nlinarith)
  rw [integral_const_mul] at hi
  change _ ≤ 4*R*(∫ z in closedBox a r, cubeEnergyDensity f z)
  nlinarith

structure RectFootprint where
  xl : ℝ
  xu : ℝ
  yl : ℝ
  yu : ℝ

def RectFootprint.carrier (Q : RectFootprint) : Set (ℝ×ℝ) :=
  Icc Q.xl Q.xu ×ˢ Icc Q.yl Q.yu

def RectFootprint.inter (Q R : RectFootprint) : RectFootprint :=
  ⟨max Q.xl R.xl,min Q.xu R.xu,max Q.yl R.yl,min Q.yu R.yu⟩

lemma RectFootprint.inter_carrier (Q R : RectFootprint) :
    (Q.inter R).carrier=Q.carrier∩R.carrier := by
  ext z
  simp only [RectFootprint.carrier,RectFootprint.inter,mem_prod,mem_Icc,mem_inter_iff,
    max_le_iff,le_min_iff]
  tauto

def RectFootprint.prism (Q : RectFootprint) (lo hi : ℝ) : Set Box3 :=
  Q.carrier ×ˢ Icc lo hi

lemma RectFootprint.prism_closedBox (Q : RectFootprint) (lo hi : ℝ) :
    Q.prism lo hi = closedBox ((Q.xl,Q.yl),lo) ((Q.xu-Q.xl,Q.yu-Q.yl),hi-lo) := by
  simp [RectFootprint.prism,RectFootprint.carrier,closedBox]

lemma RectFootprint.prism_compact (Q : RectFootprint) (lo hi : ℝ) :
    IsCompact (Q.prism lo hi) := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

def centralThickness : ℝ := 1/1000
def centralOuterX : ℝ := sourceLength*(1-sourceRadialWidth*centralThickness)
def centralInnerX : ℝ := sourceLength*(sourceHole+sourceRadialWidth*centralThickness)
def centralOuterY : ℝ := 1-sourceRadialWidth*centralThickness
def centralInnerY : ℝ := sourceHole+sourceRadialWidth*centralThickness
def centralHeight : ℝ := 1-centralThickness
def centralChildHeight : ℝ := sourceScale*(1+centralThickness)
def centralChildOuterX : ℝ := sourceScale*(1+sourceRadialWidth*centralThickness)
def centralChildOuterY : ℝ := sourceScale*sourceLength*(1+sourceRadialWidth*centralThickness)
def centralChildInnerX : ℝ := sourceScale*(sourceHole-sourceRadialWidth*centralThickness)
def centralChildInnerY : ℝ := sourceScale*sourceLength*(sourceHole-sourceRadialWidth*centralThickness)

def centralParentStrip (i : Fin 4) : RectFootprint :=
  ![⟨centralInnerX,centralOuterX,-centralOuterY,centralOuterY⟩,
    ⟨-centralOuterX,centralOuterX,centralInnerY,centralOuterY⟩,
    ⟨-centralOuterX,-centralInnerX,-centralOuterY,centralOuterY⟩,
    ⟨-centralOuterX,centralOuterX,-centralOuterY,-centralInnerY⟩] i

def centralChildOption (σ : ℝ) (k : Fin 5) : RectFootprint :=
  ![⟨σ*sourceOffset+centralChildOuterX,centralOuterX,-centralOuterY,centralOuterY⟩,
    ⟨-centralOuterX,centralOuterX,centralChildOuterY,centralOuterY⟩,
    ⟨-centralOuterX,σ*sourceOffset-centralChildOuterX,-centralOuterY,centralOuterY⟩,
    ⟨-centralOuterX,centralOuterX,-centralOuterY,-centralChildOuterY⟩,
    ⟨σ*sourceOffset-centralChildInnerX,σ*sourceOffset+centralChildInnerX,
      -centralChildInnerY,centralChildInnerY⟩] k

def centralParentFootprint (z : ℝ×ℝ) : Prop :=
  |z.1| ≤ centralOuterX ∧ |z.2| ≤ centralOuterY ∧
    (centralInnerX ≤ |z.1| ∨ centralInnerY ≤ |z.2|)

def centralAvoidChild (σ : ℝ) (z : ℝ×ℝ) : Prop :=
  centralChildOuterX ≤ |z.1-σ*sourceOffset| ∨ centralChildOuterY ≤ |z.2| ∨
    (|z.1-σ*sourceOffset| ≤ centralChildInnerX ∧ |z.2| ≤ centralChildInnerY)

lemma centralParentStrip_mem {z : ℝ×ℝ} :
    (∃ i,z∈(centralParentStrip i).carrier) ↔ centralParentFootprint z := by
  simp only [centralParentStrip,Fin.exists_fin_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.exists_fin_zero,or_false,RectFootprint.carrier,mem_prod,mem_Icc,
    centralParentFootprint,abs_le,le_abs]
  have hx : 0 ≤ centralInnerX ∧ centralInnerX ≤ centralOuterX := by
    norm_num [centralInnerX,centralOuterX,sourceLength,sourceHole,sourceRadialWidth,centralThickness]
  have hy : 0 ≤ centralInnerY ∧ centralInnerY ≤ centralOuterY := by
    norm_num [centralInnerY,centralOuterY,sourceHole,sourceRadialWidth,centralThickness]
  constructor
  · rintro (h|h|h|h)
    · exact ⟨⟨by linarith [h.1.1],h.1.2⟩,h.2,Or.inl (Or.inl h.1.1)⟩
    · exact ⟨h.1,⟨by linarith [h.2.1],h.2.2⟩,Or.inr (Or.inl h.2.1)⟩
    · exact ⟨⟨h.1.1,by linarith [h.1.2]⟩,h.2,Or.inl (Or.inr (by linarith [h.1.2]))⟩
    · exact ⟨h.1,⟨h.2.1,by linarith [h.2.2]⟩,Or.inr (Or.inr (by linarith [h.2.2]))⟩
  · intro hp
    rcases hp.2.2 with (h|h)|(h|h)
    · left; exact ⟨⟨h,hp.1.2⟩,hp.2.1⟩
    · right; right; left; exact ⟨⟨hp.1.1,by linarith⟩,hp.2.1⟩
    · right; left; exact ⟨hp.1,⟨h,hp.2.1.2⟩⟩
    · right; right; right; exact ⟨hp.1,⟨hp.2.1.1,by linarith⟩⟩

lemma centralChildOption_mem {σ : ℝ} {z : ℝ×ℝ}
    (hbox : |z.1| ≤ centralOuterX ∧ |z.2| ≤ centralOuterY) :
    (∃ k,z∈(centralChildOption σ k).carrier) ↔ centralAvoidChild σ z := by
  simp only [centralChildOption,Fin.exists_fin_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.exists_fin_zero,or_false,RectFootprint.carrier,mem_prod,mem_Icc,
    centralAvoidChild,abs_le,le_abs]
  have hx := abs_le.mp hbox.1
  have hy := abs_le.mp hbox.2
  constructor
  · rintro (h|h|h|h|h)
    · exact Or.inl (Or.inl (by linarith [h.1.1]))
    · exact Or.inr (Or.inl (Or.inl h.2.1))
    · exact Or.inl (Or.inr (by linarith [h.1.2]))
    · exact Or.inr (Or.inl (Or.inr (by linarith [h.2.2])))
    · exact Or.inr (Or.inr ⟨⟨by linarith [h.1.1],by linarith [h.1.2]⟩,h.2⟩)
  · rintro ((h|h)|(h|h)|h)
    · exact Or.inl ⟨⟨by linarith,hx.2⟩,hy⟩
    · exact Or.inr (Or.inr (Or.inl ⟨⟨hx.1,by linarith⟩,hy⟩))
    · exact Or.inr (Or.inl ⟨hx,⟨h,hy.2⟩⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hx,⟨hy.1,by linarith⟩⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨by linarith [h.1.1],by linarith [h.1.2]⟩,h.2⟩)))

def centralColumn (i : Fin 4) (j k : Fin 5) : RectFootprint :=
  ((centralParentStrip i).inter (centralChildOption 1 j)).inter (centralChildOption (-1) k)

lemma centralColumn_cover {z : ℝ×ℝ} :
    (∃ i j k,z∈(centralColumn i j k).carrier) ↔
      centralParentFootprint z ∧ centralAvoidChild 1 z ∧ centralAvoidChild (-1) z := by
  simp only [centralColumn,RectFootprint.inter_carrier,mem_inter_iff]
  constructor
  · rintro ⟨i,j,k,⟨hp,hj⟩,hk⟩
    have hh := centralParentStrip_mem.mp ⟨i,hp⟩
    exact ⟨hh,(centralChildOption_mem ⟨hh.1,hh.2.1⟩).mp ⟨j,hj⟩,
      (centralChildOption_mem ⟨hh.1,hh.2.1⟩).mp ⟨k,hk⟩⟩
  · rintro ⟨hp,hj,hk⟩
    obtain ⟨i,hi⟩ := centralParentStrip_mem.mpr hp
    obtain ⟨j,hj⟩ := (centralChildOption_mem ⟨hp.1,hp.2.1⟩).mpr hj
    obtain ⟨k,hk⟩ := (centralChildOption_mem ⟨hp.1,hp.2.1⟩).mpr hk
    exact ⟨i,j,k,⟨hi,hj⟩,hk⟩

def centralClosed : Set Box3 := {z | centralParentFootprint z.1 ∧ |z.2| ≤ centralHeight ∧
  (centralChildHeight ≤ |z.2| ∨ (centralAvoidChild 1 z.1 ∧ centralAvoidChild (-1) z.1))}

def centralTop (i : Fin 4) : Set Box3 :=
  (centralParentStrip i).prism centralChildHeight centralHeight

def centralBottom (i : Fin 4) : Set Box3 :=
  (centralParentStrip i).prism (-centralHeight) (-centralChildHeight)

theorem centralClosed_cover : centralClosed =
    (⋃ i,centralTop i) ∪ (⋃ i,centralBottom i) ∪
      ⋃ i : Fin 4,⋃ j : Fin 5,⋃ k : Fin 5,(centralColumn i j k).prism (-centralHeight) centralHeight := by
  ext z
  simp only [centralClosed,mem_ofPred_eq,mem_union,mem_iUnion,centralTop,centralBottom,
    RectFootprint.prism,mem_prod,mem_Icc]
  constructor
  · rintro ⟨hp,hz,ht|⟨hj,hk⟩⟩
    · obtain ⟨i,hi⟩ := centralParentStrip_mem.mpr hp
      have hb := abs_le.mp hz
      rcases le_abs.mp ht with h|h
      · exact Or.inl (Or.inl ⟨i,hi,h,hb.2⟩)
      · exact Or.inl (Or.inr ⟨i,hi,hb.1,by linarith⟩)
    · obtain ⟨i,j,k,hh⟩ := centralColumn_cover.mpr ⟨hp,hj,hk⟩
      exact Or.inr ⟨i,j,k,hh,abs_le.mp hz⟩
  · rintro ((⟨i,hi,hz⟩|⟨i,hi,hz⟩)|⟨i,j,k,hi,hz⟩)
    · refine ⟨centralParentStrip_mem.mp ⟨i,hi⟩,abs_le.mpr ⟨?_,hz.2⟩,Or.inl (le_abs.mpr (Or.inl hz.1))⟩
      have hh : 0 ≤ centralChildHeight+centralHeight := by norm_num [centralChildHeight,centralHeight,sourceScale,centralThickness]
      linarith
    · refine ⟨centralParentStrip_mem.mp ⟨i,hi⟩,abs_le.mpr ⟨hz.1,?_⟩,Or.inl (le_abs.mpr (Or.inr (by linarith [hz.2])))⟩
      have hh : 0 ≤ centralChildHeight+centralHeight := by norm_num [centralChildHeight,centralHeight,sourceScale,centralThickness]
      linarith
    · have hh := centralColumn_cover.mp ⟨i,j,k,hi⟩
      exact ⟨hh.1,abs_le.mpr hz,Or.inr hh.2⟩

end ScalarConductivity

end

end OAI
