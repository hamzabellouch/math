import Mathlib
import OAI.Analysis.Conductivity.Geometry.RectanglePoincare

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory

lemma centralClosed_compact : IsCompact centralClosed := by
  rw [centralClosed_cover]
  exact ((isCompact_iUnion (fun i : Fin 4 => (centralParentStrip i).prism_compact _ _)).union
    (isCompact_iUnion (fun i : Fin 4 => (centralParentStrip i).prism_compact _ _))).union
    (isCompact_iUnion (fun i : Fin 4 => isCompact_iUnion (fun j : Fin 5 =>
      isCompact_iUnion (fun k : Fin 5 => (centralColumn i j k).prism_compact _ _))))

lemma centralTop_subset (i : Fin 4) : centralTop i⊆centralClosed := by
  rw [centralClosed_cover]
  exact (subset_iUnion (fun i => centralTop i) i).trans (subset_union_left.trans subset_union_left)

lemma centralBottom_subset (i : Fin 4) : centralBottom i⊆centralClosed := by
  rw [centralClosed_cover]
  exact (subset_iUnion (fun i => centralBottom i) i).trans (subset_union_right.trans subset_union_left)

lemma centralColumn_subset (i : Fin 4) (j k : Fin 5) :
    (centralColumn i j k).prism (-centralHeight) centralHeight⊆centralClosed := by
  intro z hz
  rw [centralClosed_cover]
  exact Or.inr (mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨j,mem_iUnion.mpr ⟨k,hz⟩⟩⟩)

def centralConnector : RectFootprint := ⟨3/2,centralOuterX,-centralOuterY,centralOuterY⟩

lemma centralConnector_subset : centralConnector.prism (-centralHeight) centralHeight⊆centralClosed := by
  intro z hz
  obtain ⟨⟨hx,hy⟩,ht⟩ := hz
  have hp : centralParentFootprint z.1 := by
    apply centralParentStrip_mem.mp
    refine ⟨0,?_⟩
    change (centralInnerX ≤ z.1.1 ∧ z.1.1 ≤ centralOuterX) ∧
      -centralOuterY ≤ z.1.2 ∧ z.1.2 ≤ centralOuterY
    refine ⟨⟨?_,hx.2⟩,hy⟩
    have hh : centralInnerX ≤ 3/2 := by norm_num [centralInnerX,sourceLength,sourceHole,sourceRadialWidth,centralThickness]
    exact hh.trans hx.1
  refine ⟨hp,abs_le.mpr ht,Or.inr ⟨?_,?_⟩⟩
  all_goals
    apply Or.inl
    apply le_abs.mpr
    apply Or.inl
    change centralChildOuterX ≤ z.1.1-_
    have hh := hx.1
    change (3/2:ℝ) ≤ z.1.1 at hh
    norm_num [centralChildOuterX,sourceScale,sourceRadialWidth,sourceHole,centralThickness,sourceOffset]
    linarith

def centralAnchorData : ℕ → RectFootprint×(ℝ×ℝ)
  | 0 => (centralParentStrip 0,centralChildHeight,centralHeight)
  | 1 => (centralParentStrip 1,centralChildHeight,centralHeight)
  | 2 => (centralParentStrip 2,centralChildHeight,centralHeight)
  | 3 => (centralParentStrip 3,centralChildHeight,centralHeight)
  | 4 => (centralConnector,-centralHeight,centralHeight)
  | 5 => (centralParentStrip 0,-centralHeight,-centralChildHeight)
  | 6 => (centralParentStrip 1,-centralHeight,-centralChildHeight)
  | 7 => (centralParentStrip 2,-centralHeight,-centralChildHeight)
  | 8 => (centralParentStrip 3,-centralHeight,-centralChildHeight)
  | _ => (centralParentStrip 0,centralChildHeight,centralHeight)

def centralAnchorPiece (n : ℕ) : Set Box3 :=
  (centralAnchorData n).1.prism (centralAnchorData n).2.1 (centralAnchorData n).2.2

def centralAnchor : Set Box3 := patchCluster centralAnchorPiece 8

def centralAnchorLocalConstant (n : ℕ) : ℝ :=
  (centralAnchorData n).1.poincareConstant (centralAnchorData n).2.1 (centralAnchorData n).2.2

def centralAnchorAverage (n : ℕ) (f : Box3 → ℝ) : ℝ :=
  (centralAnchorData n).1.average (centralAnchorData n).2.1 (centralAnchorData n).2.2 f

def centralAnchorConstant : ℝ := patchPoincareConstant volume centralAnchorPiece centralAnchorLocalConstant 8

lemma centralAnchorPiece_compact (n : ℕ) : IsCompact (centralAnchorPiece n) :=
  (centralAnchorData n).1.prism_compact _ _

lemma centralAnchorPiece_subset (n : ℕ) (hn : n ≤ 8) : centralAnchorPiece n⊆centralClosed := by
  interval_cases n
  · exact centralTop_subset 0
  · exact centralTop_subset 1
  · exact centralTop_subset 2
  · exact centralTop_subset 3
  · exact centralConnector_subset
  · exact centralBottom_subset 0
  · exact centralBottom_subset 1
  · exact centralBottom_subset 2
  · exact centralBottom_subset 3

lemma RectFootprint.prism_inter (Q R : RectFootprint) (lo hi lo' hi' : ℝ) :
    Q.prism lo hi∩R.prism lo' hi'=(Q.inter R).prism (max lo lo') (min hi hi') := by
  ext z
  simp only [RectFootprint.prism,RectFootprint.inter_carrier,mem_prod,mem_Icc,
    mem_inter_iff,max_le_iff,le_min_iff]
  tauto

lemma centralAnchor_adjacent (n : ℕ) (hn : n<8) :
    0<volume.real (centralAnchorPiece n∩centralAnchorPiece (n+1)) := by
  unfold centralAnchorPiece
  rw [RectFootprint.prism_inter]
  apply RectFootprint.prism_real_pos
  all_goals
    interval_cases n <;> norm_num [centralAnchorData,centralParentStrip,centralConnector,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,
      RectFootprint.inter,centralOuterX,centralInnerX,centralOuterY,centralInnerY,
      centralHeight,centralChildHeight,sourceScale,sourceLength,sourceHole,sourceRadialWidth,
      centralThickness]

lemma centralCluster_compact (n : ℕ) : IsCompact (patchCluster centralAnchorPiece n) := by
  induction n with
  | zero => exact centralAnchorPiece_compact 0
  | succ n ih => exact ih.union (centralAnchorPiece_compact (n+1))

lemma centralCluster_subset (n : ℕ) (hn : n ≤ 8) : patchCluster centralAnchorPiece n⊆centralClosed := by
  induction n with
  | zero => exact centralAnchorPiece_subset 0 (by omega)
  | succ n ih => exact union_subset (ih (by omega)) (centralAnchorPiece_subset (n+1) hn)

lemma centralAnchor_hover (n : ℕ) (hn : n<8) :
    0<volume.real (patchCluster centralAnchorPiece n∩centralAnchorPiece (n+1)) := by
  apply (centralAnchor_adjacent n hn).trans_le
  exact measureReal_mono (inter_subset_inter_left _ (subset_patchCluster centralAnchorPiece n))
    (((centralCluster_compact n).inter (centralAnchorPiece_compact (n+1))).measure_ne_top)

lemma centralAnchorConstant_nonneg : 0 ≤ centralAnchorConstant := by
  exact patchPoincareConstant_nonneg volume centralAnchorPiece centralAnchorLocalConstant
    (fun n => (centralAnchorData n).1.poincareConstant_nonneg _ _) 8

theorem centralAnchor_poincare {f : Box3 → ℝ} (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) :
    localVariance volume centralAnchor f (centralAnchorAverage 0 f) ≤
      centralAnchorConstant*(∫ z in centralClosed,cubeEnergyDensity f z) := by
  apply connected_patch_poincare volume centralAnchorPiece centralAnchorLocalConstant
    (fun n => (centralAnchorData n).1.poincareConstant_nonneg _ _)
    (fun n => centralAnchorAverage n f) _ (integral_nonneg (cubeEnergyDensity_nonneg f)) 8
  · intro n hn; exact (centralAnchorPiece_compact n).measure_ne_top
  · exact centralAnchor_hover
  · intro n hn c
    exact ((hf.continuous.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      (centralAnchorPiece_compact n)
  · intro n hn
    exact (centralAnchorData n).1.poincare_in _ _ centralClosed_compact (centralAnchorPiece_subset n hn) hf

end ScalarConductivity

end

end OAI
