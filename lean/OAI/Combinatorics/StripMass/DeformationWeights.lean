import Mathlib
import OAI.Combinatorics.StripMass.HoneycombDictionary
import OAI.Combinatorics.StripMass.MonicPositive
import OAI.Combinatorics.StripMass.AugmentedColumn

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix _root_.OAI.Matrix Set
open scoped BigOperators Classical

lemma lambda_pos : 0<lambda := by unfold lambda; positivity

lemma L_deformation_pos {t : ℝ} (ht : t∈Icc 0 lambda) : 0<L (3*lambda-t) := by
  unfold L
  apply mul_pos <;> apply Real.sin_pos_of_pos_of_lt_pi <;>
    unfold lambda at * <;> linarith [ht.1,ht.2,Real.pi_pos]

lemma physicalWeights_deformation_pos {t : ℝ} (ht : t∈Ioc 0 lambda) :
    0<(physicalWeights (3*lambda-t)).A ∧ 0<(physicalWeights (3*lambda-t)).B ∧
      0<(physicalWeights (3*lambda-t)).U := by
  have hL:=L_deformation_pos ⟨ht.1.le,ht.2⟩
  have hd : 0<Real.cos (2*lambda) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> unfold lambda <;> linarith [Real.pi_pos]
  have ht₀ : 0<Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (ht.2.trans_lt (by unfold lambda; linarith [Real.pi_pos]))
  have hs : 0<Real.sin (3*lambda-t) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> unfold lambda at * <;> linarith [ht.1,ht.2,Real.pi_pos]
  unfold physicalWeights
  dsimp only
  rw [show 3*lambda-(3*lambda-t)=t by ring]
  exact ⟨div_pos (mul_pos hd ht₀) hL,div_pos (mul_pos hs ht₀) hL,div_pos (mul_pos hd hs) hL⟩

lemma physicalWeights_deformation_tile_nonneg {t : ℝ} (ht : t∈Icc 0 lambda)
    (s : Tile) (hs : ¬s.Occupied 0) : 0<(physicalWeights (3*lambda-t)).U ∧
      0≤(physicalWeights (3*lambda-t)).tile s := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht₀
  · rw [sub_zero,physicalWeights_three_lambda]
    constructor
    · norm_num [deletionWeights]
    · cases s <;> norm_num [deletionWeights,Weights.tile]
  · obtain ⟨hA,hB,hU⟩:=physicalWeights_deformation_pos ⟨ht₀,ht.2⟩
    refine ⟨hU,?_⟩
    cases s <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges,Weights.tile]
    any_goals positivity

lemma physicalWeights_two_lambda_nonneg (s : Tile) : 0≤(physicalWeights (2*lambda)).tile s := by
  rw [physicalWeights_two_lambda]
  have hrho : 0<rho := by unfold rho; positivity
  cases s <;> simp only [Weights.tile] <;> positivity

lemma physicalWeights_two_lambda_pos :
    0<(physicalWeights (2*lambda)).A ∧ 0<(physicalWeights (2*lambda)).B ∧
      0<(physicalWeights (2*lambda)).U := by
  have hh:=physicalWeights_deformation_pos (t:=lambda) ⟨lambda_pos,le_rfl⟩
  simpa only [show 3*lambda-lambda=2*lambda by ring] using hh

lemma northInjection_nonneg (s : Tile) : 0≤(northInjectionWeights : Weights ℝ).tile s := by
  cases s <;> norm_num [northInjectionWeights,Weights.tile]

 
def augmentedPhysicalWeights (n : ℕ) : Fin (n+1) → Weights ℝ :=
  Fin.snoc (fun _ : Fin n=>physicalWeights (2*lambda)) northInjectionWeights

def deformationAngles (n : ℕ) (t : ℝ) : Fin (n+1) → ℝ := Fin.cons t (fun _=>lambda)

def deformationWeights (n : ℕ) (t : ℝ) : Fin (n+1+1) → Weights ℝ :=
  Fin.cons (physicalWeights (3*lambda-t)) (augmentedPhysicalWeights n)

lemma deformationWeights_eq (n : ℕ) (t : ℝ) :
    deformationWeights n t=Fin.snoc
      (fun i=>physicalWeights (3*lambda-deformationAngles n t i)) northInjectionWeights := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · change physicalWeights (3*lambda-t)=
      (Fin.snoc (fun i : Fin (n+1)=>physicalWeights (3*lambda-deformationAngles n t i))
        northInjectionWeights : Fin (n+1+1) → Weights ℝ) ((0 : Fin (n+1)).castSucc)
    rw [Fin.snoc_castSucc]
    rfl
  · rw [deformationWeights,Fin.cons_succ]
    refine Fin.lastCases ?_ (fun j=>?_) j
    · rw [augmentedPhysicalWeights,Fin.snoc_last,Fin.succ_last,Fin.snoc_last]
    · rw [augmentedPhysicalWeights,Fin.snoc_castSucc,Fin.succ_castSucc,Fin.snoc_castSucc]
      simp only [deformationAngles,Fin.cons_succ,show 3*lambda-lambda=2*lambda by ring]

lemma deformationWeights_physical (n : ℕ) : deformationWeights n lambda=augmentedPhysicalWeights (n+1) := by
  rw [deformationWeights_eq]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;>
    simp only [deformationAngles,Fin.cons_zero,Fin.cons_succ,show 3*lambda-lambda=2*lambda by ring]

lemma deformationWeights_flat (n : ℕ) : deformationWeights n 0 0=deletionWeights := by
  simp [deformationWeights,physicalWeights_three_lambda]

lemma augmentedPhysical_tile_nonneg (n : ℕ) (i : Fin (n+1)) (s : Tile) :
    0≤(augmentedPhysicalWeights n i).tile s := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simpa only [augmentedPhysicalWeights,Fin.snoc_last] using northInjection_nonneg s
  · simpa only [augmentedPhysicalWeights,Fin.snoc_castSucc] using physicalWeights_two_lambda_nonneg s

lemma deformationWeights_nonnegative (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    ColumnNonnegative (deformationWeights n t) := by
  intro p q s hs
  apply Finset.prod_nonneg
  intro i _
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (physicalWeights_deformation_tile_nonneg ht (s 0) (hs.south 0 rfl)).2
  · exact augmentedPhysical_tile_nonneg n j (s j.succ)

lemma deformationWeights_accessible (n : ℕ) {t : ℝ} (ht : t∈Ioc 0 lambda) :
    PositiveMatrix.Accessible (restrictedColumn (deformationWeights n t))
      (injectionColumn (deformationWeights n t)) := by
  apply column_accessible _ (deformationWeights_nonnegative n ⟨ht.1.le,ht.2⟩)
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (physicalWeights_deformation_pos ht).1
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · norm_num [deformationWeights,augmentedPhysicalWeights,northInjectionWeights]
      · simpa only [deformationWeights,Fin.cons_succ,augmentedPhysicalWeights,Fin.snoc_castSucc]
          using physicalWeights_two_lambda_pos.1
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (physicalWeights_deformation_pos ht).2.1
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · norm_num [deformationWeights,augmentedPhysicalWeights,northInjectionWeights]
      · simpa only [deformationWeights,Fin.cons_succ,augmentedPhysicalWeights,Fin.snoc_castSucc]
          using physicalWeights_two_lambda_pos.2.1
  · intro i hi
    revert hi
    refine Fin.cases ?_ (fun j=>?_) i
    · intro _; exact (physicalWeights_deformation_pos ht).2.2
    · revert j
      apply Fin.lastCases
      · intro hh
        simp only [Fin.val_succ,Fin.val_last] at hh
        omega
      · intro j _
        simpa only [deformationWeights,Fin.cons_succ,augmentedPhysicalWeights,Fin.snoc_castSucc]
          using physicalWeights_two_lambda_pos.2.2

lemma deformationAngles_scalar_ne_zero (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    angleScalar (deformationAngles n t)≠0 := by
  rw [angleScalar,angleEvaluation_scalar]
  have he : (fun i=>(Real.cos (2*deformationAngles n t i-3*lambda):ℂ))=
      Fin.cons (Real.cos (2*t-3*lambda):ℂ) (fun _ : Fin n=>(C:ℂ)) := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · simp only [deformationAngles,Fin.cons_succ,show 2*lambda-3*lambda= -lambda by ring,Real.cos_neg,C]
  rw [he]
  have hg:=scalarValue_extract (RingHom.id ℂ)
    (Fin.snoc (fun _ : Fin n=>(C:ℂ)) (Real.cos (2*t-3*lambda):ℂ)) (Fin.last n)
  simp only [Fin.snoc_last,Fin.succAbove_last,Fin.snoc_castSucc] at hg
  rw [←hg]
  exact scalarValue_deformation_ne_zero n (cosine_deformation ht)

lemma deformationAngles_L_ne_zero (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda)
    (i : Fin (n+1)) : L (3*lambda-deformationAngles n t i)≠0 := by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (L_deformation_pos ht).ne'
  · exact (L_deformation_pos (t:=lambda) ⟨lambda_pos.le,le_rfl⟩).ne'

lemma deformationWeights_stationary (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    (restrictedColumn (deformationWeights n t)).mulVec (fun p=>angleAugmented (deformationAngles n t) p.val)+
      injectionColumn (deformationWeights n t)=fun p=>angleAugmented (deformationAngles n t) p.val := by
  rw [deformationWeights_eq]
  exact angleAugmented_restricted_stationary _ (deformationAngles_L_ne_zero n ht)
    (deformationAngles_scalar_ne_zero n ht)


 

 


lemma continuousOn_column {α : Type*} [TopologicalSpace α] {S : Set α} {n : ℕ}
    (w : α → Fin n → Weights ℝ) (hw : ∀i s,ContinuousOn (fun t=>(w t i).tile s) S) :
    ContinuousOn (fun t=>column (w t)) S := by
  apply continuousOn_pi.mpr
  intro p
  apply continuousOn_pi.mpr
  intro q
  unfold column
  apply continuousOn_finsetSum
  intro s _
  by_cases hs : Realizes q p s
  · simp only [ite_eq_left hs]
    exact continuousOn_finsetProd _ (fun i _=>hw i (s i))
  · simp only [ite_eq_right hs]
    exact continuousOn_const

lemma continuousOn_deformationWeights_tile (n : ℕ) (i : Fin (n+1+1)) (s : Tile) :
    ContinuousOn (fun t=>(deformationWeights n t i).tile s) (Icc 0 lambda) := by
  refine Fin.cases ?_ (fun j=>?_) i
  · change ContinuousOn (fun t=>(physicalWeights (3*lambda-t)).tile s) (Icc 0 lambda)
    cases s <;> simp only [physicalWeights,Weights.tile]
    · exact continuousOn_const
    all_goals
      apply ContinuousOn.div
      · fun_prop
      · unfold L; fun_prop
      · exact fun t ht=>(L_deformation_pos ht).ne'
  · change ContinuousOn (fun _ : ℝ=>(augmentedPhysicalWeights n j).tile s) (Icc 0 lambda)
    exact continuousOn_const

lemma continuousOn_deformationColumn (n : ℕ) :
    ContinuousOn (fun t=>restrictedColumn (deformationWeights n t)) (Icc 0 lambda) := by
  have hh:=continuousOn_column (deformationWeights n) (continuousOn_deformationWeights_tile n)
  apply continuousOn_pi.mpr
  intro p
  apply continuousOn_pi.mpr
  intro q
  exact continuousOn_pi.mp (continuousOn_pi.mp hh p.val) q.val

lemma continuous_deformationAngles (n : ℕ) : Continuous (deformationAngles n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_id
  · exact continuous_const

lemma continuousOn_deformationVector (n : ℕ) :
    ContinuousOn (fun t=>fun p : NonemptyPairing (n+1+1)=>angleAugmented (deformationAngles n t) p.val)
      (Icc 0 lambda) := by
  have hc:=continuousOn_angleAugmented (S:=deformationAngles n '' Icc 0 lambda) (by
    rintro u ⟨t,ht,rfl⟩
    exact deformationAngles_scalar_ne_zero n ht)
  have hh:=hc.comp (continuous_deformationAngles n).continuousOn (fun t ht=>⟨t,ht,rfl⟩)
  apply continuousOn_pi.mpr
  intro p
  exact continuousOn_pi.mp hh p.val

lemma summablePowers_flat_bottom {n : ℕ} (w : Fin (n+1) → Weights ℝ)
    (hzero : w 0=deletionWeights) (hw : ColumnNonnegative w)
    (hs : PositiveMatrix.SummablePowers (restrictedColumn (fun i=>w i.succ))) :
    PositiveMatrix.SummablePowers (restrictedColumn w) := by
  let e:=Pairing.nonemptyBottomSplit n
  apply (PositiveMatrix.summablePowers_reindex_iff _ e).mp
  apply PositiveMatrix.summablePowers_of_zero_cols
  · exact fun i j=>hw.restricted (e i) (e j)
  · have he : ((restrictedColumn w).submatrix e e).toBlocks₁₁=
        restrictedColumn (fun i=>w i.succ) := by
      ext q p
      exact column_padBottom w p.val q.val
    rw [he]
    exact hs
  · intro i p
    exact column_deletion_bottom_col w hzero p.val.val (e i).val (not_not.mp p.property)

 

theorem augmentedPhysical_summablePowers (n : ℕ) :
    PositiveMatrix.SummablePowers (restrictedColumn (augmentedPhysicalWeights n)) := by
  induction n with
  | zero =>
    intro p
    exact (p.property (Pairing.eq_empty_of_le_one (by omega) p.val)).elim
  | succ n ih =>
    rw [←deformationWeights_physical]
    apply PositiveMatrix.summablePowers_on_Icc
      (fun t=>restrictedColumn (deformationWeights n t))
      (fun t=>injectionColumn (deformationWeights n t))
      (fun t=>fun p=>angleAugmented (deformationAngles n t) p.val)
      lambda_pos.le (continuousOn_deformationColumn n) (continuousOn_deformationVector n)
      (fun t ht=>(deformationWeights_nonnegative n ht).restricted)
      (fun t ht=>(deformationWeights_nonnegative n ht).injection)
      (fun t ht=>deformationWeights_stationary n ht)
      ?_ (fun t ht=>deformationWeights_accessible n ht)
      lambda ⟨lambda_pos.le,le_rfl⟩
    apply summablePowers_flat_bottom _ (deformationWeights_flat n)
      (deformationWeights_nonnegative n ⟨le_rfl,lambda_pos.le⟩)
    simpa only [deformationWeights,Fin.cons_succ] using ih

end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip.PositiveMatrix
noncomputable section
open _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators Classical

variable {ι κ : Type*}

lemma Nonnegative.submatrix [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) (e : κ → ι) :
    Nonnegative (Q.submatrix e e) := fun i j=>hQ (e i) (e j)

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma submatrix_pow_le {Q : Matrix ι ι ℝ} (hQ : Nonnegative Q) (e : κ ↪ ι) (k : ℕ) :
    ∀i j,((Q.submatrix e e)^k) i j≤(Q^k) (e i) (e j) := by
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero,Matrix.one_apply,EmbeddingLike.apply_eq_iff_eq]
    exact le_rfl
  | succ k ih =>
    intro i j
    rw [pow_succ,pow_succ]
    calc
      _ ≤ ∑l : κ,(Q^k) (e i) (e l)*Q (e l) (e j) :=
        Finset.sum_le_sum fun l _=>mul_le_mul_of_nonneg_right (ih i l) (hQ (e l) (e j))
      _ = ∑l∈Finset.univ.map e,(Q^k) (e i) l*Q l (e j) := by rw [Finset.sum_map]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun l _ _=>mul_nonneg (hQ.pow k _ _) (hQ _ _))

lemma SummablePowers.submatrix {Q : Matrix ι ι ℝ} (hs : SummablePowers Q)
    (hQ : Nonnegative Q) (e : κ ↪ ι) : SummablePowers (Q.submatrix e e) := by
  intro i j
  apply (hs (e i) (e j)).of_nonneg_of_le
  · intro k
    exact (hQ.submatrix e).pow k i j
  · intro k
    exact submatrix_pow_le hQ e k i j

lemma SummablePowers.transpose {Q : Matrix ι ι ℝ} (hs : SummablePowers Q) :
    SummablePowers Q.transpose := by
  intro i j
  simpa only [←Matrix.transpose_pow,Matrix.transpose_apply] using hs j i

lemma summablePowers_of_zero_rows (M : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ)
    (hM : Nonnegative M) (hs : SummablePowers M.toBlocks₁₁)
    (hz : ∀i j,M (.inr i) j=0) : SummablePowers M := by
  have ht : SummablePowers M.transpose := by
    apply summablePowers_of_zero_cols
    · exact fun i j=>hM j i
    · exact hs.transpose
    · intros; apply hz
  simpa only [Matrix.transpose_transpose] using ht.transpose

end
end CriticalStrip.PositiveMatrix

 

 

namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators Classical

lemma augmentedPhysical_nonnegative (n : ℕ) : ColumnNonnegative (augmentedPhysicalWeights n) := by
  intro p q s hs
  exact Finset.prod_nonneg fun i _=>augmentedPhysical_tile_nonneg n i (s i)

 

def vacuumAugmentEmbedding (n : ℕ) : NonemptyPairing n ↪ NonemptyPairing (n+1) :=
  (Function.Embedding.trans (.inl) (sourceTopSplit n).toEmbedding)

def sourceAugmentEmbedding (n : ℕ) : SourcePairing n ↪ NonemptyPairing (n+1) :=
  (Function.Embedding.trans (.inr) (sourceTopSplit n).toEmbedding)

lemma augmentedPhysical_vacuum_block (n : ℕ) :
    (restrictedColumn (augmentedPhysicalWeights n)).submatrix
      (vacuumAugmentEmbedding n) (vacuumAugmentEmbedding n)=
      restrictedColumn (fun _ : Fin n=>physicalWeights (2*lambda)) := by
  ext q p
  simpa only [augmentedPhysicalWeights,Fin.snoc_castSucc,restrictedColumn,Matrix.submatrix_apply,
    vacuumAugmentEmbedding,Function.Embedding.trans_apply,Equiv.coe_toEmbedding,Function.Embedding.inl_apply,
    sourceTopSplit_inl,Pairing.nonemptyPadTop] using
    column_padTop (augmentedPhysicalWeights n) p.val q.val

lemma augmentedPhysical_source_block (n : ℕ) :
    (restrictedColumn (augmentedPhysicalWeights n)).submatrix
      (sourceAugmentEmbedding n) (sourceAugmentEmbedding n)=
      sourceTransfer (fun _ : Fin n=>(physicalWeights (2*lambda)).tile) := by
  ext q p
  have hh:=congrFun (congrFun (northInjection_column_blocks
    (fun _ : Fin n=>physicalWeights (2*lambda))) (.inr q)) (.inr p)
  exact hh

theorem physical_vacuum_summablePowers (n : ℕ) :
    PositiveMatrix.SummablePowers (restrictedColumn (fun _ : Fin n=>physicalWeights (2*lambda))) := by
  have hh := (augmentedPhysical_summablePowers n).submatrix
    (augmentedPhysical_nonnegative n).restricted (vacuumAugmentEmbedding n)
  rw [augmentedPhysical_vacuum_block] at hh
  exact hh

theorem physical_source_summablePowers (n : ℕ) :
    PositiveMatrix.SummablePowers (sourceTransfer (fun _ : Fin n=>(physicalWeights (2*lambda)).tile)) := by
  have hh := (augmentedPhysical_summablePowers n).submatrix
    (augmentedPhysical_nonnegative n).restricted (sourceAugmentEmbedding n)
  rw [augmentedPhysical_source_block] at hh
  exact hh

lemma physical_column_nonnegative (n : ℕ) :
    ColumnNonnegative (fun _ : Fin n=>physicalWeights (2*lambda)) := by
  intro p q s hs
  exact Finset.prod_nonneg fun i _=>physicalWeights_two_lambda_nonneg (s i)

lemma physical_source_nonnegative (n : ℕ) :
    PositiveMatrix.Nonnegative (sourceTransfer (fun _ : Fin n=>(physicalWeights (2*lambda)).tile)) := by
  rw [←augmentedPhysical_source_block]
  exact (augmentedPhysical_nonnegative n).restricted.submatrix _

lemma homogeneous_angleScalar_ne_zero (n : ℕ) : angleScalar (fun _ : Fin n=>lambda)≠0 := by
  rw [angleScalar,angleEvaluation_scalar]
  simpa only [show 2*lambda-3*lambda= -lambda by ring,Real.cos_neg,C] using
    scalarValue_homogeneous_ne_zero n

lemma homogeneous_L_ne_zero : L (3*lambda-lambda)≠0 :=
  (L_deformation_pos (t:=lambda) ⟨lambda_pos.le,le_rfl⟩).ne'

 

theorem physical_vacuum_eq_tsum (n : ℕ) (p : NonemptyPairing n) :
    angleVacuum (fun _ : Fin n=>lambda) p.val=
      ∑' k : ℕ,((restrictedColumn (fun _ : Fin n=>physicalWeights (2*lambda)))^k).mulVec
        (injectionColumn (fun _ : Fin n=>physicalWeights (2*lambda))) p := by
  apply (physical_vacuum_summablePowers n).stationary_eq_tsum (w:=fun q=>angleVacuum (fun _ : Fin n=>lambda) q.val) (i:=p)
  simpa only [show 3*lambda-lambda=2*lambda by ring] using
    angleVacuum_restricted_stationary (fun _ : Fin n=>lambda) (fun _=>homogeneous_L_ne_zero)
      (homogeneous_angleScalar_ne_zero n)

theorem physical_vacuum_nonneg (n : ℕ) (p : Pairing n) :
    0≤angleVacuum (fun _ : Fin n=>lambda) p := by
  by_cases hp : p=empty n
  · rw [hp,angleVacuum_empty _ (homogeneous_angleScalar_ne_zero n)]
    exact zero_le_one
  · rw [physical_vacuum_eq_tsum n ⟨p,hp⟩]
    exact tsum_nonneg fun k=>(physical_column_nonnegative n).restricted.pow k |>.mulVec
      (physical_column_nonnegative n).injection _

 

theorem physical_northSource_eq_tsum (n : ℕ) (p : SourcePairing n) :
    angleNorthSource (fun _ : Fin n=>lambda) p=
      ∑' k : ℕ,((sourceTransfer (fun _ : Fin n=>(physicalWeights (2*lambda)).tile))^k).mulVec
        ((northSource (fun _ : Fin n=>(physicalWeights (2*lambda)).tile)).mulVec
          (angleVacuum (fun _ : Fin n=>lambda))) p := by
  apply (physical_source_summablePowers n).stationary_eq_tsum
  simpa only [show 3*lambda-lambda=2*lambda by ring] using
    angleNorthSource_stationary (fun _ : Fin n=>lambda) (fun _=>homogeneous_L_ne_zero)

 

theorem physical_source_weighted_summable (n d : ℕ) (p q : SourcePairing n) :
    Summable (fun k : ℕ=>(k:ℝ)^d*
      ((sourceTransfer (fun _ : Fin n=>(physicalWeights (2*lambda)).tile))^k) p q) :=
  (physical_source_summablePowers n).weighted (physical_source_nonnegative n) d p q

end
end CriticalStrip.Diagram

end OAI
