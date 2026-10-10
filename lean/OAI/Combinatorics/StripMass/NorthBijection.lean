import Mathlib
import OAI.Combinatorics.StripMass.ArchTrig
import OAI.Combinatorics.StripMass.HoneycombClip

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open scoped Classical BigOperators
open Diagram

namespace Diagram.ColumnChain
lemma read_ofFn {n m : ℕ} (h : Fin m → Configuration n) (k : Fin m) (j : Fin n) :
    read (List.ofFn h) k.val j=h k j := by
  simp only [read,List.getElem?_ofFn,k.isLt,dite_eq_left,Option.getD_some]
end Diagram.ColumnChain

namespace SewnRectangle
variable {n m : ℕ}

lemma clips_left (l r : Fin m → Configuration n) (D : HoneycombAssignment n)
    (ht : D.tile=tile (List.ofFn l) (List.ofFn r)) : D.leftClip m=l := by
  funext k j
  change D.tile (-1-(k.val:ℤ),j.val)=l k j
  rw [ht,tile_left,ColumnChain.read_ofFn]

lemma clips_right (l r : Fin m → Configuration n) (D : HoneycombAssignment n)
    (ht : D.tile=tile (List.ofFn l) (List.ofFn r)) : D.rightClip m=r := by
  funext k j
  change (D.tile ((k.val:ℤ),j.val)).horizontal=r k j
  rw [ht,tile_right,ColumnChain.read_ofFn,Tile.horizontal_involutive]

lemma fits_ofFn (l r : Fin m → Configuration n) (D : HoneycombAssignment n)
    (ht : D.tile=tile (List.ofFn l) (List.ofFn r)) : D.Fits m := by
  intro q hq
  rw [ht] at hq
  have hh:=tile_nonvacant_bounds _ _ q hq
  simp only [List.length_ofFn] at hh
  exact ⟨hh.1,hh.2.1⟩
end SewnRectangle

 

structure CrossTopArch (N : ℕ) where
  left : ℕ
  right : ℕ
  arch : TopArchConfiguration N (-1-(left:ℤ)) right

namespace CrossTopArch
variable {N : ℕ}

@[ext] lemma ext {D E : CrossTopArch N} (h : D.arch.tile=E.arch.tile) : D=E := by
  have hl := (D.arch.top (-1-(D.left:ℤ))).mpr (Or.inl rfl)
  have hr := (D.arch.top D.right).mpr (Or.inr rfl)
  rw [h,E.arch.top] at hl hr
  have h₁ : D.left=E.left := by omega
  have h₂ : D.right=E.right := by omega
  cases D with
  | mk l r D =>
    cases E with
    | mk l' r' E =>
      dsimp at h₁ h₂; subst l' r'
      congr 1
      exact TopArchConfiguration.ext (HoneycombAssignment.ext h)

def Fits (D : CrossTopArch N) (m : ℕ) : Prop := D.arch.toHoneycombAssignment.Fits m

def weight (D : CrossTopArch N) : ℝ := D.arch.toHoneycombAssignment.weight

lemma exists_fits (D : CrossTopArch N) (hN : 1≤N) : ∃m,D.Fits m :=
  D.arch.toHoneycombAssignment.exists_fits (D.arch.tileSupport_finite hN (by omega))

 
abbrev Bounded (N m : ℕ) := {D : CrossTopArch N // D.Fits m}

end CrossTopArch

 

structure NorthHistory (N m : ℕ) where
  left : Fin m → Configuration (N+1)
  right : Fin m → Configuration (N+1)
  nzleft : ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn left)≠0
  nzright : ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn right)≠0
  realizes : ∃p q : Pairing (N+1),
    ColumnChain.Runs (empty (N+1)) (List.ofFn left) p ∧
    ColumnChain.Runs (empty (N+1)) (List.ofFn right) q ∧ p.GluesAt (Fin.last N) q

namespace NorthHistory
variable {N m : ℕ}

@[ext] lemma ext {D E : NorthHistory N m} (hl : D.left=E.left) (hr : D.right=E.right) : D=E := by
  cases D; cases E; cases hl; cases hr; rfl

instance : Fintype (NorthHistory N m) := Fintype.ofInjective
  (fun D=>(D.left,D.right)) (fun _ _ h=>ext (congrArg Prod.fst h) (congrArg Prod.snd h))

def leftState (h : NorthHistory N m) : Pairing (N+1) := Classical.choose h.realizes

def rightState (h : NorthHistory N m) : Pairing (N+1) :=
  Classical.choose (Classical.choose_spec h.realizes)

lemma runs_left (h : NorthHistory N m) :
    ColumnChain.Runs (empty (N+1)) (List.ofFn h.left) h.leftState :=
  (Classical.choose_spec (Classical.choose_spec h.realizes)).1

lemma runs_right (h : NorthHistory N m) :
    ColumnChain.Runs (empty (N+1)) (List.ofFn h.right) h.rightState :=
  (Classical.choose_spec (Classical.choose_spec h.realizes)).2.1

lemma glues (h : NorthHistory N m) : h.leftState.GluesAt (Fin.last N) h.rightState :=
  (Classical.choose_spec (Classical.choose_spec h.realizes)).2.2

lemma shape_left_exists (h : NorthHistory N m) : ∃kl : ℕ×ℕ,
    (List.ofFn h.left).map (fun t=>t (Fin.last N))=
      List.replicate kl.1 Tile.diagonal₁ ++ Tile.vertical₀::List.replicate kl.2 Tile.vacant := by
  obtain ⟨k,l,hh⟩ := (ColumnChain.north_shape (fun _ : Fin N=>physicalWeights (2*Diagram.lambda))
    (List.ofFn h.left) h.leftState h.runs_left h.nzleft).1 h.glues.1
  exact ⟨(k,l),hh⟩

lemma shape_right_exists (h : NorthHistory N m) : ∃kl : ℕ×ℕ,
    (List.ofFn h.right).map (fun t=>t (Fin.last N))=
      List.replicate kl.1 Tile.diagonal₁ ++ Tile.vertical₀::List.replicate kl.2 Tile.vacant := by
  obtain ⟨k,l,hh⟩ := (ColumnChain.north_shape (fun _ : Fin N=>physicalWeights Diagram.lambda)
    (List.ofFn h.right) h.rightState h.runs_right h.nzright).1 ((h.glues.2.1 _).mp h.glues.1)
  exact ⟨(k,l),hh⟩

def ls (h : NorthHistory N m) : ℕ×ℕ := Classical.choose h.shape_left_exists

def rs (h : NorthHistory N m) : ℕ×ℕ := Classical.choose h.shape_right_exists

lemma ls_spec (h : NorthHistory N m) :
    (List.ofFn h.left).map (fun t=>t (Fin.last N))=
      List.replicate h.ls.1 Tile.diagonal₁ ++ Tile.vertical₀::List.replicate h.ls.2 Tile.vacant :=
  Classical.choose_spec h.shape_left_exists

lemma rs_spec (h : NorthHistory N m) :
    (List.ofFn h.right).map (fun t=>t (Fin.last N))=
      List.replicate h.rs.1 Tile.diagonal₁ ++ Tile.vertical₀::List.replicate h.rs.2 Tile.vacant :=
  Classical.choose_spec h.shape_right_exists

 

def toCross (h : NorthHistory N m) (hN : 1≤N) : CrossTopArch N where
  left := h.ls.1
  right := h.rs.1
  arch := SewnRectangle.northArch (List.ofFn h.left) (List.ofFn h.right)
    h.leftState h.rightState hN h.runs_left h.runs_right h.glues h.nzleft h.nzright
    h.ls.1 h.ls.2 h.rs.1 h.rs.2 h.ls_spec h.rs_spec

lemma toCross_extend (h : NorthHistory N m) (hN : 1≤N) :
    ((h.toCross hN).arch.extend hN (by dsimp [toCross]; omega)).tile=
      SewnRectangle.tile (List.ofFn h.left) (List.ofFn h.right) := by
  exact congrArg HoneycombAssignment.tile
    (SewnRectangle.northArch_extend (List.ofFn h.left) (List.ofFn h.right)
      h.leftState h.rightState hN h.runs_left h.runs_right h.glues h.nzleft h.nzright
      h.ls.1 h.ls.2 h.rs.1 h.rs.2 h.ls_spec h.rs_spec)

lemma toCross_fits (h : NorthHistory N m) (hN : 1≤N) : (h.toCross hN).Fits m := by
  have hf := SewnRectangle.fits_ofFn h.left h.right _ (h.toCross_extend hN)
  intro q hq
  have hj : q.2<N := by
    by_contra hp
    exact hq ((h.toCross hN).arch.outside _ _ (by omega))
  apply hf q
  rw [(h.toCross hN).arch.extend_base hN _ _ _ hj]
  exact hq

 
def ofCross (D : CrossTopArch.Bounded N m) (hN : 1≤N) : NorthHistory N m where
  left := (D.val.arch.extend hN (by omega)).leftClip m
  right := (D.val.arch.extend hN (by omega)).rightClip m
  nzleft := (D.val.arch.clips_weight_ne_zero hN (by omega) (by omega) (by omega) m).1
  nzright := (D.val.arch.clips_weight_ne_zero hN (by omega) (by omega) (by omega) m).2
  realizes := D.val.arch.extend_clips_runs hN (by omega) (by omega) m D.property

lemma ofCross_toCross (h : NorthHistory N m) (hN : 1≤N) :
    ofCross ⟨h.toCross hN,h.toCross_fits hN⟩ hN=h := by
  apply ext
  · exact SewnRectangle.clips_left h.left h.right _ (h.toCross_extend hN)
  · exact SewnRectangle.clips_right h.left h.right _ (h.toCross_extend hN)

lemma toCross_ofCross (D : CrossTopArch.Bounded N m) (hN : 1≤N) :
    (ofCross D hN).toCross hN=D.val := by
  apply CrossTopArch.ext
  have he := (ofCross D hN).toCross_extend hN
  have hs := (D.val.arch.extend hN (by omega)).sewn_clips m
    (D.val.arch.extend_fits hN (by omega) D.property)
  have hh : (((ofCross D hN).toCross hN).arch.extend hN (by omega)).tile=
      (D.val.arch.extend hN (by omega)).tile := he.trans hs.symm
  funext ⟨i,j⟩
  by_cases hj : j<N
  · have hx:=congrFun hh (i,j)
    simpa only [TopArchConfiguration.extend_base _ _ _ _ _ hj] using hx
  · rw [((ofCross D hN).toCross hN).arch.outside _ _ (by omega),D.val.arch.outside _ _ (by omega)]

 

def equivCross (hN : 1≤N) : NorthHistory N m ≃ CrossTopArch.Bounded N m where
  toFun h := ⟨h.toCross hN,h.toCross_fits hN⟩
  invFun D := ofCross D hN
  left_inv h := ofCross_toCross h hN
  right_inv D := Subtype.ext (toCross_ofCross D hN)

def weight (h : NorthHistory N m) : ℝ :=
  ColumnChain.weight (SewnRectangle.leftWeights N) (List.ofFn h.left) *
  ColumnChain.weight (SewnRectangle.rightWeights N) (List.ofFn h.right)

lemma ofCross_weight (D : CrossTopArch.Bounded N m) (hN : 1≤N) :
    (ofCross D hN).weight=D.val.weight :=
  D.val.arch.clips_weight hN (by omega) (by omega) (by omega) m D.property

lemma toCross_weight (h : NorthHistory N m) (hN : 1≤N) :
    h.weight=(h.toCross hN).weight := by
  have hh := ofCross_weight ⟨h.toCross hN,h.toCross_fits hN⟩ hN
  rwa [ofCross_toCross h hN] at hh

end NorthHistory
end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators Classical

lemma augmentedReversed_nonnegative (n : ℕ) : ColumnNonnegative (augmentedReversedWeights n) := by
  intro p q s hs
  exact Finset.prod_nonneg fun i _=>augmentedReversed_tile_nonneg n i (s i)

lemma augmentedReversed_vacuum_block (n : ℕ) :
    (restrictedColumn (augmentedReversedWeights n)).submatrix
      (vacuumAugmentEmbedding n) (vacuumAugmentEmbedding n)=
      restrictedColumn (fun _ : Fin n=>physicalWeights lambda) := by
  ext q p
  simpa only [augmentedReversedWeights,Fin.snoc_castSucc,restrictedColumn,Matrix.submatrix_apply,
    vacuumAugmentEmbedding,Function.Embedding.trans_apply,Equiv.coe_toEmbedding,Function.Embedding.inl_apply,
    sourceTopSplit_inl,Pairing.nonemptyPadTop] using
    column_padTop (augmentedReversedWeights n) p.val q.val

lemma augmentedReversed_source_block (n : ℕ) :
    (restrictedColumn (augmentedReversedWeights n)).submatrix
      (sourceAugmentEmbedding n) (sourceAugmentEmbedding n)=
      sourceTransfer (fun _ : Fin n=>(physicalWeights lambda).tile) := by
  ext q p
  exact congrFun (congrFun (northInjection_column_blocks
    (fun _ : Fin n=>physicalWeights lambda)) (.inr q)) (.inr p)

theorem reversed_vacuum_summablePowers (n : ℕ) :
    PositiveMatrix.SummablePowers (restrictedColumn (fun _ : Fin n=>physicalWeights lambda)) := by
  have hh := (augmentedReversed_summablePowers n).submatrix
    (augmentedReversed_nonnegative n).restricted (vacuumAugmentEmbedding n)
  rw [augmentedReversed_vacuum_block] at hh
  exact hh

theorem reversed_source_summablePowers (n : ℕ) :
    PositiveMatrix.SummablePowers (sourceTransfer (fun _ : Fin n=>(physicalWeights lambda).tile)) := by
  have hh := (augmentedReversed_summablePowers n).submatrix
    (augmentedReversed_nonnegative n).restricted (sourceAugmentEmbedding n)
  rw [augmentedReversed_source_block] at hh
  exact hh

lemma reversed_column_nonnegative (n : ℕ) :
    ColumnNonnegative (fun _ : Fin n=>physicalWeights lambda) := by
  intro p q s hs
  exact Finset.prod_nonneg fun i _=>physicalWeights_lambda_nonneg (s i)

lemma reversed_source_nonnegative (n : ℕ) :
    PositiveMatrix.Nonnegative (sourceTransfer (fun _ : Fin n=>(physicalWeights lambda).tile)) := by
  rw [←augmentedReversed_source_block]
  exact (augmentedReversed_nonnegative n).restricted.submatrix _

lemma reversed_angleScalar_ne_zero (n : ℕ) : angleScalar (fun _ : Fin n=>2*lambda)≠0 := by
  rw [angleScalar,angleEvaluation_scalar]
  simpa only [show 2*(2*lambda)-3*lambda=lambda by ring,C] using
    scalarValue_homogeneous_ne_zero n

lemma reversed_L_ne_zero : L (3*lambda-2*lambda)≠0 := by
  rw [L_reflection]
  simpa only [show 3*lambda-lambda=2*lambda by ring] using homogeneous_L_ne_zero

theorem reversed_vacuum_eq_tsum (n : ℕ) (p : NonemptyPairing n) :
    angleVacuum (fun _ : Fin n=>2*lambda) p.val=
      ∑' k : ℕ,((restrictedColumn (fun _ : Fin n=>physicalWeights lambda))^k).mulVec
        (injectionColumn (fun _ : Fin n=>physicalWeights lambda)) p := by
  apply (reversed_vacuum_summablePowers n).stationary_eq_tsum
    (w:=fun q=>angleVacuum (fun _ : Fin n=>2*lambda) q.val) (i:=p)
  simpa only [show 3*lambda-2*lambda=lambda by ring] using
    angleVacuum_restricted_stationary (fun _ : Fin n=>2*lambda) (fun _=>reversed_L_ne_zero)
      (reversed_angleScalar_ne_zero n)

theorem reversed_vacuum_nonneg (n : ℕ) (p : Pairing n) :
    0≤angleVacuum (fun _ : Fin n=>2*lambda) p := by
  by_cases hp : p=empty n
  · rw [hp,angleVacuum_empty _ (reversed_angleScalar_ne_zero n)]
    exact zero_le_one
  · rw [reversed_vacuum_eq_tsum n ⟨p,hp⟩]
    exact tsum_nonneg fun k=>(reversed_column_nonnegative n).restricted.pow k |>.mulVec
      (reversed_column_nonnegative n).injection _

theorem reversed_northSource_eq_tsum (n : ℕ) (p : SourcePairing n) :
    angleNorthSource (fun _ : Fin n=>2*lambda) p=
      ∑' k : ℕ,((sourceTransfer (fun _ : Fin n=>(physicalWeights lambda).tile))^k).mulVec
        ((northSource (fun _ : Fin n=>(physicalWeights lambda).tile)).mulVec
          (angleVacuum (fun _ : Fin n=>2*lambda))) p := by
  apply (reversed_source_summablePowers n).stationary_eq_tsum
  simpa only [show 3*lambda-2*lambda=lambda by ring] using
    angleNorthSource_stationary (fun _ : Fin n=>2*lambda) (fun _=>reversed_L_ne_zero)

theorem reversed_source_weighted_summable (n d : ℕ) (p q : SourcePairing n) :
    Summable (fun k : ℕ=>(k:ℝ)^d*
      ((sourceTransfer (fun _ : Fin n=>(physicalWeights lambda).tile))^k) p q) :=
  (reversed_source_summablePowers n).weighted (reversed_source_nonnegative n) d p q


 

 


 

theorem angleVacuum_real {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (h : angleScalar u≠0)
    (hs : PositiveMatrix.SummablePowers (restrictedColumn (fun i=>physicalWeights (3*lambda-u i))))
    (p : Pairing n) :
    angleEvaluation u (polynomialVacuumVector n p)/angleScalar u=(angleVacuum u p:ℂ) := by
  let z : Pairing n → ℝ := fun q=>(angleEvaluation u (polynomialVacuumVector n q)/angleScalar u).im
  have hz : (transfer u).mulVec z=z := by
    funext q
    have hh:=congrArg (fun z : ℂ=>(z/angleScalar u).im) (congrFun (angle_rawVacuum_stationary u hL) q)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Complex.ofRealHom_eq_coe,Finset.sum_div,
      mul_div_assoc,Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,
      add_zero,z] using hh
  have he : z (empty n)=0 := by
    change (angleScalar u/angleScalar u).im=0
    rw [div_self h,Complex.one_im]
  have hr : (restrictedColumn (fun i=>physicalWeights (3*lambda-u i))).mulVec (fun p=>z p.val)+0=
      fun p=>z p.val := by
    funext q
    have hh:=congrFun hz q.val
    rw [transfer,column_mulVec_nonempty,he,mul_zero,zero_add] at hh
    simpa only [Pi.add_apply,Pi.zero_apply,add_zero] using hh
  have hzero : (fun p : NonemptyPairing n=>z p.val)=0 :=
    hs.unique_stationary hr (by simp)
  apply Complex.ext
  · rfl
  · change z p=0
    by_cases hp : p=empty n
    · simpa only [hp] using he
    · exact congrFun hzero ⟨p,hp⟩

theorem angleNorthSource_real {n : ℕ} (u : Fin n → ℝ)
    (hL : ∀i,L (3*lambda-u i)≠0) (h : angleScalar u≠0)
    (hv : PositiveMatrix.SummablePowers (restrictedColumn (fun i=>physicalWeights (3*lambda-u i))))
    (hs : PositiveMatrix.SummablePowers (sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile)))
    (p : SourcePairing n) :
    angleEvaluation u (polynomialNorthSource n p)/angleScalar u=(angleNorthSource u p:ℂ) := by
  let z : SourcePairing n → ℝ := fun q=>(angleEvaluation u (polynomialNorthSource n q)/angleScalar u).im
  have hr : (sourceTransfer (fun i=>(physicalWeights (3*lambda-u i)).tile)).mulVec z+0=z := by
    funext q
    have hh:=congrArg (fun z : ℂ=>(z/angleScalar u).im) (congrFun (angle_rawNorthSource_equation u hL) q)
    simp only [Pi.add_apply,Matrix.mulVec,dotProduct,Matrix.map_apply,Complex.ofRealHom_eq_coe,
      add_div,Finset.sum_div,mul_div_assoc,Complex.add_im,Complex.im_sum,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero,angleVacuum_real u hL h hv,
      mul_zero,Finset.sum_const_zero] at hh
    simpa only [Pi.add_apply,Pi.zero_apply,add_zero,Matrix.mulVec,dotProduct,z] using hh
  have hzero : z=0 := hs.unique_stationary hr (by simp)
  apply Complex.ext
  · rfl
  · exact congrFun hzero p

lemma physical_northSource_real (n : ℕ) (p : SourcePairing n) :
    angleEvaluation (fun _ : Fin n=>lambda) (polynomialNorthSource n p)/
      angleScalar (fun _ : Fin n=>lambda)=(angleNorthSource (fun _ : Fin n=>lambda) p:ℂ) := by
  apply angleNorthSource_real _ (fun _=>homogeneous_L_ne_zero) (homogeneous_angleScalar_ne_zero n)
  · simpa only [show 3*lambda-lambda=2*lambda by ring] using physical_vacuum_summablePowers n
  · simpa only [show 3*lambda-lambda=2*lambda by ring] using physical_source_summablePowers n

lemma reversed_northSource_real (n : ℕ) (p : SourcePairing n) :
    angleEvaluation (fun _ : Fin n=>2*lambda) (polynomialNorthSource n p)/
      angleScalar (fun _ : Fin n=>2*lambda)=(angleNorthSource (fun _ : Fin n=>2*lambda) p:ℂ) := by
  apply angleNorthSource_real _ (fun _=>reversed_L_ne_zero) (reversed_angleScalar_ne_zero n)
  · simpa only [show 3*lambda-2*lambda=lambda by ring] using reversed_vacuum_summablePowers n
  · simpa only [show 3*lambda-2*lambda=lambda by ring] using reversed_source_summablePowers n

lemma angleEvaluation_reflect {n : ℕ} (u : Fin n → ℝ) (f : Laurent n) :
    angleEvaluation u (reflectLaurent n f)=angleEvaluation (fun i=>3*lambda-u i) f := by
  have hp (e : Fin n → ℤ) (s : Finset (Fin n)) :
      phase^((3:ℤ)*∑i∈s,e i)=∏i∈s,(phase^(3:ℕ))^e i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.prod_insert hi,mul_add,zpow_add₀ phase_ne_zero,ih,
        _root_.zpow_mul]
      simp only [zpow_ofNat]
  have hh : (angleEvaluation u).toRingHom.comp (reflectLaurent n)=
      (angleEvaluation (fun i=>3*lambda-u i)).toRingHom := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro z
      change angleEvaluation u (reflectLaurent n (monomialL 0 z))=
        angleEvaluation (fun i=>3*lambda-u i) (monomialL 0 z)
      rw [reflectLaurent_monomial]
      simp only [Pi.zero_apply,Finset.sum_const_zero,mul_zero,zpow_zero,mul_one,neg_zero,
        angleEvaluation_monomial,Finset.prod_const_one]
    · intro e
      change angleEvaluation u (reflectLaurent n (monomialL e 1))=_
      rw [reflectLaurent_monomial,angleEvaluation_monomial]
      change (1*phase^(3*∑i,e i))*(∏i,anglePhase (u i)^(-e i))=
        angleEvaluation (fun i=>3*lambda-u i) (monomialL e 1)
      simp only [angleEvaluation_monomial,one_mul,anglePhase_sub,
        show anglePhase (3*lambda)=phase^(3:ℕ) from anglePhase_nat_mul 3 _,
        div_zpow,Finset.prod_div_distrib,_root_.zpow_neg,Finset.prod_inv_distrib,hp]
      rfl
  exact DFunLike.congr_fun hh f

end

 

 

noncomputable section
open scoped BigOperators Classical

 

def realNorthSeparator (n : ℕ) : ℝ :=
  sourceGlue n (angleNorthSource (fun _ : Fin n=>2*lambda))
    (angleNorthSource (fun _ : Fin n=>lambda))

lemma physical_angleScalar (n : ℕ) :
    angleScalar (fun _ : Fin n=>lambda)=
      scalarValue (RingHom.id ℂ) (fun _ : Fin n=>(C:ℂ)) := by
  rw [angleScalar,angleEvaluation_scalar]
  simp only [show 2*lambda-3*lambda= -lambda by ring,Real.cos_neg,C]

lemma reversed_angleScalar (n : ℕ) :
    angleScalar (fun _ : Fin n=>2*lambda)=
      scalarValue (RingHom.id ℂ) (fun _ : Fin n=>(C:ℂ)) := by
  rw [angleScalar,angleEvaluation_scalar]
  simp only [show 2*(2*lambda)-3*lambda=lambda by ring,C]

lemma physical_polynomialNorthSource (n : ℕ) (p : SourcePairing n) :
    angleEvaluation (fun _ : Fin n=>lambda) (polynomialNorthSource n p)=
      scalarValue (RingHom.id ℂ) (fun _ : Fin n=>(C:ℂ)) *
        (angleNorthSource (fun _ : Fin n=>lambda) p:ℂ) := by
  have hh:=physical_northSource_real n p
  rw [physical_angleScalar] at hh
  exact (div_eq_iff (scalarValue_homogeneous_ne_zero n)).mp hh |>.trans (mul_comm _ _)

lemma reversed_polynomialNorthSource (n : ℕ) (p : SourcePairing n) :
    angleEvaluation (fun _ : Fin n=>2*lambda) (polynomialNorthSource n p)=
      scalarValue (RingHom.id ℂ) (fun _ : Fin n=>(C:ℂ)) *
        (angleNorthSource (fun _ : Fin n=>2*lambda) p:ℂ) := by
  have hh:=reversed_northSource_real n p
  rw [reversed_angleScalar] at hh
  exact (div_eq_iff (scalarValue_homogeneous_ne_zero n)).mp hh |>.trans (mul_comm _ _)

lemma polynomialNorthGluing_physical (n : ℕ) :
    angleEvaluation (fun _ : Fin n=>lambda) (polynomialNorthGluing n)=
      scalarValue (RingHom.id ℂ) (fun _ : Fin n=>(C:ℂ))^2 * (realNorthSeparator n:ℂ) := by
  change (angleEvaluation (fun _ : Fin n=>lambda)).toRingHom
    (sourceGlue n (fun p=>reflectLaurent n (polynomialNorthSource n p)) (polynomialNorthSource n))=_
  rw [sourceGlue_map]
  let h := scalarValue (RingHom.id ℂ) (fun _ : Fin n=>(C:ℂ))
  have hv : (angleEvaluation (fun _ : Fin n=>lambda)).toRingHom ∘ polynomialNorthSource n=
      h • (Complex.ofRealHom ∘ angleNorthSource (fun _ : Fin n=>lambda)) := by
    funext p
    exact physical_polynomialNorthSource n p
  have hz : (angleEvaluation (fun _ : Fin n=>lambda)).toRingHom ∘
      (fun p=>reflectLaurent n (polynomialNorthSource n p))=
      h • (Complex.ofRealHom ∘ angleNorthSource (fun _ : Fin n=>2*lambda)) := by
    funext p
    change angleEvaluation (fun _ : Fin n=>lambda) (reflectLaurent n (polynomialNorthSource n p))=_
    rw [angleEvaluation_reflect,show 3*lambda-lambda=2*lambda by ring]
    exact reversed_polynomialNorthSource n p
  rw [hv,hz]
  rw [sourceGlue_scale,←sourceGlue_map,←pow_two]
  rfl

lemma archCandidate_physical (n : ℕ) :
    angleEvaluation (fun _ : Fin n=>lambda) (archCandidate n)=
      scalarArchNumerator (RingHom.id ℂ) (fun _ : Fin n=>(C:ℂ)) := by
  change (angleEvaluation (fun _ : Fin n=>lambda)).toRingHom
    (scalarArchNumerator (constantL n) rowCosineL)=_
  rw [map_scalarArchNumerator]
  have hh : (angleEvaluation (fun _ : Fin n=>lambda)).toRingHom.comp (constantL n)=RingHom.id ℂ := by
    ext z
    exact angleEvaluation_constant _ _
  rw [hh]
  congr 1
  funext i
  exact (angleEvaluation_rowCosine (fun _ : Fin n=>lambda) i).trans (by
    simp only [show 2*lambda-3*lambda= -lambda by ring,Real.cos_neg,C])

 

theorem realNorthSeparator_arch {n : ℕ} (hn : 1≤n) :
    ∃ g : Polynomial ℝ, MonicProblem n g ∧
      realNorthSeparator n=(n:ℝ)*C-eta*g.coeff (n-1) := by
  have hh:=congrArg (angleEvaluation (fun _ : Fin n=>lambda))
    (polynomialNorthGluing_eq_archCandidate n)
  rw [polynomialNorthGluing_physical,archCandidate_physical] at hh
  obtain ⟨g,hg,hnext⟩:=nextScalar_homogeneous hn
  refine ⟨g,hg,?_⟩
  simp only [scalarArchNumerator,hnext,previousCoeff,show n≠0 by omega,ite_false,
    Polynomial.coeff_C_mul,Polynomial.coeff_map,Complex.ofRealHom_eq_coe,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,RingHom.id_apply] at hh
  have hc : (realNorthSeparator n:ℂ)=(n:ℂ)*(C:ℂ)-(2*(d:ℂ)-1)*(g.coeff (n-1):ℂ) := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (scalarValue_homogeneous_ne_zero n))
    rw [hh]
    ring
  exact_mod_cast hc

end
end CriticalStrip.Diagram

end OAI
