import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.Traces

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped InnerProductSpace
open NormedSpace
open scoped TensorProduct InnerProductSpace
open UniformSpace
variable [KirchbergRordam.GenericRW.Size]
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n
variable [KirchbergRordam.GenericRW.PauliData]
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]
open Filter Topology BoundedContinuousFunction
open Filter Topology
open Topology
open scoped TensorProduct CStarAlgebra
open scoped CStarAlgebra ComplexOrder
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace
open scoped CStarAlgebra ComplexOrder
open scoped TensorProduct InnerProductSpace
open UniformSpace

namespace KirchbergRordam.GeneralBlockReindex
open MatrixBlockReindex MatrixDiagonalPath

open scoped CStarAlgebra Matrix
variable {P Q L R S T U : Type*}
  [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeL : Fintype L] [instFintypeR : Fintype R] [instFintypeS : Fintype S] [instFintypeT : Fintype T] [instFintypeU : Fintype U]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqL : DecidableEq L] [instDecidableEqR : DecidableEq R]
  [instDecidableEqS : DecidableEq S] [instDecidableEqT : DecidableEq T] [instDecidableEqU : DecidableEq U]
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instFintypeU instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT instDecidableEqU in
@[simp] lemma left_low.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6, contextLevel7}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    {U : Type contextLevel7}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [Fintype U]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    [DecidableEq U]
    (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
    (i : P) (j : Q) (l : L) :
    repackLeft hL hR ((i,j),.inl l) = (.inl (i,(hL (j,l)).1),(hL (j,l)).2) := rfl
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instFintypeU instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT instDecidableEqU in
@[simp] lemma left_full.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6, contextLevel7}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    {U : Type contextLevel7}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [Fintype U]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    [DecidableEq U]
    (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
    (i : P) (j : Q) (r : R) :
    repackLeft hL hR ((i,j),.inr r) = (.inr ((i,j),(hR r).1),(hR r).2) := rfl
lemma left_entry (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
    (a : Mat P) (m : Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
    block (Sum.elim (fun _ : L => MatrixTensor.leftMatrix (κ:=Q) a) (fun _ : R => m)) x y =
      MatrixTensor.leftMatrix (sumBlock (block (fun _ : U => a),block (fun _ : S => m)))
        (repackLeft hL hR x) (repackLeft hL hR y) := by
  rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
  · by_cases he : (j,l)=(j',l')
    · cases he; simp [block_apply]
    · have hh : (hL (j,l)).1≠(hL (j',l')).1 ∨ (hL (j,l)).2≠(hL (j',l')).2 := by
        by_contra h; push Not at h; exact he (hL.injective (Prod.ext h.1 h.2))
      have hjl : j≠j' ∨ l≠l' := by simpa only [Prod.mk.injEq,not_and_or] using he
      rcases hh with h|h <;> rcases hjl with hjl|hjl <;>
        simp [block_apply,h,hjl]
  · simp [block_apply]
  · simp [block_apply]
  · by_cases hr : r=r'
    · subst r'; simp [block_apply]
    · have hrr : (hR r).1≠(hR r').1 ∨ (hR r).2≠(hR r').2 := by
        by_contra h; push Not at h; exact hr (hR.injective (Prod.ext h.1 h.2))
      rcases hrr with h|h <;> simp [block_apply,hr,h]
lemma left_matrix (hL : Q × L ≃ U × T) (hR : R ≃ S × T)
    (a : Mat P) (m : Mat (P×Q)) :
    CStarMatrix.reindexₐ ℂ ℂ (repackLeft hL hR)
      (block (Sum.elim (fun _ : L => MatrixTensor.leftMatrix (κ:=Q) a) (fun _ : R => m))) =
        MatrixTensor.leftMatrix (sumBlock (block (fun _ : U => a),block (fun _ : S => m))) := by
  ext x y
  exact left_entry hL hR a m ((repackLeft hL hR).symm x)
    ((repackLeft hL hR).symm y) |>.trans (by simp)
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instFintypeU instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT instDecidableEqU in
@[simp] lemma right_low.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6, contextLevel7}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    {U : Type contextLevel7}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [Fintype U]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    [DecidableEq U]
    (hL : P × L ≃ T × U) (hR : R ≃ T × S)
    (i : P) (j : Q) (l : L) :
    repackRight hL hR ((i,j),.inl l) = ((hL (i,l)).1,.inl (j,(hL (i,l)).2)) := rfl
omit instFintypeP instFintypeQ instFintypeL instFintypeR instFintypeS instFintypeT instFintypeU instDecidableEqP instDecidableEqQ instDecidableEqL instDecidableEqR instDecidableEqS instDecidableEqT instDecidableEqU in
@[simp] lemma right_full.{contextLevel1, contextLevel2, contextLevel3, contextLevel4, contextLevel5, contextLevel6, contextLevel7}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    {L : Type contextLevel3}
    {R : Type contextLevel4}
    {S : Type contextLevel5}
    {T : Type contextLevel6}
    {U : Type contextLevel7}
    [Fintype P]
    [Fintype Q]
    [Fintype L]
    [Fintype R]
    [Fintype S]
    [Fintype T]
    [Fintype U]
    [DecidableEq P]
    [DecidableEq Q]
    [DecidableEq L]
    [DecidableEq R]
    [DecidableEq S]
    [DecidableEq T]
    [DecidableEq U]
    (hL : P × L ≃ T × U) (hR : R ≃ T × S)
    (i : P) (j : Q) (r : R) :
    repackRight hL hR ((i,j),.inr r) = ((hR r).1,.inr ((i,j),(hR r).2)) := rfl
lemma right_entry (hL : P × L ≃ T × U) (hR : R ≃ T × S)
    (a : Mat Q) (m : Mat (P×Q)) (x y : (P×Q)×(L⊕R)) :
    block (Sum.elim (fun _ : L => MatrixTensor.rightMatrix (ι:=P) a) (fun _ : R => m)) x y =
      MatrixTensor.rightMatrix (sumBlock (block (fun _ : U => a),block (fun _ : S => m)))
        (repackRight hL hR x) (repackRight hL hR y) := by
  rcases x with ⟨⟨i,j⟩,l|r⟩ <;> rcases y with ⟨⟨i',j'⟩,l'|r'⟩
  · by_cases he : (i,l)=(i',l')
    · cases he; simp [block_apply]
    · have hh : (hL (i,l)).1≠(hL (i',l')).1 ∨ (hL (i,l)).2≠(hL (i',l')).2 := by
        by_contra h; push Not at h; exact he (hL.injective (Prod.ext h.1 h.2))
      have hil : i≠i' ∨ l≠l' := by simpa only [Prod.mk.injEq,not_and_or] using he
      rcases hh with h|h <;> rcases hil with hil|hil <;>
        simp [block_apply,h,hil]
  · simp [block_apply]
  · simp [block_apply]
  · by_cases hr : r=r'
    · subst r'; simp [block_apply]
    · have hrr : (hR r).1≠(hR r').1 ∨ (hR r).2≠(hR r').2 := by
        by_contra h; push Not at h; exact hr (hR.injective (Prod.ext h.1 h.2))
      rcases hrr with h|h <;> simp [block_apply,hr,h]
lemma right_matrix (hL : P × L ≃ T × U) (hR : R ≃ T × S)
    (a : Mat Q) (m : Mat (P×Q)) :
    CStarMatrix.reindexₐ ℂ ℂ (repackRight hL hR)
      (block (Sum.elim (fun _ : L => MatrixTensor.rightMatrix (ι:=P) a) (fun _ : R => m))) =
        MatrixTensor.rightMatrix (sumBlock (block (fun _ : U => a),block (fun _ : S => m))) := by
  ext x y
  exact right_entry hL hR a m ((repackRight hL hR).symm x)
    ((repackRight hL hR).symm y) |>.trans (by simp)
end KirchbergRordam.GeneralBlockReindex
namespace KirchbergRordam.GeneralDropSystem
open MatrixDiagonalPath MatrixBlockReindex
open BalancedDropSystem (half lowerPath upperPath lower_zero lower_one upper_zero upper_one)
open scoped CStarAlgebra Matrix ComplexOrder

variable {p q P Q : ℕ} (d : Data p q P Q)
lemma eigen_cover (s : unitInterval) : ∃ i t, eigenpath d i t=s := by
  by_cases hs : (s:ℝ)≤1/2
  · refine ⟨.inl ⟨0,d.lower_pos⟩,⟨2*s,by constructor <;> linarith [s.property.1]⟩,?_⟩
    apply Subtype.ext
    change 2*(s:ℝ)/2=(s:ℝ)
    ring
  · refine ⟨.inr (.inl ⟨0,d.upper_pos⟩),⟨2*s-1,by constructor <;> linarith [s.property.2]⟩,?_⟩
    apply Subtype.ext
    change ((2*(s:ℝ)-1)+1)/2=(s:ℝ)
    ring
lemma eigen_lipschitz (i : Slot d) : LipschitzWith (1/2) (eigenpath d i) := by
  rcases i with i|i|i
  · apply LipschitzWith.of_dist_le_mul
    intro s t
    change |(s:ℝ)/2-(t:ℝ)/2|≤(1/2:ℝ)*|(s:ℝ)-(t:ℝ)|
    rw [←sub_div,abs_div]
    norm_num
    linarith
  · apply LipschitzWith.of_dist_le_mul
    intro s t
    change |((s:ℝ)+1)/2-((t:ℝ)+1)/2|≤(1/2:ℝ)*|(s:ℝ)-(t:ℝ)|
    rw [←sub_div,add_sub_add_right_eq_sub,abs_div]
    norm_num
    linarith
  · exact (LipschitzWith.const _).weaken (by norm_num)
lemma matrix_isTopologicalSemiring {SourceIndex : Type*} [Fintype SourceIndex] :
    IsTopologicalSemiring (MatrixDiagonalPath.Mat SourceIndex) := inferInstance

lemma matrix_continuousStar {SourceIndex : Type*} [Fintype SourceIndex] :
    ContinuousStar (MatrixDiagonalPath.Mat SourceIndex) := inferInstance

section

attribute [local instance] matrix_isTopologicalSemiring matrix_continuousStar


end

lemma fiberMap_continuous (path : C(unitInterval, PrimeDimensionDrop.Fiber p q)) :
    Continuous (fun point => fiberMap d point path) :=
  interpolate_continuous (zeroReindex d) (oneReindex d)
    (fun point => evaluationBlock (eigenpath d) point path)
    (evaluationBlock_continuous (eigenpath d) path)
@[simp] lemma rawStep_apply (f) (t : unitInterval) :
    rawStep d f t=interpolate (zeroReindex d) (oneReindex d) t (evaluationBlock (eigenpath d) t f) := rfl
lemma zero_eval (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (a : Mat (Fin p)) (ha : MatrixTensor.leftMatrix a=f 0) :
    evaluationBlock (eigenpath d) 0 f =
      block (Sum.elim (fun _ : Low d => MatrixTensor.leftMatrix (κ:=Fin q) a)
        (fun _ : High d ⊕ Mid d => f half)) := by
  apply congrArg block
  funext k
  rcases k with k|k|k <;> simp [eigenpath,ha]
lemma one_eval (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (b : Mat (Fin q)) (hb : MatrixTensor.rightMatrix b=f 1) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl (Fin p × Fin q)) (slotSwap d))
      (evaluationBlock (eigenpath d) 1 f)=
      block (Sum.elim (fun _ : High d => MatrixTensor.rightMatrix (ι:=Fin p) b)
        (fun _ : Low d ⊕ Mid d => f half)) := by
  change CStarMatrix.reindexₐ ℂ ℂ _ (block _) = _
  rw [reindex_block]
  apply congrArg block
  funext k
  rcases k with k|k|k <;> simp [slotSwap,eigenpath,hb]
lemma rawStep_zero (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (a : Mat (Fin p)) (ha : MatrixTensor.leftMatrix a=f 0) :
    rawStep d f 0=MatrixTensor.leftMatrix (κ:=Fin Q)
      (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter d)
        (sumBlock (block (fun _ : Fin d.zeroEnd => a),block (fun _ : Fin d.zeroMid => f half)))) := by
  rw [rawStep_apply,interpolate_zero,zero_eval d f a ha]
  unfold zeroReindex
  rw [reindex_trans,GeneralBlockReindex.left_matrix,reindex_left]
lemma rawStep_one (f : C(unitInterval,PrimeDimensionDrop.Fiber p q))
    (b : Mat (Fin q)) (hb : MatrixTensor.rightMatrix b=f 1) :
    rawStep d f 1=MatrixTensor.rightMatrix (ι:=Fin P)
      (CStarMatrix.reindexₐ ℂ ℂ (oneOuter d)
        (sumBlock (block (fun _ : Fin d.oneEnd => b),block (fun _ : Fin d.oneMid => f half)))) := by
  rw [rawStep_apply,interpolate_one]
  unfold oneReindex
  rw [reindex_trans,one_eval d f b hb,reindex_trans,GeneralBlockReindex.right_matrix,reindex_right]

lemma rawStep_mem (path : C(unitInterval, PrimeDimensionDrop.Fiber p q))
    (path_mem : path ∈ PrimeDimensionDrop.subalgebra p q) :
    rawStep d path ∈ PrimeDimensionDrop.subalgebra P Q := by
  obtain ⟨⟨leftValue, left_eq⟩, ⟨rightValue, right_eq⟩⟩ := path_mem
  exact ⟨⟨_, (rawStep_zero d path leftValue left_eq).symm⟩,
    ⟨_, (rawStep_one d path rightValue right_eq).symm⟩⟩


lemma rawStep_injective : Function.Injective (rawStep d) := by
  intro f g h
  apply diagonal_injective (eigenpath d) (eigen_cover d)
  apply ContinuousMap.ext
  intro t
  exact (interpolate (zeroReindex d) (oneReindex d) t).injective (DFunLike.congr_fun h t)
lemma step_injective : Function.Injective (step d) := by
  intro f g h
  apply Subtype.ext
  exact rawStep_injective d (congrArg Subtype.val h)
lemma step_norm (f : PrimeDimensionDrop.Algebra p q) : ‖step d f‖=‖f‖ :=
  NonUnitalStarAlgHom.norm_map _ (step_injective d) f
end KirchbergRordam.GeneralDropSystem
namespace KirchbergRordam.GeneralEndpointMultiplicity
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration EndpointMultiplicity
open scoped ComplexOrder CStarAlgebra
variable {P Q R E : Type*} [instFintypeP : Fintype P] [instFintypeQ : Fintype Q] [instFintypeR : Fintype R] [Fintype E]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [instDecidableEqR : DecidableEq R] [DecidableEq E]
def leftExpand : (P×E) ⊕ ((P×Q)×R) ≃ P × (E ⊕ (Q×R)) where
  toFun x := match x with
    | .inl (a,e) => (a,.inl e)
    | .inr ((a,b),r) => (a,.inr (b,r))
  invFun x := match x.2 with
    | .inl e => .inl (x.1,e)
    | .inr (b,r) => .inr ((x.1,b),r)
  left_inv x := by rcases x with ⟨a,e⟩|⟨⟨a,b⟩,r⟩ <;> rfl
  right_inv x := by rcases x with ⟨a,e|⟨b,r⟩⟩ <;> rfl
def rightExpand : (Q×E) ⊕ ((P×Q)×R) ≃ Q × (E ⊕ (P×R)) where
  toFun x := match x with
    | .inl (b,e) => (b,.inl e)
    | .inr ((a,b),r) => (b,.inr (a,r))
  invFun x := match x.2 with
    | .inl e => .inl (x.1,e)
    | .inr (a,r) => .inr ((a,x.1),r)
  left_inv x := by rcases x with ⟨b,e⟩|⟨⟨a,b⟩,r⟩ <;> rfl
  right_inv x := by rcases x with ⟨b,e|⟨a,r⟩⟩ <;> rfl
lemma leftExpand_matrix (a : Mat P) :
    CStarMatrix.reindexₐ ℂ ℂ (leftExpand (Q:=Q) (R:=R) (E:=E))
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,
        block (fun _ : R => MatrixTensor.leftMatrix (κ:=Q) a))) =
      MatrixTensor.leftMatrix (κ:=E ⊕ (Q×R)) a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  rcases k with u|⟨b,r⟩ <;> rcases l with v|⟨c,s⟩
  · change a i j*(if u=v then 1 else 0)=a i j*(if (Sum.inl u : E ⊕ Q×R)=.inl v then 1 else 0)
    simp
  · change 0=a i j*0; simp
  · change 0=a i j*0; simp
  · change (if r=s then a i j * (if b=c then 1 else 0) else 0) =
      a i j * (if (Sum.inr (b,r) : E ⊕ Q×R)=.inr (c,s) then 1 else 0)
    by_cases hb : b=c <;> by_cases hr : r=s <;> simp [hb,hr,Prod.ext_iff]
lemma rightExpand_matrix (a : Mat Q) :
    CStarMatrix.reindexₐ ℂ ℂ (rightExpand (P:=P) (R:=R) (E:=E))
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,
        block (fun _ : R => MatrixTensor.rightMatrix (ι:=P) a))) =
      MatrixTensor.leftMatrix (κ:=E ⊕ (P×R)) a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  rcases k with u|⟨b,r⟩ <;> rcases l with v|⟨c,s⟩
  · change a i j*(if u=v then 1 else 0)=a i j*(if (Sum.inl u : E ⊕ P×R)=.inl v then 1 else 0)
    simp
  · change 0=a i j*0; simp
  · change 0=a i j*0; simp
  · change (if r=s then (if b=c then 1 else 0) * a i j else 0) =
      a i j * (if (Sum.inr (b,r) : E ⊕ P×R)=.inr (c,s) then 1 else 0)
    by_cases hb : b=c <;> by_cases hr : r=s <;> simp [hb,hr,Prod.ext_iff]
def leftBase (h : 2≤Fintype.card (E ⊕ (Q×R))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ((P×E)⊕((P×Q)×R)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (leftExpand (P:=P) (Q:=Q) (R:=R) (E:=E)).symm).toStarAlgHom.comp
    (MatrixTensor.rightMatrix.comp (DropMatrixRepresentations.representation _ h))
def rightBase (h : 2≤Fintype.card (E ⊕ (P×R))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ((Q×E)⊕((P×Q)×R)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (rightExpand (P:=P) (Q:=Q) (R:=R) (E:=E)).symm).toStarAlgHom.comp
    (MatrixTensor.rightMatrix.comp (DropMatrixRepresentations.representation _ h))
lemma leftBase_commute (h : 2≤Fintype.card (E ⊕ (Q×R))) (a : Mat P)
    (d : DimensionDrop23) :
    Commute (leftBase (P:=P) h d)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => MatrixTensor.leftMatrix (κ:=Q) a))) := by
  let e := CStarMatrix.reindexₐ ℂ ℂ (leftExpand (P:=P) (Q:=Q) (R:=R) (E:=E))
  apply e.injective
  change e (leftBase h d * _)=e (_ * leftBase h d)
  rw [map_mul,map_mul,leftExpand_matrix]
  have he : e (leftBase (P:=P) h d)=MatrixTensor.rightMatrix
      (DropMatrixRepresentations.representation _ h d) := by
    simp only [leftBase,StarAlgHom.comp_apply,
      CStarMatrix.reindexₐ_symm]
    change e (e.symm (MatrixTensor.rightMatrix (DropMatrixRepresentations.representation _ h d))) = _
    exact e.apply_symm_apply _
  rw [he]
  exact (MatrixTensor.legs_commute a _).symm.eq
lemma rightBase_commute (h : 2≤Fintype.card (E ⊕ (P×R))) (a : Mat Q)
    (d : DimensionDrop23) :
    Commute (rightBase (Q:=Q) h d)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => MatrixTensor.rightMatrix (ι:=P) a))) := by
  let e := CStarMatrix.reindexₐ ℂ ℂ (rightExpand (P:=P) (Q:=Q) (R:=R) (E:=E))
  apply e.injective
  change e (rightBase h d * _)=e (_ * rightBase h d)
  rw [map_mul,map_mul,rightExpand_matrix]
  have he : e (rightBase (Q:=Q) h d)=MatrixTensor.rightMatrix
      (DropMatrixRepresentations.representation _ h d) := by
    simp only [rightBase,StarAlgHom.comp_apply,
      CStarMatrix.reindexₐ_symm]
    change e (e.symm (MatrixTensor.rightMatrix (DropMatrixRepresentations.representation _ h d))) = _
    exact e.apply_symm_apply _
  rw [he]
  exact (MatrixTensor.legs_commute a _).symm.eq

def leftRep (h : 2≤Fintype.card (E ⊕ (Q×R))) (v : unitary (Mat (P×Q))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ((P×E)⊕((P×Q)×R)) :=
  (conj (duplicateUnitary (P:=P×E) (Q:=P×Q) (R:=R) v)).toStarAlgHom.comp (leftBase (P:=P) (Q:=Q) (R:=R) h)
def rightRep (h : 2≤Fintype.card (E ⊕ (P×R))) (v : unitary (Mat (P×Q))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat ((Q×E)⊕((P×Q)×R)) :=
  (conj (duplicateUnitary (P:=Q×E) (Q:=P×Q) (R:=R) v)).toStarAlgHom.comp (rightBase (P:=P) (Q:=Q) (R:=R) h)
lemma leftRep_commute (h : 2≤Fintype.card (E ⊕ (Q×R))) (v : unitary (Mat (P×Q)))
    (a : Mat P) (d : DimensionDrop23) :
    Commute (leftRep h v d)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => conj v (MatrixTensor.leftMatrix (κ:=Q) a)))) := by
  have hc := (leftBase_commute h a d).map
    (conj (duplicateUnitary (P:=P×E) (Q:=P×Q) (R:=R) v)).toRingHom
  change Commute (conj (duplicateUnitary (P:=P×E) (Q:=P×Q) (R:=R) v) (leftBase h d))
    (conj (duplicateUnitary (P:=P×E) (Q:=P×Q) (R:=R) v)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => MatrixTensor.leftMatrix (κ:=Q) a)))) at hc
  rw [conj_duplicate] at hc
  exact hc
lemma rightRep_commute (h : 2≤Fintype.card (E ⊕ (P×R))) (v : unitary (Mat (P×Q)))
    (a : Mat Q) (d : DimensionDrop23) :
    Commute (rightRep h v d)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => conj v (MatrixTensor.rightMatrix (ι:=P) a)))) := by
  have hc := (rightBase_commute h a d).map
    (conj (duplicateUnitary (P:=Q×E) (Q:=P×Q) (R:=R) v)).toRingHom
  change Commute (conj (duplicateUnitary (P:=Q×E) (Q:=P×Q) (R:=R) v) (rightBase h d))
    (conj (duplicateUnitary (P:=Q×E) (Q:=P×Q) (R:=R) v)
      (sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => MatrixTensor.rightMatrix (ι:=P) a)))) at hc
  rw [conj_duplicate] at hc
  exact hc

lemma leftRep_bound (h : 2≤Fintype.card (E ⊕ (Q×R))) (v : unitary (Mat (P×Q)))
    (a : Mat P) (x : Mat (P×Q)) (d : DimensionDrop23) {ε : ℝ}
    (hx : ‖x-conj v (MatrixTensor.leftMatrix (κ:=Q) a)‖≤ε) :
    ‖leftRep h v d*sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => x))-
      sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => x))*leftRep h v d‖≤2*ε*‖d‖ :=
  commutator_approx (leftRep h v) _ _ d (leftRep_commute h v a d)
    ((duplicate_difference (MatrixTensor.leftMatrix (κ:=E) a) x _).trans hx)
lemma rightRep_bound (h : 2≤Fintype.card (E ⊕ (P×R))) (v : unitary (Mat (P×Q)))
    (a : Mat Q) (x : Mat (P×Q)) (d : DimensionDrop23) {ε : ℝ}
    (hx : ‖x-conj v (MatrixTensor.rightMatrix (ι:=P) a)‖≤ε) :
    ‖rightRep h v d*sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => x))-
      sumBlock (MatrixTensor.leftMatrix (κ:=E) a,block (fun _ : R => x))*rightRep h v d‖≤2*ε*‖d‖ :=
  commutator_approx (rightRep h v) _ _ d (rightRep_commute h v a d)
    ((duplicate_difference (MatrixTensor.leftMatrix (κ:=E) a) x _).trans hx)
end KirchbergRordam.GeneralEndpointMultiplicity
end

end OAI
