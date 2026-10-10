import Mathlib
import OAI.Probability.CoordinateSweeps.Decomposition
import OAI.RepresentationTheory.SignedTensor.Resolution

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma onLine_row_iff (j : Fin A.b) (L : A.Line j) (y : B.Slot) (i : Fin h) :
    H.OnLine (Fin.castAdd B.b j) (rowLines A B j (L,y)) i ↔
      H.rowOf i=y ∧ (fun k : {k : Fin A.b // k≠j} =>
        (splitSlots A B (H.path i (prefixTime A B j.castSucc))).1 k.val)=L := by
  have hh := rowLines_evaluation A B j (H.path i (prefixTime A B j.castSucc))
  constructor
  · intro hi
    have he := congrArg (rowLines A B j).symm hi
    change (rowLines A B j).symm (fun k => H.path i (prefixTime A B j.castSucc) k.val)=
      (rowLines A B j).symm (rowLines A B j (L,y)) at he
    rw [hh,Equiv.symm_apply_apply] at he
    exact ⟨(H.row_constant i j.castSucc).symm.trans (congrArg Prod.snd he),congrArg Prod.fst he⟩
  · rintro ⟨hi,hl⟩
    apply (rowLines A B j).symm.injective
    change (rowLines A B j).symm (fun k => H.path i (prefixTime A B j.castSucc) k.val)=
      (rowLines A B j).symm (rowLines A B j (L,y))
    rw [hh,Equiv.symm_apply_apply]
    exact Prod.ext hl ((H.row_constant i j.castSucc).trans hi)

lemma onLine_column_iff (j : Fin B.b) (x : A.Slot) (L : B.Line j) (i : Fin h) :
    H.OnLine (Fin.natAdd A.b j) (columnLines A B j (x,L)) i ↔
      H.columnOf i=x ∧ (fun k : {k : Fin B.b // k≠j} =>
        (splitSlots A B (H.path i (suffixTime A B j.castSucc))).2 k.val)=L := by
  have hh := columnLines_evaluation A B j (H.path i (suffixTime A B j.castSucc))
  constructor
  · intro hi
    have he := congrArg (columnLines A B j).symm hi
    change (columnLines A B j).symm (fun k => H.path i (suffixTime A B j.castSucc) k.val)=
      (columnLines A B j).symm (columnLines A B j (x,L)) at he
    rw [hh,Equiv.symm_apply_apply] at he
    exact ⟨(H.column_constant i j.castSucc).symm.trans (congrArg Prod.fst he),congrArg Prod.snd he⟩
  · rintro ⟨hi,hl⟩
    apply (columnLines A B j).symm.injective
    change (columnLines A B j).symm (fun k => H.path i (suffixTime A B j.castSucc) k.val)=
      (columnLines A B j).symm (columnLines A B j (x,L))
    rw [hh,Equiv.symm_apply_apply]
    exact Prod.ext ((H.column_constant i j.castSucc).trans hi) hl

def rowOnLineEquiv (j : Fin A.b) (L : A.Line j) (y : B.Slot) :
    {k : Fin (H.rowCount y) // (H.rowHoles y).OnLine j L k} ≃
      {i : Fin h // H.OnLine (Fin.castAdd B.b j) (rowLines A B j (L,y)) i} where
  toFun k := ⟨(H.rowCards y k.val).val,(H.onLine_row_iff j L y _).mpr
    ⟨(H.rowCards y k.val).property,k.property⟩⟩
  invFun i := ⟨(H.rowCards y).symm ⟨i.val,((H.onLine_row_iff j L y _).mp i.property).1⟩,by
    change (fun (k : {k : Fin A.b // k ≠ j}) => (splitSlots A B (H.path
      (H.rowCards y ((H.rowCards y).symm _)).val (prefixTime A B j.castSucc))).1 k.val)=L
    simp only [Equiv.apply_symm_apply]
    exact ((H.onLine_row_iff j L y _).mp i.property).2⟩
  left_inv k := by
    apply Subtype.ext
    apply (H.rowCards y).injective
    simp only [Equiv.apply_symm_apply]
  right_inv i := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]

def columnOnLineEquiv (j : Fin B.b) (x : A.Slot) (L : B.Line j) :
    {k : Fin (H.columnCount x) // (H.columnHoles x).OnLine j L k} ≃
      {i : Fin h // H.OnLine (Fin.natAdd A.b j) (columnLines A B j (x,L)) i} where
  toFun k := ⟨(H.columnCards x k.val).val,(H.onLine_column_iff j x L _).mpr
    ⟨(H.columnCards x k.val).property,k.property⟩⟩
  invFun i := ⟨(H.columnCards x).symm ⟨i.val,((H.onLine_column_iff j x L _).mp i.property).1⟩,by
    change (fun (k : {k : Fin B.b // k ≠ j}) => (splitSlots A B (H.path
      (H.columnCards x ((H.columnCards x).symm _)).val (suffixTime A B j.castSucc))).2 k.val)=L
    simp only [Equiv.apply_symm_apply]
    exact ((H.onLine_column_iff j x L _).mp i.property).2⟩
  left_inv k := by
    apply Subtype.ext
    apply (H.columnCards x).injective
    simp only [Equiv.apply_symm_apply]
  right_inv i := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]

lemma lineCount_row (j : Fin A.b) (L : A.Line j) (y : B.Slot) :
    H.lineCount (Fin.castAdd B.b j) (rowLines A B j (L,y))=(H.rowHoles y).lineCount j L := by
  exact (H.card_onLine _ _).symm.trans ((Fintype.card_congr (H.rowOnLineEquiv j L y)).symm.trans
    ((H.rowHoles y).card_onLine j L))
lemma lineCount_column (j : Fin B.b) (x : A.Slot) (L : B.Line j) :
    H.lineCount (Fin.natAdd A.b j) (columnLines A B j (x,L))=(H.columnHoles x).lineCount j L := by
  exact (H.card_onLine _ _).symm.trans ((Fintype.card_congr (H.columnOnLineEquiv j x L)).symm.trans
    ((H.columnHoles x).card_onLine j L))

/- One head stage contributes exactly the sum of its child row potentials. -/
lemma cost_stage_row (j : Fin A.b) :
    (∑ L : (concat A B).Line (Fin.castAdd B.b j),
      Real.log (((2 ^ (concat A B).bits (Fin.castAdd B.b j) : ℕ) : ℝ) ^
          H.lineCount (Fin.castAdd B.b j) L /
        ((2 ^ (concat A B).bits (Fin.castAdd B.b j)).descFactorial
          (H.lineCount (Fin.castAdd B.b j) L) : ℝ)))=
      ∑ y : B.Slot, ∑ L : A.Line j,
        Real.log (((2^A.bits j : ℕ) : ℝ)^(H.rowHoles y).lineCount j L /
          ((2^A.bits j).descFactorial ((H.rowHoles y).lineCount j L) : ℝ)) := by
  rw [← (rowLines A B j).sum_comp,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro L _
  rw [H.lineCount_row,concat_bits_left]

lemma cost_stage_column (j : Fin B.b) :
    (∑ L : (concat A B).Line (Fin.natAdd A.b j),
      Real.log (((2 ^ (concat A B).bits (Fin.natAdd A.b j) : ℕ) : ℝ) ^
          H.lineCount (Fin.natAdd A.b j) L /
        ((2 ^ (concat A B).bits (Fin.natAdd A.b j)).descFactorial
          (H.lineCount (Fin.natAdd A.b j) L) : ℝ)))=
      ∑ x : A.Slot, ∑ L : B.Line j,
        Real.log (((2^B.bits j : ℕ) : ℝ)^(H.columnHoles x).lineCount j L /
          ((2^B.bits j).descFactorial ((H.columnHoles x).lineCount j L) : ℝ)) := by
  rw [← (columnLines A B j).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro L _
  rw [H.lineCount_column,concat_bits_right]

/- No conditioning cost is discarded in the induction split. -/
theorem cost_split : H.cost=(∑ y, (H.rowHoles y).cost)+(∑ x, (H.columnHoles x).cost) := by
  unfold cost
  erw [Fin.sum_univ_add]
  congr 1
  · trans ∑ j : Fin A.b, ∑ y : B.Slot, ∑ L : A.Line j,
      Real.log (((2^A.bits j : ℕ) : ℝ)^(H.rowHoles y).lineCount j L /
        ((2^A.bits j).descFactorial ((H.rowHoles y).lineCount j L) : ℝ))
    · apply Finset.sum_congr rfl
      intro j _
      convert H.cost_stage_row j using 1
      congr 3
      exact Subsingleton.elim _ _
    · exact Finset.sum_comm
  · trans ∑ j : Fin B.b, ∑ x : A.Slot, ∑ L : B.Line j,
      Real.log (((2^B.bits j : ℕ) : ℝ)^(H.columnHoles x).lineCount j L /
        ((2^B.bits j).descFactorial ((H.columnHoles x).lineCount j L) : ℝ))
    · apply Finset.sum_congr rfl
      intro j _
      convert H.cost_stage_column j using 1
      congr 3
      exact Subsingleton.elim _ _
    · exact Finset.sum_comm

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open FiberBlocks SignedTensor UnitaryIrrep
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma row_column_index_injective : Function.Injective (fun x : H.JunctionFree => (H.rowIndex x,H.columnIndex x)) := by
  intro x y he
  apply Subtype.ext
  apply (splitSlots A B).injective
  exact Prod.ext ((Fintype.equivFin A.Slot).injective (congrArg Prod.snd he))
    ((Fintype.equivFin B.Slot).injective (congrArg Prod.fst he))

lemma row_entropy_sum {p : ℕ} (α : BlockType (FiberBlocks.size H.rowIndex) p) (c e : ℝ) :
    (∑ i, (-c*Real.log (activeIrrep (α i)).dimension+
      e*H.rowCount (H.rowSite i)*Real.log A.size-(H.rowHoles (H.rowSite i)).cost))=
      -c*blockEntropy α+e*h*Real.log A.size-∑ y, (H.rowHoles y).cost := by
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
    blockEntropy]
  have hc : (∑ i, (H.rowCount (H.rowSite i) : ℝ))=h := by
    rw [← Nat.cast_sum]
    congr 1
    exact ((Fintype.equivFin B.Slot).symm.sum_comp H.rowCount).trans H.sum_rowCount
  rw [hc]
  congr 1
  exact (Fintype.equivFin B.Slot).symm.sum_comp (fun y => (H.rowHoles y).cost)

lemma column_entropy_sum {p : ℕ} (β : BlockType (FiberBlocks.size H.columnIndex) p) (c e : ℝ) :
    (∑ i, (-c*Real.log (activeIrrep (β i)).dimension+
      e*H.columnCount (H.columnSite i)*Real.log B.size-(H.columnHoles (H.columnSite i)).cost))=
      -c*blockEntropy β+e*h*Real.log B.size-∑ x, (H.columnHoles x).cost := by
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
    blockEntropy]
  have hc : (∑ i, (H.columnCount (H.columnSite i) : ℝ))=h := by
    rw [← Nat.cast_sum]
    congr 1
    exact ((Fintype.equivFin A.Slot).symm.sum_comp H.columnCount).trans H.sum_columnCount
  rw [hc]
  congr 1
  exact (Fintype.equivFin A.Slot).symm.sum_comp (fun x => (H.columnHoles x).cost)

variable (p : ℕ) (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) (q : ℕ) (hq : 0 < q) (c e : ℝ) (s : ℕ)
theorem row_child_hook_bound (hq : 0 < q) (hAS : A.size ≤ s)
    (hR : ∀ y : B.Slot, ∀ σ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.rowCount y*Real.log A.size-(H.rowHoles y).cost))
    (α : BlockType (FiberBlocks.size H.rowIndex) p) :
      (Matrix.trace (((fiberProjector H.rowIndex eF (fun i => activeIrrep (α i))*
        H.rowAverage hf z (H.junctionTensorAction p eF)).conjTranspose*
        (fiberProjector H.rowIndex eF (fun i => activeIrrep (α i))*
        H.rowAverage hf z (H.junctionTensorAction p eF)))^q)).re ≤ Real.exp (-c*blockEntropy α+(e*h*Real.log A.size-(∑ y, (H.rowHoles y).cost)+
        ((B.size*((2*p)*(2*p)) : ℕ):ℝ)*Real.log (s+1 : ℕ))) := by
    have hh := H.row_moment_bound p eF hf z hq.ne' (fun i => activeIrrep (α i))
      (fun i => -c*Real.log (activeIrrep (α i)).dimension+
        e*H.rowCount (H.rowSite i)*Real.log A.size-(H.rowHoles (H.rowSite i)).cost)
      (fun i => hR (H.rowSite i) _)
    apply hh.trans
    have hn : ((A.size+1 : ℕ):ℝ)^(B.size*((2*p)*(2*p))) ≤
        ((s+1 : ℕ):ℝ)^(B.size*((2*p)*(2*p))) := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.add_le_add_right hAS 1) _
    apply (mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le).trans_eq
    rw [nat_pow_eq_exp,H.row_entropy_sum,← Real.exp_add]
    congr 1
    ring
theorem column_child_hook_bound (hq : 0 < q) (hBS : B.size ≤ s)
    (hC : ∀ x : A.Slot, ∀ σ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.columnCount x*Real.log B.size-(H.columnHoles x).cost))
    (β : BlockType (FiberBlocks.size H.columnIndex) p) :
      (Matrix.trace (((H.columnAverage hf z (H.junctionTensorAction p eF)*
        fiberProjector H.columnIndex eF (fun i => activeIrrep (β i))).conjTranspose*
        (H.columnAverage hf z (H.junctionTensorAction p eF)*
        fiberProjector H.columnIndex eF (fun i => activeIrrep (β i))))^q)).re ≤ Real.exp (-c*blockEntropy β+(e*h*Real.log B.size-(∑ x, (H.columnHoles x).cost)+
        ((A.size*((2*p)*(2*p)) : ℕ):ℝ)*Real.log (s+1 : ℕ))) := by
    have hh := H.column_moment_bound p eF hf z hq.ne' (fun i => activeIrrep (β i))
      (fun i => -c*Real.log (activeIrrep (β i)).dimension+
        e*H.columnCount (H.columnSite i)*Real.log B.size-(H.columnHoles (H.columnSite i)).cost)
      (fun i => hC (H.columnSite i) _)
    apply hh.trans
    have hn : ((B.size+1 : ℕ):ℝ)^(A.size*((2*p)*(2*p))) ≤
        ((s+1 : ℕ):ℝ)^(A.size*((2*p)*(2*p))) := by
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.add_le_add_right hBS 1) _
    apply (mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le).trans_eq
    rw [nat_pow_eq_exp,H.column_entropy_sum,← Real.exp_add]
    congr 1
    ring
/- Exact row/column induction estimate on the literal free junction board.
Only smaller-grid conditional estimates enter as hypotheses. -/
theorem grid_projected_hook_bound (p : ℕ) (hp : 0 < p)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (hf : H.Feasible)
    (z : ℝ) (q : ℕ) (hq : 0 < q) (c e : ℝ) (hc : 0 ≤ c) (hcq : c ≤ q)
    (s : ℕ) (hpS : p ≤ s) (hAS : A.size ≤ s) (hBS : B.size ≤ s)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree))))
    (hR : ∀ y : B.Slot, ∀ σ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.rowCount y*Real.log A.size-(H.rowHoles y).cost))
    (hC : ∀ x : A.Slot, ∀ σ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.columnCount x*Real.log B.size-(H.columnHoles x).cost)) :
    let X := H.rowAverage hf z (H.junctionTensorAction p eF)
    let Y := H.columnAverage hf z (H.junctionTensorAction p eF)
    let P := ρ.projector (action p (Fintype.card H.JunctionFree))
    (Matrix.trace (((Y*P*X).conjTranspose*(Y*P*X))^q)).re ≤
      Real.exp (-c*Real.log ρ.dimension+e*h*(Real.log A.size+Real.log B.size)-H.cost+c*h+
        (((2*q+1 : ℕ) : ℝ)*((A.size+B.size)*((2*p)*(2*p)) : ℕ)+
          c*((A.size+B.size)*(41*p^2) : ℕ))*Real.log (s+1 : ℕ)) := by
  dsimp only
  let : NeZero (Fintype.card B.Slot) := ⟨Fintype.card_ne_zero⟩
  let ER := e*h*Real.log A.size-(∑ y, (H.rowHoles y).cost)+
    ((B.size*((2*p)*(2*p)) : ℕ):ℝ)*Real.log (s+1 : ℕ)
  let EC := e*h*Real.log B.size-(∑ x, (H.columnHoles x).cost)+
    ((A.size*((2*p)*(2*p)) : ℕ):ℝ)*Real.log (s+1 : ℕ)
  have hr := H.row_child_hook_bound (p := p) (eF := eF) (hf := hf) (z := z) (q := q) (c := c) (e := e) (s := s) hq hAS hR
  have hc' := H.column_child_hook_bound (p := p) (eF := eF) (hf := hf) (z := z) (q := q) (c := c) (e := e) (s := s) hq hBS hC
  have hh := labeled_projected_moment_bound H.rowIndex H.columnIndex H.row_column_index_injective eF s hp hpS
    (fun i => (H.row_size_le i).trans hAS) (fun i => (H.column_size_le i).trans hBS)
    ρ q hq c ER EC hc hcq (H.rowAverage hf z (H.junctionTensorAction p eF))
      (H.columnAverage hf z (H.junctionTensorAction p eF)) hr hc'
  apply hh.trans_eq
  congr 1
  dsimp [ER,EC]
  rw [H.cost_split]
  simp only [card_slot]
  -- Exact number of deleted junction sites, including h=s and empty fibers.
  have hm : ((B.size:ℝ)*A.size-Fintype.card H.JunctionFree)=(h:ℝ) := by
    rw [H.card_freeAt]
    have hh : h ≤ (concat A B).size := by
      simpa only [Fintype.card_fin,card_slot] using Fintype.card_le_of_injective (H.path · 0) (H.disjoint 0)
    rw [Nat.cast_sub hh]
    simp only [concat_size,Nat.cast_mul]
    ring
  rw [hm]
  push_cast
  ring
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep SignedTensor YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
def junctionChart (hf : H.Feasible) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) :
    H.stabilizer ≃* Equiv.Perm (Fin (Fintype.card H.JunctionFree)) :=
  (H.junctionEquiv hf).trans (H.junctionFreeEquiv.trans e.symm.permCongrHom)

lemma junction_projector_commute_column (p : ℕ) (hf : H.Feasible)
    (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (z : ℝ)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree)))) :
    ρ.projector (action p _) * H.columnAverage hf z (H.junctionTensorAction p e)=
      H.columnAverage hf z (H.junctionTensorAction p e) * ρ.projector (action p _) := by
  exact ρ.projector_commute_average (action p _)
    (fun ω : H.ColumnChoices => ((∏ x, B.choiceWeight z (ω x).val/(H.columnHoles x).probability z : ℝ) : ℂ))
    (fun ω => e.symm.permCongrHom (H.junctionFreeEquiv (H.columnResidual hf ω)))

/- The exact projected tensor moment on the literal junction board equals
its genuine Hom multiplicity times the main theorem's conditional moment. -/
theorem junction_projected_moment (p : ℕ) (hf : H.Feasible)
    (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (z : ℝ)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree)))) {q : ℕ} (hq : q ≠ 0) :
    let X := H.rowAverage hf z (H.junctionTensorAction p e)
    let Y := H.columnAverage hf z (H.junctionTensorAction p e)
    let P := ρ.projector (action p (Fintype.card H.JunctionFree))
    (Matrix.trace (((Y*P*X).conjTranspose*(Y*P*X))^q)).re =
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
        (matrixRepresentation (action p (Fintype.card H.JunctionFree)))) : ℝ) *
        schattenMoment q (H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf e))) := by
  dsimp only
  let w : {ω : (concat A B).Choices // H.Compatible ω} → ℂ := fun ω =>
    (((concat A B).choiceWeight z ω.val/H.probability z : ℝ) : ℂ)
  let g := fun ω => H.junctionChart hf e (H.residual hf ω)
  have ha : averageMatrix (action p (Fintype.card H.JunctionFree)) w g =
      H.columnAverage hf z (H.junctionTensorAction p e)*H.rowAverage hf z (H.junctionTensorAction p e) :=
    H.junction_average_split hf z (H.junctionTensorAction p e)
  have hb : averageMatrix ρ.matrix w g=H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf e)) := by
    rw [H.conditionalAverage_eq_sum]
    rfl
  have he := ρ.projected_operator_moment (action p _) (fun σ => (matrix_inv σ).symm) w g hq
  have hc : ρ.projector (action p _)*averageMatrix (action p _) w g=
      H.columnAverage hf z (H.junctionTensorAction p e)*ρ.projector (action p _)*
        H.rowAverage hf z (H.junctionTensorAction p e) := by
    rw [ha,← mul_assoc,H.junction_projector_commute_column]
  rw [hc] at he
  have hre := congrArg Complex.re he
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] at hre
  calc
    _ = _ * schattenMoment q (averageMatrix ρ.matrix w g) := hre
    _ = _ := congrArg (fun M : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ =>
      (Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
        (matrixRepresentation (action p (Fintype.card H.JunctionFree)))) : ℝ)*schattenMoment q M) hb

/- Hook occurrence removes the multiplicity without normalizing the trace. -/
theorem conditional_hook_moment_le_projected (p : ℕ) (hf : H.Feasible)
    (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (z : ℝ)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree)))) {q : ℕ} (hq : q ≠ 0)
    (μ : YoungDiagram) (t : Fin (Fintype.card H.JunctionFree) ≃ Boxes μ)
    (hρ : hasShape μ t ρ.asRepresentation) (hhook : Hook μ p) :
    schattenMoment q (H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf e))) ≤
      (Matrix.trace (((H.columnAverage hf z (H.junctionTensorAction p e)*
        ρ.projector (action p _)*H.rowAverage hf z (H.junctionTensorAction p e)).conjTranspose*
        (H.columnAverage hf z (H.junctionTensorAction p e)*
        ρ.projector (action p _)*H.rowAverage hf z (H.junctionTensorAction p e)))^q)).re := by
  rw [H.junction_projected_moment p hf e z ρ hq]
  have hn := hook_multiplicity_pos ρ t hρ hhook
  have hr : (1 : ℝ) ≤ Module.finrank ℂ (ρ.asRepresentation.IntertwiningMap
      (matrixRepresentation (action p (Fintype.card H.JunctionFree)))) := by exact_mod_cast hn
  have ht := trace_moment_nonneg (H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf e))) q
  exact (one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right hr ht)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep SignedTensor YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
theorem grid_conditional_hook_bound (p : ℕ) (hp : 0 < p)
    (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) (hf : H.Feasible)
    (z : ℝ) (q : ℕ) (hq : 0 < q) (c e : ℝ) (hc : 0 ≤ c) (hcq : c ≤ q)
    (s : ℕ) (hpS : p ≤ s) (hAS : A.size ≤ s) (hBS : B.size ≤ s)
    (ρ : UnitaryIrrep (Equiv.Perm (Fin (Fintype.card H.JunctionFree))))
    (hR : ∀ y : B.Slot, ∀ σ : UnitaryIrrep (H.rowHoles y).stabilizer,
      schattenMoment q ((H.rowHoles y).conditionalAverage (H.rowHoles y).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.rowCount y*Real.log A.size-(H.rowHoles y).cost))
    (hC : ∀ x : A.Slot, ∀ σ : UnitaryIrrep (H.columnHoles x).stabilizer,
      schattenMoment q ((H.columnHoles x).conditionalAverage (H.columnHoles x).feasible_of_disjoint z σ) ≤
        Real.exp (-c*Real.log σ.dimension+e*H.columnCount x*Real.log B.size-(H.columnHoles x).cost))
    (μ : YoungDiagram) (t : Fin (Fintype.card H.JunctionFree) ≃ Boxes μ)
    (hρ : hasShape μ t ρ.asRepresentation) (hhook : Hook μ p) :
    schattenMoment q (H.conditionalAverage hf z (ρ.pullback (H.junctionChart hf eF))) ≤
      Real.exp (-c*Real.log ρ.dimension+e*h*(Real.log A.size+Real.log B.size)-H.cost+c*h+
        (((2*q+1 : ℕ) : ℝ)*((A.size+B.size)*((2*p)*(2*p)) : ℕ)+
          c*((A.size+B.size)*(41*p^2) : ℕ))*Real.log (s+1 : ℕ)) := by
  exact (H.conditional_hook_moment_le_projected p hf eF z ρ hq.ne' μ t hρ hhook).trans
    (H.grid_projected_hook_bound p hp eF hf z q hq c e hc hcq s hpS hAS hBS ρ hR hC)
end CoordinateSweeps.Grid.Holes
end
end
end
end
end
end
end
end
end
end

open scoped Matrix.Norms.L2Operator

end OAI
