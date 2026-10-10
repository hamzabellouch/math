import Mathlib
import OAI.Combinatorics.KMedian.Binary.BinaryListExtras
import OAI.Combinatorics.KMedian.Preparation.SupplierListOperations
import OAI.Combinatorics.KMedian.Preparation.PreparedLawProgram

namespace OAI


                                                  
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)
open SparseIntegerLaw.BinarySparse
variable {τ : ℝ} (qR : FixedBatch.RationalParameters τ)
structure Input where
  f : ℕ
  n : ℕ
  S : Data f n
abbrev Input.raw (x : Input) := supplierView x.S
abbrev Input.encode (x : Input) := enc x.raw

def qData (x : SupplierRaw) : QRow := (weightsData x).map (fun w => w/qR.g)
@[fun_prop] theorem qData_poly : Poly (qData qR) := by unfold qData; apply list_map <;> fun_prop
 theorem qData_view (x : Input) : qData qR x.raw=List.ofFn (q x.S.y x.S.P x.S.A x.S.c x.S.γ qR.g) := by
  unfold qData Input.raw
  rw [weightsData_view,List.map_ofFn]
  rfl

def Input.prepared (x : Input) : SparsePrepared.Program.Input :=
  ⟨x.n,size x.f x.n,x.f,D x.S.A,a,q x.S.y x.S.P x.S.A x.S.c x.S.γ qR.g,
    x.S.P,x.S.y,x.S.p,qR.Δ,x.S.hy,x.S.hp,a_bounds,
    q_nonneg _ _ _ _ _ _ x.S.hy x.S.hc0 x.S.hγ.le (FixedParameters.positive qR).le⟩
def prepareData (x : SupplierRaw) : SparsePrepared.Program.Raw :=
  ((targetsData x,(qData qR x,(x.2.1,(x.1,(x.2.2.2.1,qR.Δ))))),flagsData x)
@[fun_prop] theorem prepareData_poly : Poly (prepareData qR) := by unfold prepareData; fun_prop
 theorem prepareData_view (x : Input) : prepareData qR x.raw=(x.prepared qR).raw := by
  unfold prepareData
  rw [qData_view]
  change ((targetsData (supplierView x.S),_),flagsData (supplierView x.S))=_
  rw [targetsData_view,flagsData_view]
  rfl
noncomputable def preparedInputProgram : PolyProgram Input.encode SparsePrepared.Program.Input.encode (Input.prepared qR) :=
  (prepareData_poly qR).program.recode Input.raw (fun _ => rfl) (fun x => congrArg enc (prepareData_view qR x))

theorem ofFn_physical {f n : ℕ} {α : Type} (F : Sum (Fin f) (Fin n × Fin f) → α) :
    List.ofFn (fun e => F (physicalIndex e))=List.ofFn (fun i => F (.inl i)) ++
      (List.ofFn (fun t => List.ofFn (fun i => F (.inr (t,i))))).flatten := by
  conv_lhs => rw [List.ofFn_add]
  simp only [physicalIndex,Equiv.trans_apply,Equiv.sumCongr_apply,finSum_symm_castLE,
    finSumFinEquiv_symm_apply_natAdd,Sum.map_inl,Sum.map_inr,Equiv.refl_apply]
  rw [RoundingList.ofFn_product]

theorem index_inl {f n : ℕ} (i : Fin f) : (index (f:=f) (n:=n)).symm (.inl i)=Fin.castAdd (n*n+n) i := by
  apply (index (f:=f) (n:=n)).injective
  simp only [Equiv.apply_symm_apply,index,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumCongr_apply,Sum.map_inl,Equiv.refl_apply]

abbrev PreparedRaw := SparsePrepared.Program.PreparedRaw

def countsData (x : SupplierRaw × PreparedRaw) : List ℕ :=
  ((indices x.1.1).map (fun i => ⌊(qData qR x.1)[i]?.getD 0⌋₊+
    if 0 < x.2.1.1[i]?.getD 0 then 1 else 0)) ++ x.2.2.flatten
@[fun_prop] theorem countsData_poly : Poly (countsData qR) := by
  unfold countsData
  apply append_poly
  · apply list_map <;> fun_prop
  · exact comp (⟨listFlatten (enc : ℕ → List Bool) 0⟩ : Poly (List.flatten : List (List ℕ) → List ℕ)) (by fun_prop)

theorem countsData_view (x : Input) (z : SparseSignedPreparation.State x.n (size x.f x.n) × SparseCounts.Table x.f x.n) :
    countsData qR (x.raw,SparsePrepared.Program.view z)=List.ofFn (counts x.S.y x.S.P x.S.A x.S.c x.S.γ qR.g z) := by
  change _=List.ofFn (fun e => Sum.elim _ _ (physicalIndex e))
  rw [ofFn_physical]
  simp only [countsData,Input.raw,supplierView,indices,List.length_ofFn,RoundingList.range_finRange,
    ← List.ofFn_eq_map,List.map_ofFn,Function.comp_def,SparsePrepared.Program.view,
    SparseSignedPreparation.Program.view,SparseCounts.ListOperation.view]
  congr 1
  congr 1
  funext i
  have hq := qData_view qR x
  change (⌊(qData qR x.raw)[i.val]?.getD 0⌋₊+if 0<(z.1.1.toList)[i.val]?.getD 0 then 1 else 0)=_
  rw [hq]
  simp only [SparseOuterLaw.outsideCount,SparseGridRounding.base,index_inl,List.getElem?_ofFn,
    dite_eq_left (show i.val<size x.f x.n from lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)),
    Option.getD_some,Vector.getElem?_toList,Vector.getElem?_eq_getElem (show i.val<size x.f x.n from lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)),
    RationalWeightedStep.point]
  rfl

def tablesData (x : SupplierRaw × List PreparedRaw) : List (List ℕ) := x.2.map (fun z => countsData qR (x.1,z))
@[fun_prop] theorem tablesData_poly : Poly (tablesData qR) := by unfold tablesData; apply list_map <;> fun_prop
noncomputable def tablesProgram : PolyProgram Input.encode (enc : List (List ℕ) → List Bool)
    (fun x => (x.S.tables qR).map List.ofFn) := by
  let r : PolyProgram Input.encode enc Input.raw := (identity enc).recode Input.raw (fun _ => rfl) (fun _ => rfl)
  let states := preparedInputProgram qR |>.comp SparsePrepared.Program.program |>.comp (snd el (encodeList enc))
  exact (r.fanout states |>.comp (tablesData_poly qR).program).congr _ (fun x => by
    simp only [Function.comp_def,tablesData,SparsePrepared.Program.Input.result,List.map_map]
    change ((x.S.law qR).states.toList.map (fun z => countsData qR (x.raw,SparsePrepared.Program.view z)))=_
    simp only [countsData_view,Data.tables,List.map_map,Function.comp_def])
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
