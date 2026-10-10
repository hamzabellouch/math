import Mathlib
import OAI.Combinatorics.KMedian.Process.BatchOrdinalCodes
import OAI.Combinatorics.KMedian.Process.BatchGraphData

namespace OAI


                                          
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

 theorem erase_code (e : HeavyAction D H) :
    ActionArrays.erase (view r D H) (code r D H e)=sets r ((heavy D H).erase e) := by
  cases e with
  | inl e =>
    change ActionArrays.erase (view r D H) (r.symm e.val).val=sets r (D.erase e.val)
    simp only [ActionArrays.erase,view,sets_length,ite_eq_left (r.symm e.val).isLt,
      List.getElem?_ofFn,dite_eq_left (r.symm e.val).isLt,Option.getD_some,Fin.eta,OrderIso.apply_symm_apply]
  | inr e =>
    have hc : ¬ n+(r.symm e.val.1).val*n+(r.symm e.val.2).val<n := by omega
    change ActionArrays.erase (view r D H) (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=sets r {e.val.2}
    simp only [ActionArrays.erase,view,sets_length,ite_eq_right hc,indices,
      RoundingList.range_finRange,List.map_map,Function.comp_def]
    rw [← List.ofFn_eq_map]
    apply congrArg List.ofFn
    funext i
    rw [show ActionList.child n (n+(r.symm e.val.1).val*n+(r.symm e.val.2).val)=(r.symm e.val.2).val from child_code r D H e]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,mem_map_equiv,mem_singleton,← Fin.ext_iff]
    change (i=r.symm e.val.2) ↔ r i=e.val.2
    exact r.eq_symm_apply
 theorem bal_code (Δ : ℕ) (e : HeavyAction D H) :
    ActionArrays.bal (view r D H,Δ) (code r D H e)=true ↔ e∈balanced (heavy D H) Δ := by
  unfold ActionArrays.bal
  rw [Bool.and_eq_true,decide_eq_true_eq,decide_eq_true_eq]
  rw [show (view r D H).2.length=n from sets_length r H,erase_code,sets_card,code_light]
  change (e.isLeft=true ∧ ((heavy D H).erase e).card=Δ) ↔
    e∈((univ.filter (fun e : HeavyAction D H => e.isLeft=true)).filter (fun e => ((heavy D H).erase e).card=Δ))
  simp only [mem_filter,mem_univ,true_and]
 omit [Fintype I] in
 theorem overlap_sets (A B : Finset I) :
    ActionArrays.overlap (sets r A) (sets r B)=true ↔ (A∩B).Nonempty := by
  rw [sets,sets,ActionArrays.overlap_view,← map_inter]
  exact Finset.map_nonempty
 theorem conflict_code (Δ : ℕ) (e f : HeavyAction D H) :
    ActionArrays.conflict (view r D H,Δ) (code r D H e) (code r D H f)=true ↔ f∈conflicts (heavy D H) Δ e := by
  simp only [ActionArrays.conflict,Bool.and_eq_true,Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not,
    bal_code,erase_code,overlap_sets]
  have he : code r D H f≠code r D H e ↔ f≠e :=
    not_congr (@StrictMono.injective _ _ (actionOrder D H) _ _ (code_strictMono r D H)).eq_iff
  simp only [he]
  unfold conflicts
  split_ifs with hb <;> simp only [mem_filter,notMem_empty,iff_false] <;> tauto
 omit [Fintype I] in
 theorem bias_code (m : I → ℚ) (p φ : ℚ) (e : HeavyAction D H) :
    ActionArrays.bias (((p,φ),List.ofFn (fun i => m (r i))),n) (code r D H e)=
      RationalBatchData.bias m p φ (heavyParent D H e) := by
  simp only [ActionArrays.bias,parent_code,List.getElem?_ofFn,dite_eq_left (Fin.isLt _),Option.getD_some,
    Fin.eta,OrderIso.apply_symm_apply,RationalBatchData.bias]

 theorem data_view (m : I → ℚ) (p φ : ℚ) (Δ : ℕ) :
    ActionArrays.data ((((p,φ),List.ofFn (fun i => m (r i))),Δ),view r D H)=
    ((setView ((balanced (heavy D H) Δ).map (enumeration D H).symm.toEmbedding),
      List.ofFn (fun i => setView ((conflicts (heavy D H) Δ (enumeration D H i)).map (enumeration D H).symm.toEmbedding))),
      (p,List.ofFn (fun i => RationalBatchData.bias m p φ (heavyParent D H (enumeration D H i))))) := by
  unfold ActionArrays.data
  dsimp only
  rw [codes_eq]
  apply Prod.ext
  · apply Prod.ext
    · dsimp only
      rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,mem_map_equiv,Equiv.symm_symm,Function.comp_def]
      exact bal_code r D H Δ (enumeration D H i)
    · dsimp only
      simp only [List.map_ofFn]
      apply congrArg List.ofFn
      funext i
      apply congrArg List.ofFn
      funext j
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq,mem_map_equiv,Equiv.symm_symm,Function.comp_def]
      exact conflict_code r D H Δ (enumeration D H i) (enumeration D H j)
  · apply Prod.ext
    · rfl
    · dsimp only
      rw [List.map_ofFn,show (view r D H).2.length=n from sets_length r H]
      apply congrArg List.ofFn
      funext i
      exact bias_code r D H m p φ (enumeration D H i)

 def graphView (G : I → Finset I) : Table := List.ofFn (fun i => sets r (G (r i)))
 theorem transpose_graph (G : I → Finset I) :
    GraphData.transpose (graphView r G)=List.ofFn (fun h => sets r ((graph G).erase (r h))) := by
  simp only [GraphData.transpose,graphView,indices,List.length_ofFn,RoundingList.range_finRange,
    Function.comp_def,← List.ofFn_eq_map,List.map_ofFn,sets_eq,List.getElem?_ofFn,
    dite_eq_left (Fin.isLt _),Option.getD_some,Fin.eta,graph,mem_filter,mem_univ,true_and]
 theorem masses_graph (G : I → Finset I) (g : ℚ) :
    GraphData.masses (g,graphView r G)=List.ofFn (fun h => graphMass G g (r h)) := by
  simp only [GraphData.masses,transpose_graph,List.map_ofFn,Function.comp_def,sets_card]
  rfl
 theorem heavy_graph (G : I → Finset I) (g b : ℚ) :
    GraphData.heavy (b,GraphData.masses (g,graphView r G))=sets r (heavySet (graphMass G g) b) := by
  rw [masses_graph]
  simp only [GraphData.heavy,GraphData.amount_view,List.map_ofFn,Function.comp_def,sets_eq,
    heavySet,mem_filter,mem_univ,true_and]
  have ha : RationalBatchData.amount (fun h => graphMass G g (r h))=RationalBatchData.amount (graphMass G g) :=
    r.toEquiv.sum_comp (fun h => max (1-graphMass G g h) 0)
  rw [ha]
 theorem prepare_graph (G : I → Finset I) (g b p φ : ℚ) (Δ : ℕ) :
    GraphData.prepare (((g,b),(Δ,(p,φ))),graphView r G)=
      ((((p,φ),List.ofFn (fun h => graphMass G g (r h))),Δ),view r (graph G) (heavySet (graphMass G g) b)) := by
  unfold GraphData.prepare
  dsimp only
  rw [heavy_graph,masses_graph,transpose_graph]
  rfl
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
