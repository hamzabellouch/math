import Mathlib
import OAI.Combinatorics.KMedian.Expanders.CloudOrder
import OAI.Combinatorics.KMedian.Expanders.CloudPrograms

namespace OAI

section Inline_PCPCloudSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder

variable {A : Type}
variable (t : CSPTable A) (h : t.WellFormed)
noncomputable abbrev C := t.csp h
abbrev VO := Ordered.fin t.1.length
abbrev EO := Ordered.fin t.2.length
def dartCode (d : CloudCopies.Dart (E := Fin t.2.length)) : Dart := (d.1.val,d.2)
lemma dartCode_injective : Function.Injective (dartCode t) := by
  rintro ⟨e,b⟩ ⟨f,c⟩ hh
  have he : e=f := Fin.ext (congrArg Prod.fst hh)
  have hb : b=c := congrArg Prod.snd hh
  subst f; subst c; rfl
lemma finRange_val (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp
lemma darts_eq : darts t=((dartOrder (EO t)).entries.map (dartCode t)) := by
  unfold darts dartOrder Ordered.prod EO Ordered.fin boolOrder
  simp only [List.product,List.map_flatMap,List.map_cons,List.map_nil]
  rw [← finRange_val t.2.length,List.flatMap_map]
  rfl
lemma endpoint_eq (d : CloudCopies.Dart (E := Fin t.2.length)) :
    endpoint t (dartCode t d)=(CloudCopies.endpoint (C t h) d).val := by
  simp only [endpoint,dartCode,CloudCopies.endpoint,C,CSPTable.csp,CSPTable.row]
  rw [List.getElem?_eq_getElem d.1.isLt]
  cases d with
  | mk e b => cases b <;> rfl
lemma incident_eq (v : CloudCopies.Active (C t h)) :
    incident t v.val.val=((incidentOrder (C t h) (EO t) v).entries.map (fun d => dartCode t d.val)) := by
  unfold incident incidentOrder
  change _=List.map ((dartCode t) ∘ Subtype.val) _
  rw [← List.map_map,Ordered.filter_val,darts_eq,List.filter_map]
  congr 1
  congr 1
  funext d
  simp only [Function.comp_def,endpoint_eq t h,CloudCopies.owner,Subtype.ext_iff,Fin.ext_iff]
lemma active_test (v : Fin t.1.length) :
    (!(incident t v.val).isEmpty)=decide (v∈Set.range (CloudCopies.endpoint (C t h))) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.not_eq_true',List.isEmpty_eq_false_iff_exists_mem,Bool.decide_iff,incident,
    List.mem_filter,darts_eq,List.mem_map]
  constructor
  · rintro ⟨d,⟨⟨e,he,rfl⟩,hh⟩⟩
    exact ⟨e,Fin.ext (by simpa only [Bool.decide_iff,endpoint_eq t h] using hh)⟩
  · rintro ⟨e,he⟩
    refine ⟨dartCode t e,⟨⟨e,(dartOrder (EO t)).all e,rfl⟩,?_⟩⟩
    simp only [endpoint_eq t h,he]
lemma active_eq : active t=((activeOrder (C t h) (VO t)).entries.map (fun v => v.val.val)) := by
  unfold active activeOrder
  change _=List.map (Fin.val ∘ Subtype.val) _
  rw [← List.map_map]
  have hv := @Ordered.filter_val (Fin t.1.length) (VO t) (fun v => v∈Set.range (CloudCopies.endpoint (C t h))) (Classical.decPred _)
  rw [hv,← finRange_val t.1.length,List.filter_map]
  congr 1
  congr 1
  funext v
  have hv := active_test t h v
  apply Bool.eq_iff_iff.mpr
  simpa only [Function.comp_def,Bool.decide_iff] using Bool.eq_iff_iff.mp hv
lemma fin_equiv_val (n : ℕ) (dec : DecidableEq (Fin n)) (i : Fin n) :
    (@Ordered.equiv (Fin n) dec (Ordered.fin n) i).val=i.val := by
  have hg := @Ordered.get_equiv (Fin n) dec (Ordered.fin n) i
  change (List.finRange n)[(@Ordered.equiv (Fin n) dec (Ordered.fin n) i).val]=i at hg
  simpa only [List.getElem_finRange,Fin.val_cast] using congrArg Fin.val hg
lemma cloud_table (v : CloudCopies.Active (C t h)) :
    cloud t v.val.val=RotationTable.table (ExpanderFamily.graph (CloudCopies.depth (C t h) v))
      (ExpanderFamily.vertexEquiv (CloudCopies.depth (C t h) v)) := by
  unfold cloud
  rw [Expander.generate_table]
  have hi : (incident t v.val.val).length=Fintype.card (CloudCopies.Incident (C t h) v) := by
    rw [incident_eq,List.length_map,Ordered.length_card]
  change (fun n => RotationTable.table (ExpanderFamily.graph n) (ExpanderFamily.vertexEquiv n)) _ = _
  congr 1
  simp only [CloudCopies.depth,List.length_map,List.length_tail,hi]
  apply congrArg ExpanderFamily.level
  apply congrArg (fun n : ℕ => n-1)
  exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
lemma cloud_length (v : CloudCopies.Active (C t h)) :
    (cloud t v.val.val).length=(Fintype.card ExpanderFamily.Branch)^(CloudCopies.depth (C t h) v) := by
  rw [cloud_table t h,RotationTable.table_length]
lemma nodeCode_eq (p : CloudCopies.Node (C t h)) :
    nodeCode (C t h) (VO t) p=(p.1.val.val,(ExpanderFamily.vertexEquiv _ p.2).val) := by
  unfold nodeCode VO
  apply Prod.ext
  · exact fin_equiv_val _ _ _
  · rfl
lemma nodes_eq : nodes t=((nodeOrder (C t h) (VO t)).entries.map (nodeCode (C t h) (VO t))) := by
  unfold nodes
  rw [active_eq t h,List.flatMap_map]
  unfold nodeOrder Ordered.sigma
  simp only [List.sigma,List.map_flatMap,List.map_map]
  apply congrArg (fun f : CloudCopies.Active (C t h) → List (ℕ × ℕ) => ((activeOrder (C t h) (VO t)).entries).flatMap f)
  funext v
  rw [cloud_length t h v]
  unfold copyOrder Ordered.map Ordered.fin
  simp only [List.map_map,Function.comp_def,nodeCode_eq,Equiv.apply_symm_apply]
  rw [← finRange_val]
  simp only [List.map_map,Function.comp_def]
lemma index_eq (p : CloudCopies.Node (C t h)) :
    index t (nodeCode (C t h) (VO t) p)=((nodeOrder (C t h) (VO t)).equiv p).val := by
  unfold index
  rw [nodes_eq t h]
  rw [Ordered.index_coded _ _ (nodeCode_injective (C t h) (VO t)) p]
  congr 1
  funext q
  simp only [Prod.ext_iff]
lemma global_table [Nonempty (Fin t.2.length)] :
    global t=RotationTable.table (ExpanderFamily.graph (GlobalRegularization.depth (C t h)))
      (ExpanderFamily.vertexEquiv (GlobalRegularization.depth (C t h))) := by
  unfold global
  rw [Expander.generate_table]
  have hn : (nodes t).length=Fintype.card (CloudCopies.Node (C t h)) := by
    rw [nodes_eq t h,List.length_map,Ordered.length_card]
  change (fun n => RotationTable.table (ExpanderFamily.graph n) (ExpanderFamily.vertexEquiv n)) _ = _
  congr 1
  simp only [GlobalRegularization.depth,List.length_map,List.length_tail,hn]
  apply congrArg ExpanderFamily.level
  apply congrArg (fun n : ℕ => n-1)
  exact congrArg (@Fintype.card _) (Subsingleton.elim _ _)
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudSpec

end OAI
