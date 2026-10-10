import Mathlib
import OAI.Combinatorics.KMedian.Amplification.FlexibleCloud
import OAI.Combinatorics.KMedian.Expanders.CloudSpec

namespace OAI

section Inline_PCPCloudEmbedding
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder

variable {A : Type}
variable (t : CSPTable A) (h : t.WellFormed)
noncomputable abbrev emb := FlexibleCloud.dartEmbed (C t h) (cloudEmbed (C t h) (EO t))
lemma emb_incident (v : CloudCopies.Active (C t h)) (d : CloudCopies.Incident (C t h) v) :
    emb t h d.val=⟨v,cloudEmbed (C t h) (EO t) v d⟩ := by
  rcases d with ⟨d,hd⟩
  subst v
  rfl
lemma emb_code (d : CloudCopies.Dart (E := Fin t.2.length)) :
    nodeCode (C t h) (VO t) (emb t h d)=
      ((CloudCopies.endpoint (C t h) d).val,
        ((incidentOrder (C t h) (EO t) (CloudCopies.owner (C t h) d)).equiv ⟨d,rfl⟩).val) := by
  rw [nodeCode_eq]
  apply Prod.ext
  · rfl
  change (ExpanderFamily.vertexEquiv _ (cloudEmbed (C t h) (EO t) _ ⟨d,rfl⟩)).val=_
  rw [cloudEmbed_index]
  simp only [Ordered.equiv_val,List.idxOf]
  congr 1
  funext x
  simp only [Bool.beq_eq_decide_eq]
lemma emb_range (p : CloudCopies.Node (C t h)) :
    p∈Set.range (emb t h) ↔ (ExpanderFamily.vertexEquiv _ p.2).val<(incident t p.1.val.val).length := by
  constructor
  · rintro ⟨d,rfl⟩
    rw [incident_eq t h,List.length_map]
    change (ExpanderFamily.vertexEquiv _ (cloudEmbed (C t h) (EO t) _ ⟨d,rfl⟩)).val<_
    rw [cloudEmbed_index]
    exact List.idxOf_lt_length_iff.mpr ((incidentOrder (C t h) (EO t) _).all ⟨d,rfl⟩)
  · intro hp
    rcases p with ⟨v,p⟩
    rw [incident_eq t h,List.length_map] at hp
    let d := (incidentOrder (C t h) (EO t) v).equiv.symm
      ⟨(ExpanderFamily.vertexEquiv _ p).val,hp⟩
    refine ⟨d.val,?_⟩
    rw [emb_incident t h v d]
    apply congrArg (Sigma.mk v)
    apply (ExpanderFamily.vertexEquiv _).injective
    apply Fin.ext
    rw [cloudEmbed_index]
    calc
      _ = ((incidentOrder (C t h) (EO t) v).equiv d).val := by
        simp only [Ordered.equiv_val,List.idxOf]
        congr 1
        funext x
        simp only [Bool.beq_eq_decide_eq]
      _ = _ := by simp only [d,Equiv.apply_symm_apply]
lemma emb_get (d : CloudCopies.Dart (E := Fin t.2.length)) :
    (incident t (nodeCode (C t h) (VO t) (emb t h d)).1)[(nodeCode (C t h) (VO t) (emb t h d)).2]?=some (dartCode t d) := by
  rw [emb_code t h d]
  change (incident t (CloudCopies.owner (C t h) d).val.val)[_]?=_
  rw [incident_eq t h]
  exact Ordered.get_coded _ (fun e : CloudCopies.Incident (C t h) (CloudCopies.owner (C t h) d) => dartCode t e.val) ⟨d,rfl⟩
lemma dartIndex_eq (v : CloudCopies.Active (C t h)) (d : CloudCopies.Incident (C t h) v) :
    dartIndex t v.val.val (dartCode t d.val)=((incidentOrder (C t h) (EO t) v).equiv d).val := by
  unfold dartIndex
  rw [incident_eq t h]
  rw [Ordered.index_coded _ (fun e : CloudCopies.Incident (C t h) v => dartCode t e.val) ((dartCode_injective t).comp Subtype.val_injective) d]
  congr 1
  funext q
  simp only [Prod.ext_iff]
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPCloudEmbedding

end OAI
