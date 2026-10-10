import Mathlib
import OAI.Combinatorics.KMedian.Amplification.RegularPrograms
import OAI.Combinatorics.KMedian.Expanders.CloudEmbedding
import OAI.Combinatorics.KMedian.Machines.MatchingLaws

namespace OAI

section Inline_PCPMatchingSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder RegularProgram

variable {A : Type}
variable (t : CSPTable A) (h : t.WellFormed)
lemma emb_code_lt (d : CloudCopies.Dart (E := Fin t.2.length)) :
    (nodeCode (C t h) (VO t) (emb t h d)).2 <
      (incident t (nodeCode (C t h) (VO t) (emb t h d)).1).length := by
  rw [nodeCode_eq]
  exact (emb_range t h (emb t h d)).mp ⟨d,rfl⟩
lemma matchStep_image (d : CloudCopies.Dart (E := Fin t.2.length)) :
    matchStep t (nodeCode (C t h) (VO t) (emb t h d))=
      nodeCode (C t h) (VO t) (emb t h (CloudCopies.dartFlip d)) := by
  have hl := emb_code_lt t h d
  have hg := emb_get t h d
  simp only [matchStep,ite_eq_left hl,hg,Option.getD_some]
  change (endpoint t (dartCode t (CloudCopies.dartFlip d)),
    dartIndex t (endpoint t (dartCode t (CloudCopies.dartFlip d))) (dartCode t (CloudCopies.dartFlip d)))=_
  rw [endpoint_eq t h,emb_code t h]
  apply Prod.ext
  · rfl
  exact dartIndex_eq t h (CloudCopies.owner (C t h) (CloudCopies.dartFlip d)) ⟨CloudCopies.dartFlip d,rfl⟩
lemma matchStep_correct (p : CloudCopies.Node (C t h)) :
    matchStep t (nodeCode (C t h) (VO t) p)=nodeCode (C t h) (VO t)
      ((FlexibleCloud.matchingGraph (C t h) (cloudEmbed (C t h) (EO t))).step p ()) := by
  by_cases hp : p∈Set.range (emb t h)
  · obtain ⟨d,rfl⟩ := hp
    rw [matchStep_image t h]
    rw [FlexibleCloud.matching_step_image]
  · have hn := mt (emb_range t h p).mpr hp
    have hn' : ¬(nodeCode (C t h) (VO t) p).2<(incident t (nodeCode (C t h) (VO t) p).1).length := by
      rw [nodeCode_eq]; exact hn
    rw [matchStep,ite_eq_right hn']
    rw [FlexibleCloud.matching_step_outside _ _ p hp]
lemma row_allowed (e : Fin t.2.length) : (CSPTable.row t e.val).2.2=(C t h).allowed e := by
  simp only [CSPTable.row,List.getElem?_eq_getElem e.isLt,Option.getD_some]
  rfl
variable [Fintype A] [DecidableEq A]
lemma swap_image (R : Finset (A × A)) : R.image Prod.swap=Finset.univ.filter (fun q : A × A => (q.2,q.1)∈R) := by
  ext ⟨a,b⟩
  simp only [Finset.mem_image,Prod.exists,Prod.swap_prod_mk,Prod.mk.injEq,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨x,y,hxy,hya,hxb⟩
    subst x; subst y; exact hxy
  · intro hab
    exact ⟨b,a,hab,rfl,rfl⟩
lemma matchAllowed_image (d : CloudCopies.Dart (E := Fin t.2.length)) :
    matchAllowed t (nodeCode (C t h) (VO t) (emb t h d))=(CloudCopies.dartCSP (C t h)).allowed (d,()) := by
  have hl := emb_code_lt t h d
  have hg := emb_get t h d
  simp only [matchAllowed,ite_eq_left hl,hg,Option.getD_some,dartCode,row_allowed t h]
  rcases d with ⟨e,b⟩
  cases b
  · simp only [Bool.false_eq_true,↓reduceIte,CloudCopies.dartCSP,Finset.filter_mem_eq_inter,Finset.univ_inter]
  · simp only [↓reduceIte,CloudCopies.dartCSP]
    apply Finset.ext
    rintro ⟨a,b⟩
    simp only [Finset.mem_image,Prod.exists,Finset.mem_filter,Finset.mem_univ,true_and,Prod.swap_prod_mk,Prod.mk.injEq]
    constructor
    · rintro ⟨x,y,hxy,hya,hxb⟩
      subst x; subst y; exact hxy
    · intro hab
      exact ⟨b,a,hab,rfl,rfl⟩
lemma matchAllowed_correct (p : CloudCopies.Node (C t h)) :
    matchAllowed t (nodeCode (C t h) (VO t) p)=
      (FlexibleCloud.matchingCSP (C t h) (cloudEmbed (C t h) (EO t))).allowed (p,()) := by
  by_cases hp : p∈Set.range (emb t h)
  · obtain ⟨d,rfl⟩ := hp
    rw [matchAllowed_image t h]
    exact (FlexibleCloud.matching_allowed_image (C t h) (cloudEmbed (C t h) (EO t)) d).symm
  · have hn := mt (emb_range t h p).mpr hp
    have hn' : ¬(nodeCode (C t h) (VO t) p).2<(incident t (nodeCode (C t h) (VO t) p).1).length := by
      rw [nodeCode_eq]; exact hn
    rw [matchAllowed,ite_eq_right hn']
    exact (FlexibleCloud.matching_allowed_outside (C t h) (cloudEmbed (C t h) (EO t)) p hp).symm
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPMatchingSpec

end OAI
