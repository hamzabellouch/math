import Mathlib
import OAI.Combinatorics.KMedian.Expanders.CloudSpec

namespace OAI

section Inline_PCPPaddingSpec
namespace MetricKMedian.PCP.Compiler.CloudSpec
open scoped Classical
open CloudProgram CloudOrder

variable {A : Type} [Fintype A] [DecidableEq A] [Inhabited A]
variable (t : CSPTable A) (h : t.WellFormed) [Nonempty (Fin t.2.length)]
noncomputable abbrev padding := padEmbed (C t h) (VO t)
noncomputable def vertexCode (v : GlobalRegularization.Node (C t h)) : ℕ :=
  (ExpanderFamily.vertexEquiv _ v).val
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padding_code (p : CloudCopies.Node (C t h)) :
    vertexCode t h (padding t h p)=((nodeOrder (C t h) (VO t)).equiv p).val := by
  simp only [vertexCode,padding,padEmbed,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Equiv.apply_symm_apply,Fin.castLEEmb_apply,Fin.val_castLE]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padding_index (p : CloudCopies.Node (C t h)) :
    vertexCode t h (padding t h p)=index t (nodeCode (C t h) (VO t) p) := by
  rw [padding_code,index_eq t h]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padding_range (v : GlobalRegularization.Node (C t h)) :
    v∈Set.range (padding t h) ↔ vertexCode t h v<(nodes t).length := by
  rw [nodes_eq t h,List.length_map]
  constructor
  · rintro ⟨p,rfl⟩
    rw [padding_code]
    exact ((nodeOrder (C t h) (VO t)).equiv p).isLt
  · intro hv
    let p := (nodeOrder (C t h) (VO t)).equiv.symm ⟨vertexCode t h v,hv⟩
    refine ⟨p,?_⟩
    apply (ExpanderFamily.vertexEquiv _).injective
    apply Fin.ext
    change vertexCode t h (padding t h p)=vertexCode t h v
    rw [padding_code]
    simp only [p,Equiv.apply_symm_apply]
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padding_get (p : CloudCopies.Node (C t h)) :
    (nodes t)[vertexCode t h (padding t h p)]?=some (nodeCode (C t h) (VO t) p) := by
  rw [nodes_eq t h,padding_code]
  exact Ordered.get_coded _ _ p
omit [Fintype A] [DecidableEq A] [Inhabited A] in
lemma padding_index_lt (p : CloudCopies.Node (C t h)) :
    vertexCode t h (padding t h p)<(nodes t).length :=
  (padding_range t h (padding t h p)).mp ⟨p,rfl⟩
end MetricKMedian.PCP.Compiler.CloudSpec

end Inline_PCPPaddingSpec

end OAI
