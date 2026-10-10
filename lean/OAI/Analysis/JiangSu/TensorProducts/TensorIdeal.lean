import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.RelativeCoefficient

namespace OAI

section

noncomputable section
namespace NonunitalTensor
open NonunitalRelative
open scoped CStarAlgebra TensorProduct

variable {A D E : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra D] [CStarAlgebra E]
variable (j : A →⋆ₙₐ[ℂ] E) (κ : D →⋆ₐ[ℂ] E)

lemma coefficientSum_append (l m : List (A×D)) :
    coefficientSum j κ (l++m)=coefficientSum j κ l+coefficientSum j κ m := by
  simp [coefficientSum]

lemma coefficientSum_smul (c : ℂ) (l : List (A×D)) :
    coefficientSum j κ (l.map fun z => (c•z.1,z.2))=c•coefficientSum j κ l := by
  induction l with
  | nil => simp [coefficientSum]
  | cons z l ih =>
    simp only [coefficientSum,List.map_cons,List.sum_cons] at ih ⊢
    simp only [map_smul,smul_mul_assoc,ih,smul_add]

lemma mem_span_iff (x : E) : x∈coefficientSpan j κ ↔ ∃ l : List (A×D),coefficientSum j κ l=x := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a,d,rfl⟩ := hx
      exact ⟨[(a,d)],by simp [coefficientSum]⟩
    | zero => exact ⟨[],by simp [coefficientSum]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨l,rfl⟩ := ihx
      obtain ⟨m,rfl⟩ := ihy
      exact ⟨l++m,coefficientSum_append j κ l m⟩
    | smul c x hx ih =>
      obtain ⟨l,rfl⟩ := ih
      exact ⟨l.map (fun z => (c•z.1,z.2)),coefficientSum_smul j κ c l⟩
  · rintro ⟨l,rfl⟩
    induction l with
    | nil => simp [coefficientSum]
    | cons z l ih =>
      simpa only [coefficientSum,List.map_cons,List.sum_cons] using
        (coefficientSpan j κ).add_mem (coefficientSpan_mem j κ z.1 z.2) ih

variable (hc : ∀ a d,Commute (j a) (κ d))

include hc in

include hc in

lemma tensorIdeal_coefficient_dense (b : tensorIdeal j κ hc) {ε : ℝ} (hε : 0<ε) :
    ∃ l : List (A×D),‖coefficientSum j κ l-(b:E)‖<ε := by
  have hb : (b:E)∈closure (coefficientSpan j κ : Set E) := b.property
  obtain ⟨x,hx,hxb⟩ := Metric.mem_closure_iff.mp hb ε hε
  obtain ⟨l,rfl⟩ := (mem_span_iff j κ x).mp hx
  exact ⟨l,by simpa only [dist_eq_norm,norm_sub_rev] using hxb⟩

end NonunitalTensor

end
end

end OAI
