import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Polytabloids

namespace OAI

section
namespace PartialPermutation
namespace YoungTabloid
noncomputable section
open Finset
open scoped Classical

def spechtSub (μ : YoungDiagram) : Subrepresentation (tabloidRep μ) where
  toSubmodule := Submodule.span ℂ (Set.range (fun g => tabloidRep μ g (polytabloid μ)))
  apply_mem_toSubmodule g v hv := by
    induction hv using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨h,rfl⟩ := hu
      apply Submodule.subset_span
      exact ⟨g*h,by simp [Module.End.mul_apply]⟩
    | zero => simp
    | add u v hu hv ih ih' => simpa only [map_add] using Submodule.add_mem _ ih ih'
    | smul a u hu ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

lemma polytabloid_mem_specht (μ : YoungDiagram) : polytabloid μ ∈ spechtSub μ := by
  apply Submodule.subset_span
  exact ⟨1,by simp⟩

lemma specht_le_of_polytabloid_mem (μ : YoungDiagram) (W : Subrepresentation (tabloidRep μ))
    (hw : polytabloid μ ∈ W) : spechtSub μ ≤ W := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g,rfl⟩
  exact W.apply_mem_toSubmodule g hw

lemma antisym_mem_invariant (μ : YoungDiagram) (W : Subrepresentation (tabloidRep μ))
    {f : EuclideanSpace ℂ (Tabloid μ)} (hf : f∈W) : antisym μ f∈W := by
  simp only [antisym,LinearMap.sum_apply,LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro c _
  exact W.toSubmodule.smul_mem _ (W.apply_mem_toSubmodule c.1 hf)

lemma specht_detect (μ : YoungDiagram) (f : EuclideanSpace ℂ (Tabloid μ))
    (hf : f∈spechtSub μ) (hne : f≠0) :
    ∃ g : Equiv.Perm μ.cells, inner ℂ (polytabloid μ) (tabloidRep μ g f)≠0 := by
  by_contra hn
  simp only [not_exists,not_not] at hn
  have hz (v) (hv : v∈(spechtSub μ).toSubmodule) : inner ℂ v f=0 := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨g,rfl⟩ := hv
      have hh := tabloidRep_unitary μ g (polytabloid μ) (tabloidRep μ g⁻¹ f)
      simpa [hn] using hh
    | zero => simp
    | add v w hv hw ih ih' => simp [ih,ih']
    | smul a v hv ih => simp [ih]
  exact hne (inner_self_eq_zero.mp (hz f hf))

lemma specht_minimal (μ : YoungDiagram) (W : Subrepresentation (tabloidRep μ))
    (hW : W ≤ spechtSub μ) : W=⊥ ∨ W=spechtSub μ := by
  by_cases hw : W=⊥
  · exact Or.inl hw
  right
  have hne : W.toSubmodule≠⊥ := by
    intro hh
    exact hw (Subrepresentation.ext hh)
  obtain ⟨f,hf,hf0⟩ := W.toSubmodule.ne_bot_iff.mp hne
  obtain ⟨g,hg⟩ := specht_detect μ f (hW hf) hf0
  have ha := antisym_mem_invariant μ W (W.apply_mem_toSubmodule g hf)
  rw [antisym_eq_inner] at ha
  have he : polytabloid μ∈W := (W.toSubmodule.smul_mem_iff hg).mp ha
  exact le_antisymm hW (specht_le_of_polytabloid_mem μ W he)

def spechtRep (μ : YoungDiagram) := (spechtSub μ).toRepresentation

instance specht_irreducible (μ : YoungDiagram) : Representation.IsIrreducible (spechtRep μ) := by
  let S := (spechtSub μ).toSubmodule
  let e : S := ⟨polytabloid μ,polytabloid_mem_specht μ⟩
  have he : e≠0 := fun h => polytabloid_ne_zero μ (congrArg Subtype.val h)
  let : Nontrivial (Subrepresentation (spechtRep μ)) := by
    refine ⟨⟨⊥,⊤,?_⟩⟩
    intro h
    have hh : e ∈ (⊥ : Subrepresentation (spechtRep μ)) := by rw [h]; trivial
    exact he hh
  constructor
  intro σ
  let W : Subrepresentation (tabloidRep μ) :=
    { toSubmodule := σ.toSubmodule.map S.subtype
      apply_mem_toSubmodule := by
        intro g v hv
        obtain ⟨u,hu,rfl⟩ := hv
        exact ⟨spechtRep μ g u,σ.apply_mem_toSubmodule g hu,rfl⟩ }
  have hW : W ≤ spechtSub μ := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := hv
    exact u.2
  rcases specht_minimal μ W hW with hw | hw
  · left
    apply Subrepresentation.ext
    apply σ.toSubmodule.eq_bot_iff.mpr
    intro u hu
    have h : u.1 ∈ W := ⟨u,hu,rfl⟩
    rw [hw] at h
    exact Subtype.ext h
  · right
    apply Subrepresentation.ext
    apply top_unique
    intro u _
    have h : u.1∈W := by rw [hw]; exact u.2
    obtain ⟨v,hv,heq⟩ := h
    have huv : v=u := Subtype.ext heq
    exact huv ▸ hv

end
end YoungTabloid
end PartialPermutation

end

end OAI
