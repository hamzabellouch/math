import Mathlib
import OAI.Probability.LatticeSurface.Geometry.CapMatching

namespace OAI

noncomputable section

namespace ExtremalEdges

open Finset

variable {V I : Type*} [Fintype V] [Fintype I]

attribute [local instance] Classical.propDecidable

end ExtremalEdges

namespace ExtremalEdges

attribute [local instance] Classical.propDecidable

local instance capOrientDecidableEq (carrier : Sort*) : DecidableEq carrier :=
  Classical.typeDecidableEq carrier

variable {V I : Type*} [Fintype V] [Fintype I]

omit [Fintype V] [Fintype I] in
theorem orient_matching (e : I → V × V) (pins : Set V)
    (hne : ∀ i, (e i).1 ≠ (e i).2) (hp : ∀ i, ¬ ((e i).1 ∈ pins ∧ (e i).2 ∈ pins))
    (M : Finset I) (hM : (M : Set I).Pairwise (fun i k => Disjoint (edgeEnds e i) (edgeEnds e k))) :
    ∃ (W : Finset V) (r : V → V), W.card = M.card ∧
      (∀ w ∈ W, w ∉ pins) ∧ (∀ w ∈ W, r w ∉ W) ∧
      ∀ w ∈ W, ∃ i ∈ M, (w = (e i).1 ∧ r w = (e i).2) ∨
        (w = (e i).2 ∧ r w = (e i).1) := by
  let o (i : I) : V × V := if (e i).1 ∈ pins then ((e i).2,(e i).1) else e i
  have hof (i : I) : (o i).1 ∉ pins := by
    by_cases ht : (e i).1 ∈ pins
    · simpa [o,ht] using (fun hh => hp i ⟨ht,hh⟩)
    · simp [o,ht]
  have hoo (i : I) : (o i).1 ≠ (o i).2 := by
    by_cases ht : (e i).1 ∈ pins
    · simpa [o,ht] using (hne i).symm
    · simpa [o,ht] using hne i
  have hoEnds (i : I) : edgeEnds o i = edgeEnds e i := by
    by_cases ht : (e i).1 ∈ pins <;> simp [edgeEnds,o,ht,Finset.pair_comm]
  have hMo : (M : Set I).Pairwise (fun i k => Disjoint (edgeEnds o i) (edgeEnds o k)) := by
    simpa only [hoEnds] using hM
  let f : M → V := fun i => (o i).1
  let g : M → V := fun i => (o i).2
  have hf : Function.Injective f := by
    intro i k hik
    apply Subtype.ext
    by_contra hne'
    have hiEnd : f i ∈ edgeEnds o i := by simp [f,edgeEnds]
    have hkEnd : f i ∈ edgeEnds o k := by rw [hik]; simp [f,edgeEnds]
    exact Finset.disjoint_left.mp (hMo i.2 k.2 hne') hiEnd hkEnd
  let W := Finset.univ.image f
  let r := Function.extend f g id
  have hr (i : M) : r (f i) = g i := hf.extend_apply g id i
  refine ⟨W,r,?_,?_,?_,?_⟩
  · simp [W,Finset.card_image_of_injective _ hf]
  · intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    exact hof i
  · intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    rw [hr]
    intro hgw
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hgw
    by_cases hik : i = k
    · subst k
      exact hoo i hk
    · have hne' : (i : I) ≠ k := fun hh => hik (Subtype.ext hh)
      have hd := hMo i.2 k.2 hne'
      have hiEnd : g i ∈ edgeEnds o i := by simp [g,edgeEnds]
      have hkEnd : g i ∈ edgeEnds o k := by rw [← hk]; simp [f,edgeEnds]
      exact Finset.disjoint_left.mp hd hiEnd hkEnd
  · intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    refine ⟨i,i.2,?_⟩
    rw [hr]
    by_cases ht : (e i).1 ∈ pins
    · right; simp [f,g,o,ht]
    · left; simp [f,g,o,ht]

end ExtremalEdges

end

end OAI
