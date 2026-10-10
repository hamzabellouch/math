import Mathlib
import OAI.Geometry.Borsuk.Simplicial.MemSupportSimplex

namespace OAI

namespace BorsukNine.SimplicialChains
open Finset
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def subdivSimplex (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    (s : Finset V) : Chain L :=
  if _hs : s.Nonempty then
    if s.card = 1 then simplex L {b s}
    else cone L (b s) (∑ a ∈ s.attach, subdivSimplex L b (s.erase a.val))
  else 0
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem a.property

@[simp] lemma subdivSimplex_empty (L : PreAbstractSimplicialComplex W) (b : Finset V → W) :
    subdivSimplex L b ∅ = 0 := by rw [subdivSimplex]; simp

lemma subdivSimplex_one (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    {s : Finset V} (hc : s.card = 1) : subdivSimplex L b s = simplex L {b s} := by
  have hn : s.Nonempty := Finset.card_pos.mp (by omega)
  rw [subdivSimplex, dite_eq_left hn, ite_eq_left hc]

lemma subdivSimplex_many (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    {s : Finset V} (hn : s.Nonempty) (hc : s.card ≠ 1) :
    subdivSimplex L b s = cone L (b s) (∑ a ∈ s, subdivSimplex L b (s.erase a)) := by
  rw [subdivSimplex, dite_eq_left hn, ite_eq_right hc]
  exact congrArg (cone L (b s)) (Finset.sum_attach s (fun a : V => subdivSimplex L b (s.erase a)))

def vertexCarrier (b : Finset V → W) (s : Finset V) : Set W :=
  {w | ∃ t : Finset V, t.Nonempty ∧ t ⊆ s ∧ b t = w}

omit [DecidableEq V] [DecidableEq W] in
lemma vertexCarrier_mono (b : Finset V → W) {s t : Finset V} (hst : s ⊆ t) :
    vertexCarrier b s ⊆ vertexCarrier b t := by
  rintro w ⟨u, hu, hus, hb⟩
  exact ⟨u, hu, hus.trans hst, hb⟩

omit [DecidableEq V] [DecidableEq W] in
lemma center_mem_carrier (b : Finset V → W) {s : Finset V} (hs : s.Nonempty) :
    b s ∈ vertexCarrier b s := ⟨s, hs, Finset.Subset.refl _, rfl⟩

lemma support_sum_chains (L : PreAbstractSimplicialComplex W) {α : Type*}
    (s : Finset α) (c : α → Chain L) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (∑ a ∈ s, c a).support) : ∃ a ∈ s, t ∈ (c a).support := by
  classical
  by_contra hn
  push Not at hn
  have hh : (∑ a ∈ s, c a) t = 0 := by
    rw [Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero (fun a ha => Finsupp.notMem_support_iff.mp (hn a ha))
  exact Finsupp.mem_support_iff.mp ht hh

lemma subdivSimplex_carrier (L : PreAbstractSimplicialComplex W) (b : Finset V → W)
    (s : Finset V) {t : {s : Finset W // s ∈ L}}
    (ht : t ∈ (subdivSimplex L b s).support) : ↑t.val ⊆ vertexCarrier b s := by
  induction s using Finset.strongInductionOn generalizing t with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hn
    · simp at ht
    by_cases hc : s.card = 1
    · rw [subdivSimplex_one L b hc, mem_support_simplex] at ht
      rw [ht]
      exact Finset.singleton_subset_set_iff.mpr (center_mem_carrier b hn)
    · rw [subdivSimplex_many L b hn hc] at ht
      obtain ⟨u, hu, _, htu⟩ := support_cone L (b s) _ ht
      obtain ⟨a, ha, hua⟩ := support_sum_chains L s _ hu
      have hu' := ih (s.erase a) (Finset.erase_ssubset ha) hua
      rw [htu, Finset.coe_insert]
      exact Set.insert_subset (center_mem_carrier b hn)
        (hu'.trans (vertexCarrier_mono b (Finset.erase_subset a s)))

end BorsukNine.SimplicialChains

end OAI
