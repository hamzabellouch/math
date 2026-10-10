import Mathlib
import OAI.Combinatorics.KMedian.Binary.NumericParserProgram
import OAI.Combinatorics.KMedian.Hardness.Model
import OAI.Combinatorics.KMedian.Hardness.Composition

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Complexity
open Binary.Automatic Binary.Automatic.Poly

def firstWord (s : Word) : Word :=
  let a := InputParser.natRead s
  a.2.take a.1

@[fun_prop] theorem firstWord_poly : Poly firstWord := by
  unfold firstWord
  exact Poly.comp InputParser.take_poly
    (pair (Poly.comp snd InputParser.natRead_poly) (Poly.comp fst InputParser.natRead_poly))

 theorem firstWord_encodePair (x : Word × Word) : firstWord (encodePair x) = x.1 := by
  simp only [firstWord, encodePair, List.append_assoc, InputParser.natRead_append]
  simp

noncomputable def firstWordProgram : Binary.PolyProgram id id firstWord :=
  (Binary.BooleanLists.packProgram.comp firstWord_poly.program).comp
    Binary.BooleanLists.unpackProgram

noncomputable def firstProjectionProgram : Binary.PolyProgram encodePair id Prod.fst :=
  firstWordProgram.recode encodePair (fun _ => rfl) firstWord_encodePair

 theorem firstProjection_finite : FinitePolyTime encodePair id Prod.fst :=
  ⟨firstProjectionProgram.stock, firstProjectionProgram.finite_work⟩

theorem P_subset_NP : P ⊆ NP := by
  intro L hL
  obtain ⟨d, hd, hc⟩ := hL
  refine ⟨d ∘ Prod.fst, 0, firstProjection_finite.comp hd, ?_⟩
  intro x
  constructor
  · intro hx
    exact ⟨[], by simp, (hc x).mpr hx⟩
  · rintro ⟨w, _, hw⟩
    exact (hc x).mp hw

theorem exists_NP_not_P (h : PNeNP) : ∃ L : Language, L ∈ NP ∧ L ∉ P := by
  by_contra hn
  apply h
  apply Set.Subset.antisymm P_subset_NP
  intro L hL
  by_contra hp
  exact hn ⟨L, hL, hp⟩

end MetricKMedian.Complexity

end Inline_PCPInherited

end OAI
