import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Enum

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SharedSlotPatterns
open Finset Classical
variable {α β : Type*} [DecidableEq α] [DecidableEq β] {J : ℕ}

noncomputable def rowFactors (c : Fin J → Option α) : Finset α :=
  univ.biUnion (fun j => (c j).toFinset)

lemma mem_rowFactors (c : Fin J → Option α) (a : α) :
    a ∈ rowFactors c ↔ ∃ j, c j=some a := by
  simp [rowFactors,Option.mem_toFinset,Option.mem_def]

lemma rowFactors_relabel (c : Fin J → Option α) (e : α ↪ β) :
    rowFactors (fun j => (c j).map e)=(rowFactors c).image e := by
  ext b
  simp only [mem_rowFactors,mem_image]
  constructor
  · rintro ⟨j,hj⟩
    cases he : c j with
    | none => simp [he] at hj
    | some a =>
      simp only [he,Option.map_some,Option.some.injEq] at hj
      exact ⟨a,⟨j,he⟩,hj⟩
  · rintro ⟨a,⟨j,hj⟩,rfl⟩
    exact ⟨j,by simp [hj]⟩

lemma rowFactors_code (s : Finset α) (hs : s.card ≤ J) :
    rowFactors (FiniteSlotEncoding.code s J)=s := by
  ext a
  exact (mem_rowFactors _ a).trans (FiniteSlotEncoding.mem_iff_code s J hs a).symm
end OrdinaryCorrelations.SharedSlotPatterns

end

end OAI
