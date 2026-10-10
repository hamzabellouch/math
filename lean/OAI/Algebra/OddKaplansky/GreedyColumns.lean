import OAI.Algebra.OddKaplansky.SourceSector

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3

section
namespace OddKaplansky.GreedyColumns
noncomputable section
open scoped Classical BigOperators
open Submodule
variable {K : Type portUniverse1} {S : Type portUniverse2} {V : Type portUniverse3} [Field K] [Fintype S] [LinearOrder S]
variable [AddCommGroup V] [Module K V]
variable (v : S → V)

def Selected : Set S := {i | v i ∉ span K (v '' Set.Iio i)}
abbrev Index := {i // Selected (K := K) v i}
instance : Fintype (Index (K := K) v) :=
  @Fintype.ofFinite _ (@Subtype.finite S (Finite.of_fintype S) (Selected (K := K) v))
lemma independent : LinearIndependent K (fun i : Index (K := K) v => v i.val) := by
  classical
  have aux (s : Finset S) : (↑s : Set S) ⊆ Selected (K := K) v → LinearIndepOn K v (↑s : Set S) := by
    induction s using Finset.induction_on_max with
    | empty => intro _; simpa only [Finset.coe_empty] using linearIndepOn_empty K v
    | insert a s hlt ih =>
      intro hs
      rw [Finset.coe_insert]
      apply (ih (fun x hx => hs (by simp [hx]))).insert
      intro ha
      apply hs (show a ∈ (↑(insert a s) : Set S) by simp)
      exact span_mono (Set.image_mono (fun x hx => hlt x hx)) ha
  have h := aux (Finset.univ.filter (fun i => i ∈ Selected (K := K) v)) (by simp)
  change LinearIndepOn K v (Selected (K := K) v)
  convert h using 1
  ext i
  simp
lemma span_selected : span K (Set.range (fun i : Index (K := K) v => v i.val)) = span K (Set.range v) := by
  classical
  apply le_antisymm
  · apply span_mono
    rintro x ⟨i,rfl⟩
    exact ⟨i.val,rfl⟩
  · apply span_le.mpr
    rintro x ⟨i,rfl⟩
    refine @WellFounded.induction S (· < ·) wellFounded_lt (fun i => v i ∈ span K (Set.range (fun i : Index (K := K) v => v i.val))) i ?_
    intro i ih
    by_cases hi : Selected (K := K) v i
    · exact subset_span ⟨⟨i,hi⟩,rfl⟩
    · have hm : v i ∈ span K (v '' Set.Iio i) := by
        change ¬ (v i ∉ span K (v '' Set.Iio i)) at hi
        exact not_not.mp hi
      apply (span_le.mpr ?_ : span K (v '' Set.Iio i) ≤ span K (Set.range (fun i : Index (K := K) v => v i.val))) hm
      rintro x ⟨j,hj,rfl⟩
      exact ih j (by exact hj)
end
end OddKaplansky.GreedyColumns

end

end OAI
