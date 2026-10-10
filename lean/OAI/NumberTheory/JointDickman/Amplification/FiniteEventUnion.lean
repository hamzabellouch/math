import OAI.NumberTheory.JointDickman.Counting.SamplingMoments

namespace OAI

/-! # A union over a finite list of events -/

namespace JointDickman
open Finset PublishedInputs

open Classical in
theorem finiteProbability_exists_mem {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (I : Finset ι) (E : ι → Ω → Prop) :
    finiteProbability w (fun x => ∃ i ∈ I, E i x) ≤ ∑ i ∈ I, finiteProbability w (E i) := by
  have he : (fun x => ∃ i ∈ I, E i x) = (fun x => ∃ i : I, E i.val x) := by
    funext x
    apply propext
    constructor
    · rintro ⟨i,hi,hE⟩
      exact ⟨⟨i,hi⟩,hE⟩
    · rintro ⟨i,hE⟩
      exact ⟨i.val,i.property,hE⟩
  rw [he]
  exact (finiteProbability_union_le w hw (fun i : I => E i.val)).trans_eq
    (sum_coe_sort I (fun i => finiteProbability w (E i)))

end JointDickman

end OAI
