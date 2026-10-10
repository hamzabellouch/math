import OAI.NumberTheory.Jacobsthal.Paths.PrefixCompletions

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.ReferencePruning
attribute [local instance] Classical.propDecidable
open FinitePathGeometry ReferenceAdmission ErdosPrimeInputs.PrimePrefixMass

noncomputable def rejectedPrefixes (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : Finset (List ℕ) :=
  (decreasingPrefixes P).filter (fun ps => ¬admitted w i r ps)

theorem rejected_eq_omission_completions (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    rejectedPrefixes w P i r = (firstOmissions w P i r).biUnion (completions P) := by
  ext ps
  constructor
  · intro hp
    obtain ⟨hD,hnot⟩ := Finset.mem_filter.mp hp
    obtain ⟨pre,suf,he,hfirst⟩ := exists_first_omitted_prefix hnot
    have hjoin : pre++suf ∈ decreasingPrefixes P := by rwa [← he]
    have hpre := decreasing_prefix_mem hjoin
    have hsuf := (append_mem_decreasing_iff hpre).mp hjoin
    apply Finset.mem_biUnion.mpr
    exact ⟨pre,Finset.mem_filter.mpr ⟨hpre,hfirst⟩,
      Finset.mem_image.mpr ⟨suf,hsuf,he.symm⟩⟩
  · intro hp
    obtain ⟨pre,hpre,hcomplete⟩ := Finset.mem_biUnion.mp hp
    obtain ⟨suf,hsuf,rfl⟩ := Finset.mem_image.mp hcomplete
    obtain ⟨hD,hfirst⟩ := Finset.mem_filter.mp hpre
    apply Finset.mem_filter.mpr
    refine ⟨(append_mem_decreasing_iff hD).mpr hsuf,?_⟩
    intro hallowed
    exact firstOmitted_not_admitted hfirst ((admitted_append w r i pre suf).mp hallowed).1

theorem omission_completions_disjoint (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    (firstOmissions w P i r : Set (List ℕ)).PairwiseDisjoint (completions P) := by
  intro pre hpre other hother hne
  apply Finset.disjoint_left.mpr
  intro whole hp hq
  obtain ⟨suf,_,he⟩ := Finset.mem_image.mp hp
  obtain ⟨tail,_,hf⟩ := Finset.mem_image.mp hq
  have h := first_omission_prefix_unique (Finset.mem_filter.mp hpre).2
    (Finset.mem_filter.mp hother).2 (show pre <+: whole from ⟨suf,he⟩)
    (show other <+: whole from ⟨tail,hf⟩)
  exact hne h

end NumberTheoryLean.ReferencePruning

end

end Erdos970

end OAI
