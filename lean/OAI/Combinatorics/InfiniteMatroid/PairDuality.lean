import OAI.Combinatorics.InfiniteMatroid.CorollaryModel

namespace OAI

namespace InfiniteMatroidCounterexample
open Set Matroid

lemma pair_covering_iff_dual_packing {α : Type*} {M : Bool → Matroid α} {F : Set α}
    (hE : ∀ i, (M i).E = F) :
    FamilyCovering F M ↔ FamilyPacking (fun i ↦ (M i).dual) := by
  constructor
  · rintro ⟨I, hI, hcov⟩
    refine ⟨fun i ↦ F \ I i, ?_, ?_⟩
    · intro i j hij
      apply disjoint_left.mpr
      rintro x ⟨hxF, hxi⟩ ⟨_, hxj⟩
      have hx : x ∈ ⋃ k, I k := hcov.symm ▸ hxF
      obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
      have hk : k = i ∨ k = j := by cases i <;> cases j <;> cases k <;> simp_all
      rcases hk with rfl | rfl
      · exact hxi hxk
      · exact hxj hxk
    · intro i
      have hc : (M i).dual.Coindep (I i) := by
        rw [Matroid.dual_coindep_iff]
        exact hI i
      simpa only [Matroid.dual_ground, hE] using hc.compl_spanning
  · rintro ⟨S, hdisj, hS⟩
    refine ⟨fun i ↦ F \ S i, ?_, ?_⟩
    · intro i
      have hc := (hS i).compl_coindep
      simpa only [Matroid.dual_ground, hE, Matroid.dual_coindep_iff] using hc
    · ext x
      simp only [mem_iUnion, mem_sdiff]
      constructor
      · rintro ⟨i, hx, _⟩
        exact hx
      · intro hx
        by_cases hs : x ∈ S false
        · exact ⟨true, hx, fun h ↦ disjoint_left.mp (hdisj Bool.false_ne_true) hs h⟩
        · exact ⟨false, hx, hs⟩

lemma separate_packing_of_covering_counterexample {α : Type*}
    {M : Bool → Matroid α} {F : Set α} (hE : ∀ i, (M i).E = F)
    (hno : ¬ FamilyCovering F M)
    (hcond : ∀ Y ⊆ F, FamilyPacking (fun i ↦ M i ↾ Y) →
      FamilyCovering Y (fun i ↦ M i ↾ Y)) :
    ¬ PackingConjectureFor F (fun i ↦ (M i).dual) := by
  intro hconj
  apply hno
  apply (pair_covering_iff_dual_packing hE).mpr
  apply hconj.mpr
  intro Y hY hcov
  have hground : ∀ i, (M i ↾ Y).E = Y := fun _ ↦ rfl
  have hdualground : ∀ i, (M i ↾ Y).dual.E = Y := fun _ ↦ rfl
  have hcov' : FamilyCovering Y (fun i ↦ (M i ↾ Y).dual) := by
    simpa only [contractOnto, Matroid.dual_dual] using hcov
  have hp : FamilyPacking (fun i ↦ M i ↾ Y) := by
    simpa only [Matroid.dual_dual] using
      (pair_covering_iff_dual_packing hdualground).mp hcov'
  have hdc := (pair_covering_iff_dual_packing hground).mp (hcond Y hY hp)
  simpa only [contractOnto, Matroid.dual_dual] using hdc

end InfiniteMatroidCounterexample

end OAI
