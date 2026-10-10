import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace OAI

namespace HadwigerMatching

/-- A finite set admits pairwise disjoint two-element subsets covering all but at most
one of its elements, without requiring the ambient type to be finite. -/
theorem exists_finite_pairing {V : Type*} (S : Finset V) :
    ∃ P : Finset (Finset V),
      (∀ A ∈ P, A.card = 2 ∧ A ⊆ S) ∧
      (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
      2 * P.card ≤ S.card ∧ S.card ≤ 2 * P.card + 1 := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hsmall : S.card ≤ 1
    · exact ⟨∅, by simp, by simp, by simp, by simpa using hsmall⟩
    have hpos : 0 < S.card := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
    have hca := Finset.card_erase_add_one ha
    have hpos' : 0 < (S.erase a).card := by omega
    obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos'
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    have hbS : b ∈ S := (Finset.mem_erase.mp hb).2
    let R := (S.erase a).erase b
    have hR : R ⊂ S :=
      Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset _ _) (Finset.erase_ssubset ha)
    obtain ⟨P, hP, hdisj, hlo, hhi⟩ := ih R hR
    have hcr : R.card + 2 = S.card := by
      have hcb := Finset.card_erase_add_one hb
      dsimp [R]
      omega
    have hRsub : R ⊆ S := fun x hx =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hx)
    have haR : a ∉ R := by simp [R]
    have hbR : b ∉ R := by simp [R]
    have hpair : ({a, b} : Finset V).card = 2 := by simp [Ne.symm hba]
    have hpairsub : ({a, b} : Finset V) ⊆ S := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ha
      · have hxb := Finset.mem_singleton.mp hx
        subst x
        exact hbS
    have hnew : ({a, b} : Finset V) ∉ P := by
      intro hp
      exact haR ((hP _ hp).2 (by simp))
    have hpairdisj : ∀ A ∈ P, Disjoint ({a, b} : Finset V) A := by
      intro A hA
      apply Finset.disjoint_left.mpr
      intro x hx hxA
      have hxR := (hP A hA).2 hxA
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact haR hxR
      · have hxb := Finset.mem_singleton.mp hx
        subst x
        exact hbR hxR
    refine ⟨insert {a, b} P, ?_, ?_, ?_, ?_⟩
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact ⟨hpair, hpairsub⟩
      · exact ⟨(hP A hA).1, fun x hx => hRsub ((hP A hA).2 hx)⟩
    · intro A hA B hB hne
      rcases Finset.mem_insert.mp hA with rfl | hA
      · rcases Finset.mem_insert.mp hB with rfl | hB
        · exact (hne rfl).elim
        · exact hpairdisj B hB
      · rcases Finset.mem_insert.mp hB with rfl | hB
        · exact (hpairdisj A hA).symm
        · exact hdisj A hA B hB hne
    · rw [Finset.card_insert_of_notMem hnew]
      omega
    · rw [Finset.card_insert_of_notMem hnew]
      omega

end HadwigerMatching

end OAI
