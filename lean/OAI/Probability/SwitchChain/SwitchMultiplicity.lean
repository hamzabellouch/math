import OAI.Probability.SwitchChain.SwitchPairFiber

namespace OAI

noncomputable section

namespace Problem315.SwitchPairFiber

attribute [local instance] Classical.propDecidable

def Crosses {n : ℕ} (p : SwitchProposal n) (A : Finset (Fin n)) : Prop :=
  ∀ u v, ((removedMatching p).Adj u v ∨ (addedMatching p).Adj u v) →
    (u ∈ A ↔ v ∉ A)

lemma complement_card {n : ℕ} (p : SwitchProposal n) {A : Finset (Fin n)}
    (hAS : A ⊆ p.1.val) (hA : A.card = 2) : (p.1.val \ A).card = 2 := by
  rw [Finset.card_sdiff_of_subset hAS, p.1.property, hA]

lemma crosses_complement {n : ℕ} (p : SwitchProposal n) {A : Finset (Fin n)}
    (hcross : Crosses p A) : Crosses p (p.1.val \ A) := by
  intro u v huv
  have hmem : u ∈ p.1.val ∧ v ∈ p.1.val := by
    rcases huv with h | h
    · exact matching_endpoints_mem p.2.val.1 h
    · exact matching_endpoints_mem p.2.val.2 h
  have h := hcross u v huv
  simp only [Finset.mem_sdiff, hmem.1, hmem.2, true_and]
  tauto

theorem cross_cuts_eq_of_inter_nonempty {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) {A B : Finset (Fin n)}
    (hA : A.card = 2) (hB : B.card = 2) (hAS : A ⊆ p.1.val) (hBS : B ⊆ p.1.val)
    (hcA : Crosses p A) (hcB : Crosses p B) (hi : (A ∩ B).Nonempty) : A = B := by
  classical
  obtain ⟨u, hu⟩ := hi
  obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
  have huS := hAS huA
  obtain ⟨v, huv, hvuniq⟩ := (p.2.val.1.property u).1 huS
  obtain ⟨w, huw, hwuniq⟩ := (p.2.val.2.property u).1 huS
  have hvS := (matching_endpoints_mem p.2.val.1 huv).2
  have hwS := (matching_endpoints_mem p.2.val.2 huw).2
  have hvw : v ≠ w := by
    intro h
    subst w
    exact validSwitch_matchings_disjoint hp huv huw
  have hvA : v ∉ A := (hcA u v (Or.inl huv)).mp huA
  have hwA : w ∉ A := (hcA u w (Or.inr huw)).mp huA
  have hvB : v ∉ B := (hcB u v (Or.inl huv)).mp huB
  have hwB : w ∉ B := (hcB u w (Or.inr huw)).mp huB
  have heqA : p.1.val \ A = {v, w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z
      · exact Finset.mem_sdiff.mpr ⟨hvS, hvA⟩
      · exact Finset.mem_sdiff.mpr ⟨hwS, hwA⟩
    · simp [complement_card p hAS hA, hvw]
  have heqB : p.1.val \ B = {v, w} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz <;> subst z
      · exact Finset.mem_sdiff.mpr ⟨hvS, hvB⟩
      · exact Finset.mem_sdiff.mpr ⟨hwS, hwB⟩
    · simp [complement_card p hBS hB, hvw]
  have heq : p.1.val \ A = p.1.val \ B := heqA.trans heqB.symm
  ext z
  have hz := Finset.ext_iff.mp heq z
  simp only [Finset.mem_sdiff] at hz
  constructor
  · intro hzA
    have hzS := hAS hzA
    tauto
  · intro hzB
    have hzS := hBS hzB
    tauto

theorem cross_cuts_eq_or_complement {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) {A B : Finset (Fin n)}
    (hA : A.card = 2) (hB : B.card = 2) (hAS : A ⊆ p.1.val) (hBS : B ⊆ p.1.val)
    (hcA : Crosses p A) (hcB : Crosses p B) :
    B = A ∨ B = p.1.val \ A := by
  classical
  by_cases hi : (A ∩ B).Nonempty
  · exact Or.inl (cross_cuts_eq_of_inter_nonempty p hp hA hB hAS hBS hcA hcB hi).symm
  · right
    apply Finset.eq_of_subset_of_card_le
    · intro z hzB
      apply Finset.mem_sdiff.mpr
      refine ⟨hBS hzB, ?_⟩
      intro hzA
      exact hi ⟨z, Finset.mem_inter.mpr ⟨hzA, hzB⟩⟩
    · rw [complement_card p hAS hA, hB]

def crossingPairs {n : ℕ} (p : SwitchProposal n) : Finset (Finset (Fin n)) :=
  (p.1.val.powersetCard 2).filter (Crosses p)

theorem crossingPairs_card {n : ℕ} {G : SimpleGraph (Fin n)}
    (p : SwitchProposal n) (hp : validSwitch G p) :
    (crossingPairs p).card = 2 := by
  classical
  obtain ⟨A, hA, hAS, hcA⟩ := exists_cross_cut p hp
  have hAc : (p.1.val \ A).card = 2 := complement_card p hAS hA
  have hcAc : Crosses p (p.1.val \ A) := crosses_complement p hcA
  have hne : A ≠ p.1.val \ A := by
    intro heq
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
    have hu' : u ∈ p.1.val \ A := heq ▸ hu
    exact (Finset.mem_sdiff.mp hu').2 hu
  have heq : crossingPairs p = {A, p.1.val \ A} := by
    ext B
    simp only [crossingPairs, Finset.mem_filter, Finset.mem_powersetCard,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hBS, hB⟩, hcB⟩
      exact cross_cuts_eq_or_complement p hp hA hB hAS hBS hcA hcB
    · intro h
      rcases h with h | h <;> subst B
      · exact ⟨⟨hAS, hA⟩, hcA⟩
      · exact ⟨⟨Finset.sdiff_subset, hAc⟩, hcAc⟩
  rw [heq]
  simp [hne]

end Problem315.SwitchPairFiber

end

end OAI
