import OAI.MeasureTheory.Falconer.Recursion.DirectPolicyWitness

namespace OAI

namespace PlanarFalconer

theorem remaining_maximum_preserved (A : ℕ → ℝ) {N q a₀ t₀ a p : ℕ}
    (hap : a ≤ p) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a)
    (hm : descriptorLength d = (remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength)
    (hanchor : p < descriptorAnchor d) :
    (remainingPolicyDescriptors A N q a₀ t₀ p).sup descriptorLength =
      (remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength := by
  apply le_antisymm
  · exact Finset.sup_mono (remainingPolicyDescriptors_mono A N q a₀ t₀ hap)
  · rw [← hm]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hd).1,hanchor⟩)

theorem actual_near_progress (A : ℕ → ℝ) {N q a₀ t₀ a v : ℕ} {sig : ℝ}
    (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    (hnear : a < v-2*sourceFarBuffer N
      ((remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength) sig) :
    let S := remainingPolicyDescriptors A N q a₀ t₀ a
    let L := S.sup descriptorLength
    let b := v-2*sourceFarBuffer N L sig
    v ≤ b+100*q ∨
      (∃ d ∈ S, descriptorLength d = L ∧ a < descriptorAnchor d ∧ descriptorAnchor d ≤ b ∧
        descriptorAnchor d ∈ policyRepresentatives A N q ∧
        (remainingPolicyDescriptors A N q a₀ t₀ b).card < S.card) ∨
      ((remainingPolicyDescriptors A N q a₀ t₀ b).sup descriptorLength = L ∧
        v-2*sourceFarBuffer N
          ((remainingPolicyDescriptors A N q a₀ t₀ b).sup descriptorLength) sig = b) := by
  classical
  dsimp only
  let S := remainingPolicyDescriptors A N q a₀ t₀ a
  let L := S.sup descriptorLength
  let b := v-2*sourceFarBuffer N L sig
  by_cases hterm : v ≤ b+100*q
  · exact Or.inl hterm
  apply Or.inr
  have hb := direct_buffer_eq_length hceil (by omega : b+100*q < v) (le_refl b)
  have hLpos : 0 < L := hb.2.2
  have hS : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : L = 0 := by simp [L,he]
    omega
  by_cases hpassed : ∃ d ∈ S, descriptorLength d = L ∧ descriptorAnchor d ≤ b
  · obtain ⟨d,hd,hm,hdb⟩ := hpassed
    have hap := (Finset.mem_filter.mp hd).2
    exact Or.inl ⟨d,hd,hm,hap,hdb,
      policyDescriptor_anchor_mem A hq (Finset.mem_filter.mp hd).1,
      reached_anchor_strictly_reduces_list A N q a₀ t₀ hnear.le hd hdb⟩
  · obtain ⟨d,hd,hm⟩ := Finset.exists_mem_eq_sup S hS descriptorLength
    have hdb : b < descriptorAnchor d := by
      by_contra h
      exact hpassed ⟨d,hd,hm.symm,by omega⟩
    have he := remaining_maximum_preserved A hnear.le hd hm.symm hdb
    exact Or.inr ⟨he,by rw [he]⟩

end PlanarFalconer

end OAI
