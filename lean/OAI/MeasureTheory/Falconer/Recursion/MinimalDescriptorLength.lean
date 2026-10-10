import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_length_le_anchor (A : ℕ → ℝ) {N q b u : ℕ}
    {d : PolicyDescriptor} (hd : d ∈ originDescriptors A N q b u) :
    descriptorLength d ≤ descriptorAnchor d := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.sub_le _ _
  · split_ifs at hd with h
    · obtain rfl := Finset.mem_singleton.mp hd
      dsimp [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem policyDescriptor_twice_length (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    a + 2*descriptorLength d ≤ t := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,ha,ht,hw⟩ := Finset.mem_filter.mp hz
  have hu := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hl := originDescriptor_length A hq hu hw hd
  have hp := originDescriptor_length_le_anchor A hd
  omega

theorem policyDescriptor_length_le_half (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    descriptorLength d ≤ (t-a)/2 := by
  have := policyDescriptor_twice_length A hq hd
  omega

theorem policyDescriptor_real_length (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    2*(descriptorLength d:ℝ) ≤ (t:ℝ)-(a:ℝ) := by
  have h : (a:ℝ)+2*(descriptorLength d:ℝ) ≤ (t:ℝ) := by
    exact_mod_cast policyDescriptor_twice_length A hq hd
  linarith

end PlanarFalconer

end OAI
