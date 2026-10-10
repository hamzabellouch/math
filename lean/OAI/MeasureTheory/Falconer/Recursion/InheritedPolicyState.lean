import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors

namespace OAI

namespace PlanarFalconer

noncomputable def remainingPolicyDescriptors (A : ℕ → ℝ) (N q a₀ t₀ a : ℕ) : Finset PolicyDescriptor :=
  (policyDescriptorList A N q a₀ t₀).filter fun b => a < descriptorAnchor b

 theorem policyDescriptor_anchor_gt_left (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) : a < descriptorAnchor d := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,ha,_,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)
  rw [originDescriptor_anchor A hd]
  omega

 theorem minimal_policy_list_survives (A : ℕ → ℝ) {N q a₀ t₀ a b v : ℕ}
    (hq : 0 < q) (hleft : a₀ ≤ b) (hright : v ≤ t₀) (hdepth : a ≤ b) :
    policyDescriptorList A N q b v ⊆ remainingPolicyDescriptors A N q a₀ t₀ a := by
  intro d hd
  exact Finset.mem_filter.mpr ⟨policyDescriptorList_mono A hleft hright hd,
    hdepth.trans_lt (policyDescriptor_anchor_gt_left A hq hd)⟩

 theorem remainingPolicyDescriptors_mono (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    remainingPolicyDescriptors A N q a₀ t₀ p ⊆ remainingPolicyDescriptors A N q a₀ t₀ a := by
  intro d hd
  obtain ⟨hd,hp⟩ := Finset.mem_filter.mp hd
  exact Finset.mem_filter.mpr ⟨hd,hap.trans_lt hp⟩

 theorem remainingPolicyDescriptors_drop (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ} (hap : a ≤ p) :
    (remainingPolicyDescriptors A N q a₀ t₀ a).filter (fun d => p < descriptorAnchor d) =
      remainingPolicyDescriptors A N q a₀ t₀ p := by
  ext d
  simp only [remainingPolicyDescriptors,Finset.mem_filter]
  constructor
  · exact fun h => ⟨h.1.1,h.2⟩
  · exact fun h => ⟨⟨h.1,hap.trans_lt h.2⟩,h.2⟩

 theorem remainingPolicyDescriptors_card (A : ℕ → ℝ) {N q a₀ t₀ a : ℕ} (hq : 0 < q) :
    (remainingPolicyDescriptors A N q a₀ t₀ a).card ≤ (N+1)^3 :=
  (Finset.card_filter_le _ _).trans (policyDescriptorList_card A hq)

 theorem reached_anchor_strictly_reduces_list (A : ℕ → ℝ) (N q a₀ t₀ : ℕ) {a p : ℕ}
    (hap : a ≤ p) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a) (hp : descriptorAnchor d ≤ p) :
    (remainingPolicyDescriptors A N q a₀ t₀ p).card <
      (remainingPolicyDescriptors A N q a₀ t₀ a).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨remainingPolicyDescriptors_mono A N q a₀ t₀ hap,?_⟩
  intro he
  rw [← he] at hd
  have hh := (Finset.mem_filter.mp hd).2
  omega

end PlanarFalconer

end OAI
