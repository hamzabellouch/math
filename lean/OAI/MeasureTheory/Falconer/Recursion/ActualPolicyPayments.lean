import OAI.MeasureTheory.Falconer.Recursion.PrefixPolicyGeometry

namespace OAI

namespace PlanarFalconer

theorem actual_prefix_policy_payment (A : ℕ → ℝ) {N q a t v : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hpref : 2*policyDepth A N q a t ≤ a+t) (hvt : v ≤ t) (hhigh : t-v ≤ q) :
    let p := policyDepth A N q a t
    p+10*q ≤ v ∧
      potential A a t (10*q)+height A a p ≤ potential A p v (10*q) := by
  have hg := prefix_policy_geometry A hq htN hw hpref
  obtain ⟨l,r,hl,hr,hlp,hpr,hinner⟩ := policy_interior_interval A hq htN hw
  have hwidth : policyDepth A N q a t+10*q ≤ v := by omega
  exact ⟨hwidth,policy_prefix_payment A hq hwidth hg.1.le hvt hlp hr hinner⟩

theorem actual_suffix_policy_payment (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) (htN : t ≤ N) (hw : a+100*q < t)
    (hsuffix : a+t < 2*policyDepth A N q a t) :
    let p := policyDepth A N q a t
    a+10*q ≤ p ∧
      potential A a t (10*q)+(A p-intervalMin A p t) ≤ potential A a p (10*q) := by
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq htN hw)
  obtain ⟨l,r,hl,hr,hlp,hpr,hinner⟩ := policy_interior_interval A hq htN hw
  have hwidth : a+10*q ≤ policyDepth A N q a t := by omega
  exact ⟨hwidth,policy_suffix_payment A hq hwidth (by omega) hl hpr hinner⟩

theorem actual_direct_policy_payment (A : ℕ → ℝ) {N q a v a₀ t₀ : ℕ}
    (hq : 0 < q) (hw : a+100*q < v) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a₀ t₀)
    (hap : a < descriptorAnchor d)
    (hdirect : v ≤ a+2*descriptorLength d)
    (hscale : 2*descriptorAnchor d ≤ a+v+2*q) :
    descriptorAnchor d+10*q ≤ v ∧
      potential A a v (10*q)+height A a (descriptorAnchor d) ≤
        potential A (descriptorAnchor d) v (10*q) := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,_,_,hzwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hp := originDescriptor_anchor A hd
  have hlength := originDescriptor_length A hq huN hzwide hd
  have hlengthp := originDescriptor_length_le_anchor A hd
  obtain ⟨l,r,hl,hr,hlp,hpr,hinner⟩ := policy_interior_interval A hq huN hzwide
  rw [← hp] at hlp hpr hinner
  have hwidth : descriptorAnchor d+10*q ≤ v := by omega
  refine ⟨hwidth,policy_direct_payment A hq hwidth hap.le hlp hpr hl hr ?_ hdirect hinner⟩
  omega

end PlanarFalconer

end OAI
