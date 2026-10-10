import OAI.MeasureTheory.Falconer.Estimates.ActualDirectBuffer
import OAI.MeasureTheory.Falconer.Recursion.ActualPolicyPayments
import OAI.MeasureTheory.Falconer.Recursion.InheritedPolicyState

namespace OAI

namespace PlanarFalconer

theorem remaining_descriptor_companion (A : ℕ → ℝ) {N q a₀ t₀ a : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a) :
    PolicyDescriptor.parallel (max a (descriptorAnchor d-descriptorLength d))
      (descriptorAnchor d) ∈ remainingPolicyDescriptors A N q a₀ t₀ a := by
  classical
  obtain ⟨hd,hap⟩ := Finset.mem_filter.mp hd
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  have hz' := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz'.1).2)
  have hp := originDescriptor_anchor A hd
  have hl := originDescriptor_length A hq huN hz'.2.2.2 hd
  have hLp := originDescriptor_length_le_anchor A hd
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_biUnion.mpr ⟨z,hz,?_⟩,hap⟩
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  refine ⟨max a (descriptorAnchor d-descriptorLength d),Finset.mem_Ico.mpr ⟨?_,?_⟩,?_⟩
  · rw [← hp]
    omega
  · omega
  · rw [hp]

structure DirectPolicyWitness (A : ℕ → ℝ) (N q a₀ t₀ a v : ℕ) (sig : ℝ)
    (d : PolicyDescriptor) : Prop where
  mem : d ∈ remainingPolicyDescriptors A N q a₀ t₀ a
  maximal : descriptorLength d = (remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength
  buffer : sourceFarBuffer N (descriptorLength d) sig = descriptorLength d
  direct_depth : v ≤ a+2*descriptorLength d
  anchor_gt : a < descriptorAnchor d
  anchor_lt : descriptorAnchor d < v
  width : descriptorAnchor d+10*q ≤ v
  companion : PolicyDescriptor.parallel (max a (descriptorAnchor d-descriptorLength d))
    (descriptorAnchor d) ∈ remainingPolicyDescriptors A N q a₀ t₀ a
  g_lt : max a (descriptorAnchor d-descriptorLength d) < descriptorAnchor d
  g_slack : ((max a (descriptorAnchor d-descriptorLength d):ℕ):ℝ)-a ≤ sig*N
  frequency_slack : 10*sig*N ≤ (v:ℝ)-descriptorAnchor d
  depth_scale : ((descriptorAnchor d-a:ℕ):ℝ) ≤ (v:ℝ)-descriptorAnchor d+2*sig*N
  length_scale : (descriptorLength d:ℝ) ≤ (v:ℝ)-descriptorAnchor d+2*sig*N
  midpoint : 2*descriptorAnchor d ≤ a+v+2*q
  shrinks : (remainingPolicyDescriptors A N q a₀ t₀ (descriptorAnchor d)).card <
    (remainingPolicyDescriptors A N q a₀ t₀ a).card
  payment : potential A a v (10*q)+height A a (descriptorAnchor d) ≤
    potential A (descriptorAnchor d) v (10*q)

theorem actual_direct_policy_witness (A : ℕ → ℝ) {N q a₀ t₀ a v : ℕ} {sig : ℝ}
    (hsig : 0 ≤ sig) (hq : 0 < q) (hceil : ⌈10*sig*(N:ℝ)⌉₊ < q)
    (hslack : sig*(N:ℝ) ≤ (q:ℝ)) (hslack10 : 10*sig*(N:ℝ) ≤ (q:ℝ))
    (ht : (t₀:ℝ) ≤ (v:ℝ)+sig*N) (hw : a+100*q < v)
    (hdirect : v-2*sourceFarBuffer N
      ((remainingPolicyDescriptors A N q a₀ t₀ a).sup descriptorLength) sig ≤ a) :
    ∃ d : PolicyDescriptor, DirectPolicyWitness A N q a₀ t₀ a v sig d := by
  classical
  let S := remainingPolicyDescriptors A N q a₀ t₀ a
  have hb := direct_buffer_eq_length hceil hw hdirect
  have hS : S.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hz : S.sup descriptorLength = 0 := by rw [he]; rfl
    exact (Nat.ne_of_gt hb.2.2) hz
  obtain ⟨d,hd,hmax⟩ := Finset.exists_mem_eq_sup S hS descriptorLength
  dsimp only [S] at hmax
  have hmax' := hmax.symm
  have hdir : v ≤ a+2*descriptorLength d := by simpa only [hmax] using hb.2.1
  have hmem := Finset.mem_filter.mp hd
  have hap : a < descriptorAnchor d := hmem.2
  obtain ⟨z,hz,hzd⟩ := Finset.mem_biUnion.mp hmem.1
  have hz' := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz'.1).2)
  have hl := originDescriptor_length A hq huN hz'.2.2.2 hzd
  have hLp := originDescriptor_length_le_anchor A hzd
  have hpt : descriptorAnchor d+descriptorLength d ≤ t₀ := hl.2.2.trans hz'.2.2.1
  have hptR : (descriptorAnchor d:ℝ)+(descriptorLength d:ℝ) ≤ (t₀:ℝ) := by exact_mod_cast hpt
  have hsigN : 0 ≤ sig*(N:ℝ) := mul_nonneg hsig (Nat.cast_nonneg _)
  have hdirR : (v:ℝ) ≤ (a:ℝ)+2*(descriptorLength d:ℝ) := by exact_mod_cast hdir
  have hmidR : 2*(descriptorAnchor d:ℝ) ≤ (a:ℝ)+v+2*q := by linarith
  have hmid : 2*descriptorAnchor d ≤ a+v+2*q := by exact_mod_cast hmidR
  have hwidth : descriptorAnchor d+10*q ≤ v := by omega
  have hwidthR : (descriptorAnchor d:ℝ)+10*(q:ℝ) ≤ (v:ℝ) := by exact_mod_cast hwidth
  have hn : ((descriptorAnchor d-a:ℕ):ℝ) = (descriptorAnchor d:ℝ)-a := Nat.cast_sub hap.le
  have hgs : ((descriptorAnchor d-descriptorLength d:ℕ):ℝ) =
      (descriptorAnchor d:ℝ)-descriptorLength d := Nat.cast_sub hLp
  refine ⟨d, {
    mem := hd
    maximal := hmax'
    buffer := ?_
    direct_depth := hdir
    anchor_gt := hap
    anchor_lt := by omega
    width := hwidth
    companion := remaining_descriptor_companion A hq hd
    g_lt := by omega
    g_slack := ?_
    frequency_slack := by linarith
    depth_scale := ?_
    length_scale := ?_
    midpoint := hmid
    shrinks := reached_anchor_strictly_reduces_list A N q a₀ t₀ hap.le hd le_rfl
    payment := (actual_direct_policy_payment A hq hw hmem.1 hap hdir hmid).2 }⟩
  · simpa only [← hmax] using hb.1
  · rw [Nat.cast_max,hgs,sub_le_iff_le_add]
    apply max_le <;> linarith [show 0 ≤ sig*(N:ℝ) by positivity]
  · rw [hn]
    linarith
  · have haR : (a:ℝ) < (descriptorAnchor d:ℝ) := Nat.cast_lt.mpr hap
    linarith

end PlanarFalconer

end OAI
