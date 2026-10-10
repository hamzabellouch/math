import OAI.Analysis.CircleDomains.Modulus.PriorityWeights

namespace OAI

/-! A cutoff equal to one terminates the priority interpolation. Its
continuity near a nonpoint end therefore does not require a trace of
the original horizontal coordinate at that end. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem priorityRemainder_zero_of_one {χ : ℕ → ℝ} {j n : ℕ} (hj : χ j = 1) (hjn : j < n) :
    priorityRemainder χ n = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hjn)
  simp only [hj, sub_self]

 theorem priorityWeight_zero_after_one {χ : ℕ → ℝ} {j n : ℕ} (hj : χ j = 1) (hjn : j < n) :
    priorityWeight χ n = 0 := by
  rw [priorityWeight, priorityRemainder_zero_of_one hj hjn, mul_zero]

 theorem priorityInfiniteValue_eq_prefix {χ c : ℕ → ℝ} {j : ℕ} (hj : χ j = 1) (x : ℝ) :
    priorityInfiniteValue χ c x = ∑ n ∈ Finset.range (j+1), priorityWeight χ n*c n := by
  have hw : (∑' n, priorityWeight χ n) = 1 := by
    have hsum : (∑' n, priorityWeight χ n) = ∑ n ∈ Finset.range (j+1), priorityWeight χ n := by
      apply tsum_eq_sum
      intro n hn
      have hn' : j+1 ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
      exact priorityWeight_zero_after_one hj (by omega)
    rw [hsum, priorityWeight_sum, priorityRemainder_zero_of_one hj (Nat.lt_succ_self j), sub_zero]
  rw [priorityInfiniteValue, hw, sub_self, zero_mul, zero_add]
  apply tsum_eq_sum
  intro n hn
  rw [priorityWeight_zero_after_one hj (by
    have hn' : j+1 ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)
    omega), zero_mul]

 theorem priorityWeight_continuousAt {X : Type*} [TopologicalSpace X]
    {χ : ℕ → X → ℝ} {p : X} (hχ : ∀ n, ContinuousAt (χ n) p) (n : ℕ) :
    ContinuousAt (fun q => priorityWeight (fun i => χ i q) n) p := by
  apply (hχ n).mul
  exact tendsto_finsetProd _ (fun i _ => continuousAt_const.sub (hχ i))

 theorem priorityInfiniteValue_continuousAt_of_one {X : Type*} [TopologicalSpace X]
    {χ : ℕ → X → ℝ} {p : X} (hχ : ∀ n, ContinuousAt (χ n) p)
    (c : ℕ → ℝ) (x : X → ℝ) {j : ℕ} (hj : ∀ᶠ q in 𝓝 p, χ j q = 1) :
    ContinuousAt (fun q => priorityInfiniteValue (fun i => χ i q) c (x q)) p := by
  have hfinite : ContinuousAt (fun q =>
      ∑ n ∈ Finset.range (j+1), priorityWeight (fun i => χ i q) n*c n) p :=
    tendsto_finsetSum _ (fun n _ => (priorityWeight_continuousAt hχ n).mul continuousAt_const)
  apply hfinite.congr_of_eventuallyEq
  filter_upwards [hj] with q hq
  exact priorityInfiniteValue_eq_prefix (χ := fun i => χ i q) (c := c) hq (x q)

end CircleDomainRigidity

end

end OAI
