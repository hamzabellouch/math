import OAI.NumberTheory.CubicMoment.Estimates.PrimeStoppingPairs

namespace OAI

/-! Exact finite reindexing from choices in the stopping bin to the
independent selected and complementary divisor subsets. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def stoppingDivisorSubsets (s : Finset Eisenstein) (bin : Eisenstein → ℕ)
    (j k : ℕ) : Finset (Finset Eisenstein) :=
  s.powerset.filter (fun d =>
    (∀ p ∈ d, bin p ≤ j) ∧ (primeBin d bin j).card = k ∧
      (∀ p ∈ s \ d, j ≤ bin p))

/-- This is the finite reindexing behind independent alpha/beta
collection; both subsets, and hence all coefficient weights, are exact. -/
theorem stopping_subset_sum (s : Finset Eisenstein) (bin : Eisenstein → ℕ)
    (j k : ℕ) (K : Finset Eisenstein → Finset Eisenstein → ℂ) :
    (∑ t ∈ (primeBin s bin j).powersetCard k,
      K (stoppingSelected s bin j t) (stoppingRemainder s bin j t)) =
    ∑ d ∈ stoppingDivisorSubsets s bin j k, K d (s \ d) := by
  apply Finset.sum_bij (fun t _ => stoppingSelected s bin j t)
  · intro t ht
    obtain ⟨hsub,hcard⟩ := Finset.mem_powersetCard.mp ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (stoppingSelected_subset hsub),
      fun p hp => stoppingSelected_bins_le hsub hp,?_,?_⟩
    · change ((stoppingSelected s bin j t).filter (fun p => bin p = j)).card = k
      rw [stoppingSelected_bin_count hsub,hcard]
    · intro p hp
      exact stoppingRemainder_bins_ge hp
  · intro t ht t' ht' heq
    have hsub := (Finset.mem_powersetCard.mp ht).1
    have hsub' := (Finset.mem_powersetCard.mp ht').1
    have hf := congrArg (fun d : Finset Eisenstein => d.filter (fun p => bin p = j)) heq
    rwa [stoppingSelected_bin_count hsub,stoppingSelected_bin_count hsub'] at hf
  · intro d hd
    obtain ⟨hdsub,hdlo,hdcard,hehi⟩ := Finset.mem_filter.mp hd
    have hdsub' := Finset.mem_powerset.mp hdsub
    let t := primeBin d bin j
    have ht : t ∈ (primeBin s bin j).powersetCard k := by
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_,hdcard⟩
      intro p hp
      obtain ⟨hpd,hpj⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hdsub' hpd,hpj⟩
    have hsel := stoppingSelected_of_separated_bins d (s \ d) bin j hdlo hehi
    rw [Finset.union_sdiff_of_subset hdsub'] at hsel
    exact ⟨t,ht,hsel⟩
  · intro t _ht
    rfl

end CubicFirstMoment

end

end OAI
