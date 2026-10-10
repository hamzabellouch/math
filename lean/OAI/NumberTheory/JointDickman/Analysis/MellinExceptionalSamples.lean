import OAI.NumberTheory.JointDickman.Analysis.MultiscaleMellinEnergy
import OAI.NumberTheory.TwoPointCorrelations.MRTLargeValues

namespace OAI

/-! # Sparse samples in the exceptional frequency class

Every exceptional frequency has a large prime polynomial in each selected
band. The exact high-moment bound therefore controls any separated sample
of this class. The statement retains the chosen moment order and cutoff.
-/
namespace JointDickman
open Finset MeasureTheory TwoPointCorrelations
open scoped Classical

namespace MellinPrimeBands

noncomputable def sampleCost (D : MellinPrimeBands) (j k M r : ℕ)
    (T : ℝ) : ℝ :=
  (8 * Real.exp 1 * (T + 1 + (M^r : ℕ)) *
    (2 + (Real.log (M^r : ℕ))^2) * (r.factorial : ℝ) *
    (∑ p ∈ (D.primes j).filter (fun p => D.bin j p = k), 1/(p : ℝ)^2)^r) /
      (D.threshold j k)^(2*r)

lemma bin_sample_bound (D : MellinPrimeBands) (f : ℕ → ℂ)
    (hf : OneBounded f) (j k M r : ℕ)
    (hprime : ∀ p ∈ D.primes j, p.Prime)
    (hM : ∀ p ∈ D.primes j, D.bin j p = k → p ≤ M)
    (hV : 0 < D.threshold j k)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    (hlarge : ∀ t ∈ S, D.threshold j k ≤ ‖D.polynomial f j k t‖) :
    (S.card : ℝ) ≤ D.sampleCost j k M r T := by
  have hp : ∀ p ∈ (D.primes j).filter (fun p => D.bin j p = k), p.Prime :=
    fun p hp => hprime p (mem_filter.mp hp).1
  have hm : ∀ p ∈ (D.primes j).filter (fun p => D.bin j p = k), p ≤ M :=
    fun p hp => hM p (mem_filter.mp hp).1 (mem_filter.mp hp).2
  have hb := mrt_prime_large_values _ (fun p => f p/(p : ℂ)) M r hp hm
    S hT hV hS hsep hlarge
  apply hb.trans
  unfold sampleCost
  apply div_le_div_of_nonneg_right _ (pow_nonneg hV.le _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply pow_le_pow_left₀ (by positivity)
  apply sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p (mem_filter.mp hp).1).pos
  rw [norm_div, Complex.norm_natCast, div_pow, one_div]
  have hb := hf p (hprime p (mem_filter.mp hp).1).pos
  have hs : ‖f p‖^2 ≤ 1 := by nlinarith [norm_nonneg (f p)]
  simpa only [one_div] using div_le_div_of_nonneg_right hs (sq_nonneg (p : ℝ))

/-- A separated sample of the residual class is covered by the large
values in any one of its bands. This is a finite counting argument,
followed by the proved prime high-moment estimate. -/
theorem exceptional_samples (D : MellinPrimeBands) (f : ℕ → ℂ)
    (hf : OneBounded f) {J j : ℕ} (hj : j < J)
    (hprime : ∀ p ∈ D.primes j, p.Prime)
    (M : ℕ → ℕ) (r : ℕ)
    (hM : ∀ k ∈ D.bins j, ∀ p ∈ D.primes j, D.bin j p = k → p ≤ M k)
    (hV : ∀ k ∈ D.bins j, 0 < D.threshold j k)
    (S : Finset ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hS : ∀ t ∈ S, |t| ≤ T)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x-y|)
    (hres : ∀ t ∈ S, t ∈ mrtNoSmallBand D.bins (D.polynomial f) D.threshold J) :
    (S.card : ℝ) ≤ ∑ k ∈ D.bins j, D.sampleCost j k (M k) r T := by
  let E : ℕ → Finset ℝ := fun k => S.filter
    (fun t => D.threshold j k ≤ ‖D.polynomial f j k t‖)
  have hcover : S ⊆ (D.bins j).biUnion E := by
    intro t ht
    obtain ⟨k, hk, hkt⟩ := mrt_no_small_band_large_witness D.bins (D.polynomial f)
      D.threshold hj (hres t ht)
    exact mem_biUnion.mpr ⟨k, hk, mem_filter.mpr ⟨ht, hkt.le⟩⟩
  calc
    (S.card : ℝ) ≤ ((D.bins j).biUnion E).card := by exact_mod_cast card_le_card hcover
    _ ≤ ∑ k ∈ D.bins j, ((E k).card : ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ _ := by
      apply sum_le_sum
      intro k hk
      apply D.bin_sample_bound f hf j k (M k) r hprime (hM k hk) (hV k hk)
        (E k) hT
      · intro t ht
        exact hS t (mem_filter.mp ht).1
      · intro x hx y hy hxy
        exact hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy
      · intro t ht
        exact (mem_filter.mp ht).2

end MellinPrimeBands
end JointDickman

end OAI
