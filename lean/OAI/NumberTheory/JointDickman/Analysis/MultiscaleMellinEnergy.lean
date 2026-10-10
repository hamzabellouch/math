import OAI.NumberTheory.JointDickman.Analysis.MellinAngularEnergy
import OAI.NumberTheory.TwoPointCorrelations.MRTGeneralSmallEnergy
import OAI.NumberTheory.TwoPointCorrelations.MRTGeneralWitnessed
import OAI.NumberTheory.TwoPointCorrelations.MRTFrequencyPartition

namespace OAI

/-! # The actual multiscale prime partition in the Mellin convention

The costs below are the proved Ramaré extraction and amplified cofactor
costs. The integral over the class with no small prime polynomial remains
explicit; no estimate for that exceptional class is assumed here.
-/
namespace JointDickman
open Finset MeasureTheory
open TwoPointCorrelations

structure MellinPrimeBands where
  primes : ℕ → Finset ℕ
  bins : ℕ → Finset ℕ
  bin : ℕ → ℕ → ℕ
  lower : ℕ → ℕ → ℝ
  resolution : ℕ → ℝ
  threshold : ℕ → ℕ → ℝ

namespace MellinPrimeBands

noncomputable def polynomial (D : MellinPrimeBands) (f : ℕ → ℂ)
    (j k : ℕ) (t : ℝ) : ℂ :=
  mrtExponentialPolynomial ((D.primes j).filter (fun p => D.bin j p = k))
    (fun p => f p / (p : ℂ)) (fun p => -Real.log (p : ℝ)) t

structure Valid (D : MellinPrimeBands) (J N : ℕ) : Prop where
  prime : ∀ j ∈ range J, ∀ p ∈ D.primes j, p.Prime
  disjoint : Set.PairwiseDisjoint (range J : Set ℕ) D.primes
  bin_mem : ∀ j ∈ range J, ∀ p ∈ D.primes j, D.bin j p ∈ D.bins j
  resolution_one : ∀ j ∈ range J, 1 ≤ D.resolution j
  resolution_two : ∀ j ∈ range J, D.resolution j ≤ 2
  prime_bounds : ∀ j ∈ range J, ∀ p ∈ D.primes j,
    D.lower j (D.bin j p) ≤ p ∧ (p : ℝ) ≤ D.resolution j * D.lower j (D.bin j p)
  lower_two : ∀ j ∈ range J, ∀ k ∈ D.bins j, 2 ≤ D.lower j k
  upper : ∀ j ∈ range J, ∀ k ∈ D.bins j, 2 ≤ (N : ℝ) / D.lower j k
  threshold_pos : ∀ j ∈ range J, ∀ k ∈ D.bins j, 0 < D.threshold j k

noncomputable def extractionCost (D : MellinPrimeBands) (j N : ℕ) (T : ℝ) : ℝ :=
  2816 * Real.exp 1 * (T / N + 1) *
    ((∑ p ∈ D.primes j, 1 / (p : ℝ)^2) +
      (∑ p ∈ D.primes j, 1 / (p : ℝ)^2)^2 + (D.resolution j - 1))

noncomputable def initialCost (D : MellinPrimeBands) (N : ℕ) (T : ℝ) : ℝ :=
  64 * Real.exp 1 * ((D.bins 0).card : ℝ) *
    ∑ k ∈ D.bins 0, (D.threshold 0 k)^2 * (T * D.lower 0 k / N + 1)

noncomputable def laterCost (D : MellinPrimeBands) (j N : ℕ) (T : ℝ) : ℝ :=
  2 * ∑ b ∈ D.bins (j-1), ((D.bins j).card : ℝ) *
    ∑ k ∈ D.bins j, (D.threshold j k)^2 *
      ((16 * Real.exp 10 *
        (T / N + (2 : ℝ)^(mrtAmplificationOrder ⌈D.lower (j-1) b⌉₊ (D.lower j k)+1) *
          ⌈D.lower (j-1) b⌉₊) *
        ((mrtAmplificationOrder ⌈D.lower (j-1) b⌉₊ (D.lower j k)).factorial : ℝ)^2) /
        (D.threshold (j-1) b)^(2*mrtAmplificationOrder ⌈D.lower (j-1) b⌉₊ (D.lower j k)))

lemma angular_eq_dyadic (f : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    angularMellinPolynomial (Ioc N (2*N)) f t = mrtDyadicPolynomial f N t := rfl

lemma polynomial_continuous (D : MellinPrimeBands) (f : ℕ → ℂ) (j k : ℕ) :
    Continuous (D.polynomial f j k) := mrtExponentialPolynomial_continuous _ _ _

theorem firstSmallBand_energy_le (D : MellinPrimeBands) {J N : ℕ}
    (hD : D.Valid J N) (hJ : 0 < J) (hN : 0 < N)
    (f : ℕ → ℂ) (hf : Multiplicative f) (hb : OneBounded f)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S ∩ mrtFirstSmallBand D.bins (D.polynomial f) D.threshold 0,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (range J) D.primes f) N t‖^2) ≤
      D.extractionCost 0 N T + D.initialCost N T := by
  have hj : 0 ∈ range J := mem_range.mpr hJ
  apply mrt_general_typical_small_prime_energy (range J) D.primes hD.prime hD.disjoint hj
    (D.bins 0) (D.bin 0) (hD.bin_mem 0 hj) (D.lower 0) hN
    (hD.resolution_one 0 hj) (hD.resolution_two 0 hj) (hD.prime_bounds 0 hj)
    (fun k hk => le_trans (by norm_num) (hD.lower_two 0 hj k hk))
    (hD.upper 0 hj) f hf hb hT _ (Set.inter_subset_left.trans hS)
  intro k hk t ht
  exact ht.2.1 k hk

theorem laterSmallBand_energy_le (D : MellinPrimeBands) {J N j : ℕ}
    (hD : D.Valid J N) (hj : j ∈ range J) (hj0 : 0 < j) (hN : 0 < N)
    (f : ℕ → ℂ) (hf : Multiplicative f) (hb : OneBounded f)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S ∩ mrtFirstSmallBand D.bins (D.polynomial f) D.threshold j,
      ‖mrtDyadicPolynomial (mrtTypicalCoefficient (range J) D.primes f) N t‖^2) ≤
      D.extractionCost j N T + D.laterCost j N T := by
  have hp : j-1 ∈ range J := mem_range.mpr (by have := mem_range.mp hj; omega)
  apply mrt_general_typical_witnessed_energy (range J) D.primes hD.prime hD.disjoint hj
    (D.bins j) (D.bin j) (hD.bin_mem j hj) (D.lower j) hN
    (hD.resolution_one j hj) (hD.resolution_two j hj) (hD.prime_bounds j hj)
    (fun k hk => le_trans (by norm_num) (hD.lower_two j hj k hk)) f hf hb
    (D.bins (j-1)) (fun b => (D.primes (j-1)).filter (fun p => D.bin (j-1) p = b))
    (D.lower (j-1)) (fun b hb => lt_of_lt_of_le (by norm_num) (hD.lower_two _ hp b hb))
    (fun b _ p hpb => hD.prime _ hp p (mem_filter.mp hpb).1) ?_
    (D.threshold (j-1)) (hD.threshold_pos _ hp) hT
    (hSm.inter (mrt_first_small_band_measurable _ _ _ (D.polynomial_continuous f) j))
    (Set.inter_subset_left.trans hS) (D.threshold j) ?_ ?_
  · intro b _ p hpb
    obtain ⟨hmem, heq⟩ := mem_filter.mp hpb
    have hbounds := hD.prime_bounds (j-1) hp p hmem
    rw [heq] at hbounds
    exact ⟨hbounds.1, hbounds.2.trans (mul_le_mul_of_nonneg_right
      (hD.resolution_two _ hp) (by have := hD.lower_two _ hp b (heq ▸ hD.bin_mem _ hp p hmem); linarith))⟩
  · intro k hk t ht
    exact ht.2.1 k hk
  · intro t ht
    obtain ⟨b, hb, hlarge⟩ := mrt_later_band_large_witness D.bins (D.polynomial f)
      D.threshold hj0 ht.2
    exact ⟨b, hb, hlarge.le⟩

/-- Every nonexceptional class is bounded by its actual small-prime or
amplified cofactor estimate. Only the no-small-band integral is left. -/
theorem partition_energy_le (D : MellinPrimeBands) {J N : ℕ}
    (hD : D.Valid J N) (hN : 0 < N)
    (f : ℕ → ℂ) (hf : Multiplicative f) (hb : OneBounded f)
    {T : ℝ} (hT : 0 < T) {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : S ⊆ Set.Ioc (-T) T) :
    (∫ t in S, ‖angularMellinPolynomial (Ioc N (2*N))
      (mrtTypicalCoefficient (range J) D.primes f) t‖^2) ≤
    (∫ t in S ∩ mrtNoSmallBand D.bins (D.polynomial f) D.threshold J,
      ‖angularMellinPolynomial (Ioc N (2*N))
        (mrtTypicalCoefficient (range J) D.primes f) t‖^2) +
    ∑ j ∈ range J, (D.extractionCost j N T +
      if j = 0 then D.initialCost N T else D.laterCost j N T) := by
  simp_rw [angular_eq_dyadic]
  rw [mrt_frequency_partition_integral D.bins (D.polynomial f) D.threshold
    (D.polynomial_continuous f) J hSm
    (fun t => ‖mrtDyadicPolynomial (mrtTypicalCoefficient (range J) D.primes f) N t‖^2)
    (mrt_continuous_square_integrable (mrtExponentialPolynomial_continuous _ _ _) hT.le hS)]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro j hj
  split_ifs with hj0
  · subst j
    exact D.firstSmallBand_energy_le hD (mem_range.mp hj) hN f hf hb hT hS
  · exact D.laterSmallBand_energy_le hD hj (Nat.pos_of_ne_zero hj0) hN f hf hb hT hSm hS

end MellinPrimeBands
end JointDickman

end OAI
