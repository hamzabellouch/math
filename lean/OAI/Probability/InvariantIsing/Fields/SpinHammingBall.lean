import OAI.Probability.InvariantIsing.Fields.SpinSliceProjection
import OAI.Probability.InvariantIsing.Magnetic.RestrictedSpinLog

namespace OAI

/-! Exponential bounds for Hamming balls and for the fibers of a
nearest-slice map. The bound is uniform over the target configuration. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def spinHammingBall {N : ℕ} (τ : Spin N) (d : ℕ) : Finset (Spin N) :=
  Finset.univ.filter (fun σ => hammingDist σ τ ≤ d)

lemma sum_exp_hamming {N : ℕ} (τ : Spin N) (t : ℝ) :
    (∑ σ : Spin N, Real.exp (-t * (hammingDist σ τ : ℝ))) =
      (1 + Real.exp (-t)) ^ N := by
  classical
  have he (σ : Spin N) : (hammingDist σ τ : ℝ) =
      ∑ i, if σ i ≠ τ i then (1 : ℝ) else 0 := by
    simp [hammingDist, Finset.sum_ite]
  simp_rw [he, Finset.mul_sum, Real.exp_sum]
  have hp := Fintype.prod_sum (fun (i : Fin N) (b : Bool) =>
    Real.exp (-t * (if b ≠ τ i then (1 : ℝ) else 0)))
  rw [← hp]
  have hi (i : Fin N) : (∑ b : Bool, Real.exp (-t * (if b ≠ τ i then (1 : ℝ) else 0))) =
      1 + Real.exp (-t) := by
    cases τ i <;> simp [add_comm]
  simp only [hi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma card_spinHammingBall_le {N : ℕ} (τ : Spin N) (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    ((spinHammingBall τ d).card : ℝ) ≤
      Real.exp (t * d) * (1 + Real.exp (-t)) ^ N := by
  have hsum : ((spinHammingBall τ d).card : ℝ) ≤
      Real.exp (t * d) * ∑ σ : Spin N, Real.exp (-t * (hammingDist σ τ : ℝ)) := by
    calc
      _ = ∑ _σ ∈ spinHammingBall τ d, (1 : ℝ) := by simp
      _ ≤ ∑ σ ∈ spinHammingBall τ d,
          Real.exp (t * d) * Real.exp (-t * (hammingDist σ τ : ℝ)) := by
        apply Finset.sum_le_sum
        intro σ hσ
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        have hd : (hammingDist σ τ : ℝ) ≤ d := by
          exact_mod_cast (Finset.mem_filter.mp hσ).2
        nlinarith
      _ ≤ ∑ σ : Spin N, Real.exp (t * d) * Real.exp (-t * (hammingDist σ τ : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun σ _ _ => (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le)
      _ = _ := (Finset.mul_sum _ _ _).symm
  rwa [sum_exp_hamming] at hsum

lemma spin_map_fiber_bound {N : ℕ} (S : Finset (Spin N)) (f : Spin N → Spin N)
    (d : ℕ) {t : ℝ} (ht : 0 ≤ t) (hf : ∀ σ ∈ S, hammingDist σ (f σ) ≤ d)
    (τ : Spin N) :
    ((S.filter fun σ => f σ = τ).card : ℝ) ≤
      Real.exp (t * d) * (1 + Real.exp (-t)) ^ N := by
  have hsub : (S.filter fun σ => f σ = τ) ⊆ spinHammingBall τ d := by
    intro σ hσ
    obtain ⟨hS, he⟩ := Finset.mem_filter.mp hσ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa only [← he] using hf σ hS⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (card_spinHammingBall_le τ d ht)

lemma restrictedSpinLog_le_of_hamming_map {N : ℕ} (S T : Finset (Spin N))
    (hS : S.Nonempty) (hT : T.Nonempty) (f : Spin N → Spin N)
    (H K : Spin N → ℝ) (c : ℝ) (d : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ σ ∈ S, f σ ∈ T) (hd : ∀ σ ∈ S, hammingDist σ (f σ) ≤ d)
    (hE : ∀ σ ∈ S, H σ ≤ K (f σ) + c) :
    restrictedSpinLog S H ≤ restrictedSpinLog T K + c +
      t * d + N * Real.log (1 + Real.exp (-t)) := by
  have hpos : 0 < 1 + Real.exp (-t) := by positivity
  have hh := restrictedSpinLog_le_of_map S T hS hT f H K c
    (Real.exp (t * d) * (1 + Real.exp (-t)) ^ N) (by positivity) hf hE
    (fun τ _ => spin_map_fiber_bound S f d ht hd τ)
  rw [Real.log_mul (Real.exp_ne_zero _) (pow_pos hpos N).ne',
    Real.log_exp, Real.log_pow] at hh
  linarith

end InvariantIsing

end

end OAI
