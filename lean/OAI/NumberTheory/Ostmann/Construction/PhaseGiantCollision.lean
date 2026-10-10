import OAI.NumberTheory.Ostmann.Construction.PhaseGiantMean
import OAI.NumberTheory.Ostmann.Preliminaries.WeightedNormTriangle

namespace OAI

/-! # Collision control for the unbounded physical giant test -/

namespace Ostmann
open scoped Classical BigOperators

/-- The pointwise inverse bound grows with the prime; the empirical error uses
its counting energy instead and loses exactly one factor of the modulus. -/
theorem phaseGiantPhysical_empirical_error {p : ℕ} [NeZero p]
    (S : Finset (ZMod p)) (μ : ZMod p → ℝ) (g : ZMod p → ℂ) :
    ‖(∑ x ∈ S, (μ x : ℂ) * phaseGiantPhysical g x) -
      (S.card : ℂ)⁻¹ * ∑ x ∈ S, phaseGiantPhysical g x‖ ^ 2 ≤
        (p : ℝ) * ∑ x ∈ S, (μ x - 1 / (S.card : ℝ)) ^ 2 := by
  have henergy : (∑ x ∈ S, ‖phaseGiantPhysical g x‖ ^ 2) ≤ (p : ℝ) :=
    (Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)).trans
      (phaseGiantPhysical_energy g)
  have h := centered_test_bound S μ (phaseGiantPhysical g) p henergy
  convert h using 1
  congr 2
  simp only [Complex.ofReal_sub, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum, one_div, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- Weighted Cauchy gives the square-root error in Section 7.1 directly from
the collision budget. No pointwise bound on the inverse transform is used. -/
theorem phaseGiant_weighted_empirical_error {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (μ : ∀ i, ZMod (p i) → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (B : ℝ)
    (hbudget : (∑ i, w i * ((p i : ℝ) *
      ∑ x ∈ S i, (μ i x - 1 / ((S i).card : ℝ)) ^ 2)) ≤ B) :
    ‖∑ i, (w i : ℂ) * ((∑ x ∈ S i, (μ i x : ℂ) * phaseGiantPhysical (g i) x) -
      ((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, phaseGiantPhysical (g i) x)‖ ≤
      Real.sqrt (∑ i, w i) * Real.sqrt B := by
  let E := fun i => (∑ x ∈ S i, (μ i x : ℂ) * phaseGiantPhysical (g i) x) -
    ((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, phaseGiantPhysical (g i) x
  have he : (∑ i, w i * ‖E i‖ ^ 2) ≤ B := by
    apply le_trans _ hbudget
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (phaseGiantPhysical_empirical_error (S i) (μ i) (g i)) (hw i)
  have h := weighted_correlation_le_sqrt_energy Finset.univ w (fun _ => 1) E
    (fun i _ => hw i)
  simp only [one_mul, norm_one, one_pow, mul_one] at h
  have hc : ‖∑ i, (w i : ℂ) * E i‖ = ‖∑ i, (w i : ℂ) * star (E i)‖ := by
    calc
      _ = ‖starRingEnd ℂ (∑ i, (w i : ℂ) * E i)‖ := (Complex.norm_conj _).symm
      _ = _ := by simp only [map_sum, map_mul, Complex.conj_ofReal, Complex.star_def]
  change ‖∑ i, (w i : ℂ) * E i‖ ≤ _
  rw [hc]
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _))

/-- The complex collision estimate implies the required lower bound for the
real empirical mean before the soft-cell pigeonhole. -/
theorem phaseGiant_weighted_empirical_mean_lower {I : Type*} [Fintype I]
    (p : I → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ i, Finset (ZMod (p i))) (μ : ∀ i, ZMod (p i) → ℝ)
    (g : ∀ i, ZMod (p i) → ℂ) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (B : ℝ)
    (hbudget : (∑ i, w i * ((p i : ℝ) *
      ∑ x ∈ S i, (μ i x - 1 / ((S i).card : ℝ)) ^ 2)) ≤ B) :
    (∑ i, w i * (((S i).card : ℝ)⁻¹ *
      ∑ x ∈ S i, (phaseGiantPhysical (g i) x).re)) -
        Real.sqrt (∑ i, w i) * Real.sqrt B ≤
      ∑ i, w i * ∑ x ∈ S i, μ i x * (phaseGiantPhysical (g i) x).re := by
  have h := phaseGiant_weighted_empirical_error p S μ g w hw B hbudget
  let e : ℂ := ∑ i, (w i : ℂ) * ((∑ x ∈ S i, (μ i x : ℂ) * phaseGiantPhysical (g i) x) -
    ((S i).card : ℂ)⁻¹ * ∑ x ∈ S i, phaseGiantPhysical (g i) x)
  have he : -e.re ≤ ‖e‖ := by
    simpa only [Complex.neg_re, norm_neg] using Complex.re_le_norm (-e)
  have hr : e.re =
      (∑ i, w i * ∑ x ∈ S i, μ i x * (phaseGiantPhysical (g i) x).re) -
      (∑ i, w i * (((S i).card : ℝ)⁻¹ * ∑ x ∈ S i, (phaseGiantPhysical (g i) x).re)) := by
    dsimp only [e]
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_inv,
      Complex.re_sum, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, mul_sub, Finset.sum_sub_distrib]
  change ‖e‖ ≤ _ at h
  linarith

end Ostmann

end OAI
