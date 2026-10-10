import OAI.NumberTheory.CubicMoment.Estimates.PrimeBins
import OAI.NumberTheory.CubicMoment.Estimates.PrimeTupleDecomposition
import OAI.NumberTheory.CubicMoment.Estimates.FixedScalePowers

namespace OAI

/-! Uniform norm distortion for the multiplicative bin surrogate.
The bin ratio is fixed before the norm parameter; all selected subsets
simultaneously satisfy the manuscript's small-power distortion bound. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_norm_ge_two {p : Eisenstein} (hp : primaryPrime p) : 2 ≤ norm p := by
  have hz := normNat_ne_zero hp.2.ne_zero
  have ho : normNat p ≠ 1 := by
    intro h
    apply hp.2.not_isUnit
    apply isUnit_of_norm_eq_one
    rw [←normNat_cast,h]
    norm_num
  have h : 2 ≤ normNat p := by omega
  rw [←normNat_cast]
  exact_mod_cast h

lemma primary_prime_subset_norm_le {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    norm (∏ p ∈ s, p) ≤ norm n := by
  have he := (primaryFactorRemainder_spec hn hs hsub).2.2
  exact norm_le_of_dvd_nonzero (primary_ne_zero hn) ⟨primaryFactorRemainder n s,he.symm⟩

lemma primary_prime_subset_two_pow_le {n : Eisenstein} (hn : primary n) (hs : Squarefree n)
    {s : Finset Eisenstein} (hsub : s ⊆ primaryPrimeFactors n) :
    (2:ℝ)^s.card ≤ norm n := by
  calc
    _ = ∏ _p ∈ s, (2:ℝ) := by rw [Finset.prod_const]
    _ ≤ ∏ p ∈ s, norm p := Finset.prod_le_prod₀ (fun _ _ => by norm_num)
      (fun p hp => primaryPrime_norm_ge_two (primaryPrimeFactor_spec hn (hsub hp)).1)
    _ = norm (∏ p ∈ s, p) := (norm_finset_prod _ _).symm
    _ ≤ norm n := primary_prime_subset_norm_le hn hs hsub

lemma primeSurrogate_norm_bounds (s : Finset Eisenstein) (b : Eisenstein → ℕ)
    (ell : ℕ → ℝ) {ρ : ℝ} (_hρ : 0 ≤ ρ)
    (hcell : ∀ p ∈ s, 0 ≤ ell (b p) ∧ ell (b p) ≤ norm p ∧ norm p ≤ ρ*ell (b p)) :
    primeSurrogate s b ell ≤ norm (∏ p ∈ s, p) ∧
      norm (∏ p ∈ s, p) ≤ ρ^s.card*primeSurrogate s b ell := by
  rw [norm_finset_prod]
  constructor
  · exact Finset.prod_le_prod₀ (fun p hp => (hcell p hp).1) (fun p hp => (hcell p hp).2.1)
  · calc
      _ ≤ ∏ p ∈ s, ρ*ell (b p) :=
        Finset.prod_le_prod₀ (fun p _ => norm_nonneg p) (fun p hp => (hcell p hp).2.2)
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]; rfl

/-- A fixed ratio larger than one can be chosen so that all selected
subproducts in every squarefree envelope have distortion at most
X^(kappa/4). No bin occupancy vector is enumerated. -/
theorem uniform_prime_bin_distortion {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∀ᶠ X : ℝ in atTop,
      ∀ n : Eisenstein, primary n → Squarefree n → norm n ≤ C*X →
      ∀ s : Finset Eisenstein, s ⊆ primaryPrimeFactors n →
      ∀ (b : Eisenstein → ℕ) (ell : ℕ → ℝ),
        (∀ p ∈ s, 0 ≤ ell (b p) ∧ ell (b p) ≤ norm p ∧ norm p ≤ ρ*ell (b p)) →
      primeSurrogate s b ell ≤ norm (∏ p ∈ s, p) ∧
        norm (∏ p ∈ s, p) ≤ X^(κ/4)*primeSurrogate s b ell := by
  let δ : ℝ := κ/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let ρ : ℝ := (2:ℝ)^δ
  have hρ : 1 < ρ := Real.one_lt_rpow (by norm_num) hδ
  refine ⟨ρ,hρ,?_⟩
  filter_upwards [eventually_gt_atTop (0:ℝ),
    eventually_const_mul_rpow_le (show δ < κ/4 by dsimp [δ]; linarith) (C^δ)] with X hX hbound
  intro n hn hs hnX s hsub b ell hcell
  have hpow : ρ^s.card ≤ X^(κ/4) := by
    calc
      _ = ((2:ℝ)^s.card)^δ := by
        dsimp [ρ]
        rw [←Real.rpow_mul_natCast (by norm_num),←Real.rpow_natCast_mul (by norm_num),mul_comm]
      _ ≤ (C*X)^δ := Real.rpow_le_rpow (by positivity)
        ((primary_prime_subset_two_pow_le hn hs hsub).trans hnX) hδ.le
      _ = C^δ*X^δ := Real.mul_rpow hC.le hX.le
      _ ≤ _ := hbound
  obtain ⟨hlo,hhi⟩ := primeSurrogate_norm_bounds s b ell (zero_lt_one.trans hρ).le hcell
  exact ⟨hlo,hhi.trans (mul_le_mul_of_nonneg_right hpow
    (Finset.prod_nonneg (fun p hp => (hcell p hp).1)))⟩

end CubicFirstMoment

end

end OAI
