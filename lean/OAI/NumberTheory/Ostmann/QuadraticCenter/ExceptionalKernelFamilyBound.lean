import OAI.NumberTheory.Ostmann.QuadraticCenter.ConductorKernelCandidates
import OAI.NumberTheory.Ostmann.Characters.FiniteKernelExclusion

namespace OAI

/-! # The total population removed by one exceptional conductor -/

namespace Ostmann

private theorem kernel_sqrt_quotient_bound (X : ℝ) (q : ℕ) (d : ℤ)
    (hX : 0 ≤ X) (hq : 0 < q) (hd : q ≤ 4 * d.natAbs) :
    X / Real.sqrt |(d : ℝ)| ≤ 2 * (X / Real.sqrt (q : ℝ)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hdR : (q : ℝ) ≤ 4 * |(d : ℝ)| := by
    have hh : (q : ℝ) ≤ 4 * (d.natAbs : ℝ) := by exact_mod_cast hd
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  have hdpos : 0 < |(d : ℝ)| := by nlinarith
  have hroot : Real.sqrt (q : ℝ) ≤ 2 * Real.sqrt |(d : ℝ)| := by
    have hh := Real.sqrt_le_sqrt hdR
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)] at hh
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at hh
    exact hh
  rw [show 2 * (X / Real.sqrt (q : ℝ)) = (2 * X) / Real.sqrt (q : ℝ) by ring]
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hdpos) (Real.sqrt_pos.mpr hqR)).mpr
  calc
    X * Real.sqrt (q : ℝ) ≤ X * (2 * Real.sqrt |(d : ℝ)|) :=
      mul_le_mul_of_nonneg_left hroot hX
    _ = (2 * X) * Real.sqrt |(d : ℝ)| := by ring

/-- At most 32 possible signed products are lost. The conductor lower bound
replaces each product size in the previously proved population estimate. -/
theorem exists_exceptional_kernel_family_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset ℤ) (f g : ℤ → ℤ)
      (r s : ℤ → ℕ) (m q : ℕ) (h : ℤ) (X : ℝ),
      0 < m → 0 < q → 0 ≤ X →
      (∀ x ∈ S, f x ≠ 0) → (∀ y ∈ T, g y ≠ 0) →
      h.natAbs.Coprime m →
      (∀ x ∈ S, f x * (r x : ℤ) ^ 2 = (m : ℤ) * x - h) →
      (∀ y ∈ T, g y * (s y : ℤ) ^ 2 = (m : ℤ) * y - h) →
      (∀ x ∈ S, ∀ y ∈ S, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ T, ∀ y ∈ T, |((x - y : ℤ) : ℝ)| ≤ X) →
      (∀ x ∈ S, ∀ y ∈ T, (f x).natAbs.Coprime (g y).natAbs) →
      (((S.product T).filter fun z => f z.1 * g z.2 ∈ largeConductorKernelCandidates q).card : ℝ) ≤
        C * (X / Real.sqrt (q : ℝ) + 2 * Real.sqrt (X * m) + m) := by
  obtain ⟨C, hC, hbound⟩ := exists_endpoint_kernel_product_bound
  refine ⟨64 * C, by positivity, ?_⟩
  intro S T f g r s m q h X hm hq hX hf hg hred hr hs hspanS hspanT hcross
  let B := X / Real.sqrt (q : ℝ) + 2 * Real.sqrt (X * m) + m
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hd (d : ℤ) (hd : d ∈ largeConductorKernelCandidates q) :
      (((S.product T).filter fun z => f z.1 * g z.2 = d).card : ℝ) ≤ 2 * C * B := by
    have hb := hbound S T f g r s m h d X hm hX hf hg hred hr hs hspanS hspanT hcross
    rw [← kernel_pair_filter_card] at hb
    have hquot := kernel_sqrt_quotient_bound X q d hX hq (Finset.mem_filter.mp hd).2
    have ht : X / Real.sqrt |(d : ℝ)| + 2 * Real.sqrt (X * m) + m ≤ 2 * B := by
      dsimp [B]
      linarith [Real.sqrt_nonneg (X * m), show (0 : ℝ) ≤ m from Nat.cast_nonneg m]
    exact hb.trans ((mul_le_mul_of_nonneg_left ht hC.le).trans_eq (by ring))
  have hb := kernel_pair_finite_exclusion_bound S T f g (largeConductorKernelCandidates q)
    (2 * C * B) hd
  have hcard : ((largeConductorKernelCandidates q).card : ℝ) ≤ 32 := by
    exact_mod_cast largeConductorKernelCandidates_card q
  calc
    _ ≤ (largeConductorKernelCandidates q).card * (2 * C * B) := hb
    _ ≤ 32 * (2 * C * B) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (mul_nonneg (by norm_num) hC.le) hB)
    _ = _ := by dsimp [B]; ring

end Ostmann

end OAI
