import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeFactorization
import OAI.NumberTheory.CubicMoment.Estimates.PrimeErrorPointwise
import OAI.NumberTheory.CubicMoment.Estimates.PrimeExclusionSavingPowers

namespace OAI

/-! The repeated-prime error in the literal full convolution has every
logarithmic saving for rough coordinates. Its support saving is proved. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem full_prime_error_log_saving {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0)
    {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) (k : ℕ) :
    ∃ L₀ : ℝ, ∀ (r : γ) (X : ι → ℝ), L₀ ≤ L r → 1 ≤ L r →
      (∀ i, 1 ≤ X i) → (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      ∀ (e : Eisenstein) (χ : Eisenstein → ℂ),
      (∀ b ∈ orderedConvolutionSupport (fullPrimeSupport R (W r) X), ‖χ b‖ ≤ 1) →
      ∀ (ℓ : ℤ) (u t : ℝ),
      ‖twistedErrorPrimePolynomial (fullPrimeSupport R (W r) X)
        (excludedPrimeWeight e (W r) X) χ ℓ u t‖ ≤ L r/(1+Real.log (L r))^k := by
  classical
  obtain ⟨K,hK,hbound⟩ := primeConvolutionError_cutoff_bound (ι := ι)
  obtain ⟨M,m,hM,hMb⟩ := hW.norm_log_bound
  let n := Fintype.card ι
  let C := K*R^n*(n^n:ℕ)*M^n
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg hK.le
    (pow_nonneg (zero_le_one.trans hR) _)) (Nat.cast_nonneg _)) (pow_nonneg hM _)
  obtain ⟨L₀,hL₀⟩ := eventually_atTop.mp
    (exclusion_log_absorption (c := 1) (d := 1-c/4) (ε := 1)
      (by norm_num) (by linarith) hC (m*n) k)
  refine ⟨L₀,?_⟩
  intro r X hL₀' hL hX hprod hrough e χ hχ ℓ u t
  have hLp : 0 < L r := zero_lt_one.trans_le hL
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg hL]
  have hXp : ∀ i, 0 < X i := fun i => zero_lt_one.trans_le (hX i)
  have hprime : ∀ i, ∀ p ∈ fullPrimeSupport R (W r) X i,
      primaryPrime p ∧ (L r)^c < norm p := by
    intro i p hp
    refine ⟨fullPrimeSupport_prime R (W r) X i p hp,?_⟩
    have hn := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
    have hcont := ((hW.smooth (r,i)).continuous)
    have hh : 1 < norm p/X i := lt_of_not_ge (fun h => hn
      (continuous_zero_on_lower_closed hcont (hlo r i) h))
    have hh' : X i < norm p := by simpa only [one_mul] using (lt_div_iff₀ (hXp i)).mp hh
    exact (hrough i).trans_lt hh'
  have hnorm : ∀ f ∈ Fintype.piFinset (fullPrimeSupport R (W r) X),
      norm (∏ i, f i) ≤ R^n*L r := by
    intro f hf
    rw [norm_finset_prod]
    calc
      _ ≤ ∏ i, (R*X i) := Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ =>
        (mem_primaryElementBall.mp (Finset.mem_filter.mp
          (Finset.mem_filter.mp ((Fintype.mem_piFinset.mp hf) i)).1).1).2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,Finset.card_univ,hprod,n]
  have hw : ∀ i, ∀ p ∈ fullPrimeSupport R (W r) X i,
      ‖excludedPrimeWeight e (W r) X i p‖ ≤ M*(1+Real.log (L r))^m := by
    intro i p _
    rw [excludedPrimeWeight,norm_mul]
    apply le_trans (mul_le_of_le_one_right (_root_.norm_nonneg _) ?_) (hMb (r,i) _)
    rw [primeExclusionCharacter_apply]
    split_ifs <;> simp
  have hb := hbound (fullPrimeSupport R (W r) X) (excludedPrimeWeight e (W r) X)
    (fun _ => M*(1+Real.log (L r))^m) (R^n*L r) ((L r)^c)
    (mul_nonneg (pow_nonneg (zero_le_one.trans hR) _) hLp.le)
    (Real.rpow_pos_of_pos hLp _) (fun _ => mul_nonneg hM (pow_nonneg hz.le _))
    hprime hnorm hw χ hχ ℓ u t
  have he : (L r)^(1-c/4) = L r*(L r)^(c*(-(1/4:ℝ))) := by
    rw [show 1-c/4 = 1+c*(-(1/4:ℝ)) by ring,Real.rpow_add hLp,Real.rpow_one]
  have heq : K*(R^n*L r)*((L r)^c)^(-(1/4:ℝ))*(n^n:ℕ)*
      (∏ _i : ι, M*(1+Real.log (L r))^m) =
      C*(L r)^(1-c/4)*(1+Real.log (L r))^(m*n) := by
    rw [Finset.prod_const,Finset.card_univ,mul_pow,← pow_mul,← Real.rpow_mul hLp.le,he]
    dsimp [C,n]
    ring
  change _ ≤ K*(R^n*L r)*((L r)^c)^(-(1/4:ℝ))*(n^n:ℕ)*
    (∏ _i : ι, M*(1+Real.log (L r))^m) at hb
  rw [heq] at hb
  apply hb.trans
  simpa only [Real.rpow_one] using hL₀ (L r) hL₀' (L r) ((L r)^(1-c/4))
    (Real.rpow_nonneg hLp.le _) le_rfl (by rw [Real.rpow_one])

end CubicFirstMoment

end

end OAI
