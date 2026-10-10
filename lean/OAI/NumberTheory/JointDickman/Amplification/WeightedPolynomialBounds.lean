import OAI.NumberTheory.JointDickman.Amplification.WeightedPolynomialFeatures
import OAI.NumberTheory.JointDickman.Amplification.GeometricFeatureBounds

namespace OAI

/-! # Uniform bounds for the compact smooth finite-feature kernels -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem weightedPolynomialTermKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ 1) → ∀ x y,
        |weightedPolynomialTermKernel P d m B j c H T t S s r x y| ≤ C := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,_,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,_,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,_,hM₂,_,hw₂,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let R := |P.coeff d| *(3 : ℝ)^(d 3)*D
  let C := (m : ℝ)^2*(2*((((1+Real.log (17/4)-Real.log (1/4))/t+1)*(R*M₀*M₁*M₂)))*
    (Real.log (17/4)-Real.log (1/4)+2))/channelMesh m
  have hR : 0 ≤ R := by positivity
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hw : 0 ≤ 1+Real.log (17/4)-Real.log (1/4) := by linarith
  have hw' : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
  have hmesh := channelMesh_pos hm
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j T S hlog s hs r hr x y
  have hcoeff : ∀ k ∈ S, |(r k*(P.coeff d*(s k)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ R := by
    intro k hk
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog k hk]
    rw [abs_mul,abs_mul,abs_mul,abs_pow]
    apply mul_le_mul _ hden' (abs_nonneg _) (by positivity)
    have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hs k hk) (d 3)) (abs_nonneg (P.coeff d))
    exact (mul_le_mul (hr k hk) hp (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _)) zero_le_one).trans_eq (one_mul _)
  exact geometric_primeCoarseKernel_bound hm hB ht (by norm_num) (by norm_num)
    hR hM₀ hM₁ hM₂ S _ _ _ _ hcoeff hw₀ hw₁ hw₂ x y

theorem weightedPolynomialPrimeKernel_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (m : (Fin 4 →₀ ℕ) → ℕ) (hm : ∀ d, 0 < m d)
    (c : (Fin 4 →₀ ℕ) → ℕ → ℝ) (hc : ∀ d, c d 0 = squarefreeLeadingConstant (1/2))
    (H : (Fin 4 →₀ ℕ) → ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ 1) → ∀ x y,
        |weightedPolynomialPrimeKernel P m B j c H T t S s r x y| ≤ C := by
  choose C hC hbound using fun d => weightedPolynomialTermKernel_bounded hM hMP P d (hm d) (c d) (hc d) (H d) ht
  refine ⟨∑ d ∈ P.support, C d,sum_nonneg (fun d _ => hC d),?_⟩
  filter_upwards [(eventually_all_finset P.support).mpr (fun d _ => hbound d)] with B hb
  intro j T S hlog s hs r hr x y
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (fun d hd => hb d hd j T S hlog s hs r hr x y))

end JointDickman

end OAI
