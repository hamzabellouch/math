import OAI.NumberTheory.JointDickman.Counting.PolynomialTermLagVariation

namespace OAI

/-! # Uniform boundedness of the actual finite model coefficients -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem weightedTermCoefficient_bounded
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ k ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((k : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ k ∈ S, |s k| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ k ∈ S, |r k| ≤ 1) → ∀ a b : Fin m,
        |weightedTermCoefficient P d m B j c H T t S s r a b| ≤ C := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,_,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,_,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,_,hM₂,_,hw₂,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let R := |P.coeff d| *(3 : ℝ)^(d 3)*D
  let C := channelMesh m*(2*((((1+Real.log (17/4)-Real.log (1/4))/t+1)*(R*M₀*M₁*M₂)))*
    (Real.log (17/4)-Real.log (1/4)+2))
  have hR : 0 ≤ R := by positivity
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hw : 0 ≤ 1+Real.log (17/4)-Real.log (1/4) := by linarith
  have hw' : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
  have hmesh := channelMesh_pos hm
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j T S hlog s hs r hr a b
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
  apply geometric_coarseCoefficient_bound hm hB ht hlogs (by positivity) S _ _ a b
  exact endpointSpatialWeight_bound m B t (T/j) S _ _ _ _ hR hM₀ hM₁ hcoeff hw₀ hw₁ hw₂

end JointDickman

end OAI
