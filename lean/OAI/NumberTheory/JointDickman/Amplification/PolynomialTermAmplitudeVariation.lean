import OAI.NumberTheory.JointDickman.Counting.PolynomialTermLagVariation
import OAI.NumberTheory.JointDickman.Amplification.AmplitudeParameterVariation

namespace OAI

/-! # Uniform variation of the polynomial model in its cutoff parameter -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem weightedTermCoefficient_parameter_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j : ℕ) (T : ℝ) (S : Finset ℤ),
      (∀ u ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((u : ℝ)*t)/T)) →
      ∀ s₁ s₂ : ℤ → ℝ, (∀ u ∈ S, |s₁ u| ≤ 3) → (∀ u ∈ S, |s₂ u| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ u ∈ S, |r u| ≤ 1) → ∀ δ : ℝ, 0 ≤ δ →
      (∀ u ∈ S, |s₁ u-s₂ u| ≤ δ) → ∀ a b : Fin m,
      |weightedTermCoefficient P d m B j c H T t S s₁ r a b-
        weightedTermCoefficient P d m B j c H T t S s₂ r a b| ≤ C*δ := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,D₀,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,D₁,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,D₂,hM₂,_,hw₂,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let R := |P.coeff d| *(d 3 : ℝ)*(3 : ℝ)^(d 3-1)*D
  let C := channelMesh m*(2*(((1+Real.log (17/4)-Real.log (1/4))/t+1)*
    (R*M₀*M₁*M₂))*(Real.log (17/4)-Real.log (1/4)+2))
  have hR : 0 ≤ R := by positivity
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hC : 0 ≤ C := by
    have hh : 0 ≤ (1+Real.log (17/4)-Real.log (1/4))/t+1 := by
      apply add_nonneg _ zero_le_one
      exact div_nonneg (by linarith) ht.le
    have hw : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
    dsimp only [C]
    exact mul_nonneg (channelMesh_pos hm).le
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hh (by positivity))) hw)
  refine ⟨C,hC,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j T S hlog s₁ s₂ hs₁ hs₂ r hr δ hδ hdist a b
  have hcoeff : ∀ u ∈ S,
      |(r u*(P.coeff d*(s₁ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)-
        (r u*(P.coeff d*(s₂ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ R*δ := by
    intro u hu
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog u hu]
    have hp : |(s₁ u)^(d 3)-(s₂ u)^(d 3)| ≤ δ*(d 3 : ℝ)*(3 : ℝ)^(d 3-1) := by
      refine (abs_pow_sub_pow_le (s₁ u) (s₂ u) (d 3)).trans ?_
      gcongr
      · exact hdist u hu
      · exact max_le (hs₁ u hu) (hs₂ u hu)
    rw [show (r u*(P.coeff d*(s₁ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)-
        (r u*(P.coeff d*(s₂ u)^(d 3)))*coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B) =
        r u*P.coeff d*((s₁ u)^(d 3)-(s₂ u)^(d 3))*
          coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B) by ring]
    simp only [abs_mul]
    have hh := mul_le_mul
      (mul_le_mul (mul_le_mul_of_nonneg_right (hr u hu) (abs_nonneg (P.coeff d))) hp
        (abs_nonneg _) (by positivity : 0 ≤ 1*|P.coeff d|)) hden'
      (abs_nonneg _) (by positivity : 0 ≤ (1*|P.coeff d|)*(δ*(d 3 : ℝ)*(3 : ℝ)^(d 3-1)))
    convert hh using 1
    dsimp [R]
    ring
  have hh := geometric_coarseCoefficient_amplitude_difference (β := T/j) hm hB ht hlogs
    (mul_nonneg hR hδ) hM₀ hM₁ hM₂ S _ _ _ _ _ hcoeff hw₀ hw₁ hw₂ a b
  change |weightedTermCoefficient P d m B j c H T t S s₁ r a b-
    weightedTermCoefficient P d m B j c H T t S s₂ r a b| ≤ _ at hh
  convert hh using 1
  dsimp [C]
  ring

end JointDickman

end OAI
