import OAI.NumberTheory.JointDickman.Counting.LagParameterVariation
import OAI.NumberTheory.JointDickman.Amplification.WeightedPolynomialBounds

namespace OAI

/-! # Uniform lag variation of the polynomial model's finite coefficients -/
namespace JointDickman
open Finset Filter Classical
open scoped Topology

noncomputable def weightedTermCoefficient (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T t : ℝ) (S : Finset ℤ) (s r : ℤ → ℝ) (a b : Fin m) : ℝ :=
  primeCoarseCoefficient m B
    (geometricWindowKernel m B t (Real.log (1/4)) (Real.log (17/4)) S
      (endpointSpatialWeight m B t (T/j)
        (fun k => (r k*(P.coeff d*(s k)^(d 3)))*
          coefficientDensity c H B (Real.log (Real.exp ((k : ℝ)*t)/T)/B))
        (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2)))) a b

theorem weightedPolynomialTermKernel_coefficients (P : MvPolynomial (Fin 4) ℝ)
    (d : Fin 4 →₀ ℕ) (m B j : ℕ) (c : ℕ → ℝ) (H : ℕ)
    (T t : ℝ) (S : Finset ℤ) (s r : ℤ → ℝ) (x y : auxiliaryPrimes B → Bool) :
    weightedPolynomialTermKernel P d m B j c H T t S s r x y =
      ∑ a, ∑ b, weightedTermCoefficient P d m B j c H T t S s r a b*
        primeCoarseFeature m B a x*primeCoarseFeature m B b y := rfl

theorem weightedTermCoefficient_lag_variation
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput)
    (P : MvPolynomial (Fin 4) ℝ) (d : Fin 4 →₀ ℕ)
    {m : ℕ} (hm : 0 < m) (c : ℕ → ℝ) (hc : c 0 = squarefreeLeadingConstant (1/2))
    (H : ℕ) {t η : ℝ} (ht : 0 < t) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ B : ℕ in atTop, ∀ (j k : ℕ) (T : ℝ),
      0 < T → η*T ≤ j → η*T ≤ k → ∀ S : Finset ℤ,
      (∀ u ∈ S, (9/10 : ℝ)*B ≤ Real.log (Real.exp ((u : ℝ)*t)/T)) →
      ∀ s : ℤ → ℝ, (∀ u ∈ S, |s u| ≤ 3) →
      ∀ r : ℤ → ℝ, (∀ u ∈ S, |r u| ≤ 1) → ∀ a b : Fin m,
      |weightedTermCoefficient P d m B j c H T t S s r a b-
        weightedTermCoefficient P d m B k c H T t S s r a b| ≤
        C*|(j : ℝ)-k|/T := by
  obtain ⟨D,L,hD,_,hden⟩ := coefficientDensity_bounded_lipschitz hM hMP c hc
    (by norm_num : (0 : ℝ) < 1/2) H
  obtain ⟨M₀,D₀,hM₀,_,hw₀,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 0))
  obtain ⟨M₁,D₁,hM₁,_,hw₁,_,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 1))
  obtain ⟨M₂,D₂,_,hD₂,_,hd₂,_⟩ := schwartz_value_derivative_bounds (tensorPowerFactor (d 2))
  let K : NNReal := ⟨D₂,hD₂⟩
  have hLip : LipschitzWith K (tensorPowerFactor (d 2)) := by
    apply lipschitzWith_of_nnnorm_deriv_le (tensorPowerFactor (d 2)).differentiable
    intro x
    change ‖deriv (tensorPowerFactor (d 2)) x‖₊ ≤ K
    exact_mod_cast hd₂ x
  let R := |P.coeff d| *(3 : ℝ)^(d 3)*D
  let C₀ := channelMesh m*(2*(((1+Real.log (17/4)-Real.log (1/4))/t+1)*
    (R*M₀*M₁*(K : ℝ)*Real.exp (Real.log (17/4))))*(Real.log (17/4)-Real.log (1/4)+2))
  have hlogs : Real.log (1/4) ≤ Real.log (17/4) := Real.log_le_log (by norm_num) (by norm_num)
  have hR : 0 ≤ R := by positivity
  have hC₀ : 0 ≤ C₀ := by
    have hh : 0 ≤ (1+Real.log (17/4)-Real.log (1/4))/t+1 := by
      apply add_nonneg _ zero_le_one
      exact div_nonneg (by linarith) ht.le
    have hw : 0 ≤ Real.log (17/4)-Real.log (1/4)+2 := by linarith
    dsimp only [C₀]
    exact mul_nonneg (channelMesh_pos hm).le
      (mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg hh (by positivity))) hw)
  refine ⟨C₀/η^2,by positivity,?_⟩
  filter_upwards [hden,eventually_ge_atTop 1] with B hd hB
  intro j k T hT hj hk S hlog s hs r hr a b
  have hcoeff : ∀ u ∈ S, |(r u*(P.coeff d*(s u)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ R := by
    intro u hu
    have hden' : |coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B)| ≤ D := by
      apply hd.1
      apply (le_div_iff₀ (show (0 : ℝ) < B by exact_mod_cast (Nat.zero_lt_of_lt hB))).mpr
      nlinarith [hlog u hu]
    rw [abs_mul,abs_mul,abs_mul,abs_pow]
    apply mul_le_mul _ hden' (abs_nonneg _) (by positivity)
    have hp := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (hs u hu) (d 3)) (abs_nonneg (P.coeff d))
    exact (mul_le_mul (hr u hu) hp (mul_nonneg (abs_nonneg _) (pow_nonneg (abs_nonneg _) _))
      zero_le_one).trans_eq (one_mul _)
  have he := geometric_coarseCoefficient_parameter_difference hm hB ht hlogs hR hM₀ hM₁
    S (fun u => (r u*(P.coeff d*(s u)^(d 3)))*
      coefficientDensity c H B (Real.log (Real.exp ((u : ℝ)*t)/T)/B))
    (tensorPowerFactor (d 0)) (tensorPowerFactor (d 1)) (tensorPowerFactor (d 2))
    (β := T/j) (γ := T/k) hLip hcoeff hw₀ hw₁ a b
  change |weightedTermCoefficient P d m B j c H T t S s r a b-
    weightedTermCoefficient P d m B k c H T t S s r a b| ≤ C₀*|T/j-T/k| at he
  have hb := he.trans (mul_le_mul_of_nonneg_left (reciprocal_lag_difference hT hη hj hk) hC₀)
  convert hb using 1
  field_simp

end JointDickman

end OAI
