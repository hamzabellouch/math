import OAI.NumberTheory.CubicMoment.Angular.AngularNoncubePoissonTotal
import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeTransition
import OAI.NumberTheory.CubicMoment.Estimates.SinglePrimeHeight

namespace OAI

/-! The prime transition variance from the precise published noncube
inputs. No transition or dispersion theorem of the new paper is assumed. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem angular_single_prime_transition_variance {γ : Type*}
    (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C R M : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V)
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hVM : ∀ x, ‖V x‖ ≤ M)
    (hcut : ∀ x, R < x → V x = 0)
    (L : γ → ℝ) (W : γ → ℝ → ℂ) (hL : ∀ r, 1 ≤ L r)
    (hW : UniformLogWeights W) (hlo : ∀ r x, x < 1 → W r x = 0)
    (hhi : ∀ r x, 2 < x → W r x = 0) (k U : ℕ) :
    ∃ η K T₀ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < K ∧
      ∀ (r : γ) (A u : ℝ), T₀ ≤ L r → (2*L r)^(1/2:ℝ) < L r →
      (L r)^(1-η/4) ≤ A → A ≤ (L r)^2 → |u| ≤ (1+Real.log (L r))^U →
      let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
      let β := angularHeightPrimeCoefficient ℓ 2 (fun _ : Unit => W r) (fun _ => L r)
      ‖smoothedDispersionVariance S β u V A‖ ≤ K*(
        A*(∑ p ∈ S, ‖β p‖^2) +
        A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2 +
        A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by
  obtain ⟨η,σ,hη,hη1,hσ,hmain⟩ := angular_noncube_poisson_total_saving ℓ
    (γ := γ) (ι := Unit) (c := 1/2) (R := 2) hSW hℓ hpub hHuxley hperiod
    hMV hC (by norm_num) (by norm_num) (by norm_num) hGI hGQ V hV hV' k U
  obtain ⟨Kn,T₀,hKn,hn⟩ := hmain L (fun r _ => W r) hL
    (uniformLogWeights_prime_coordinates L W hL hW) (fun r _ => hlo r) (fun r _ => hhi r)
  obtain ⟨Kc,hKc,hc⟩ := prime_variance_transition_bound V hV hV' hR hM hVM hcut
  refine ⟨η,Kc+Kn,T₀,hη,hη1,by positivity,?_⟩
  intro r A u hT hrough hAlo hAhi hu
  dsimp only
  let S := fullSquarefreePrimeSupport 2 (fun _ : Unit => W r) (fun _ => L r) 1
  let β := angularHeightPrimeCoefficient ℓ 2 (fun _ : Unit => W r) (fun _ => L r)
  have hB : 0 < L r := zero_lt_one.trans_le (hL r)
  have hA : 0 < A := (Real.rpow_pos_of_pos hB _).trans_le hAlo
  have hS (p : Eisenstein) (hp : p ∈ S) : primaryPrime p := by
    dsimp only [S] at hp
    rw [fullSquarefreePrimeSupport_unit] at hp
    exact fullPrimeSupport_prime 2 (fun _ : Unit => W r) (fun _ => L r) () p hp
  have hN (p : Eisenstein) (hp : p ∈ S) : L r ≤ norm p := by
    have hh := (fullPrimeProduct_norm_bounds 2 (fun _ : Unit => W r) (fun _ => L r)
      (fun _ => hB) (fun _ => hlo r) (fun _ => hhi r) (Finset.mem_filter.mp hp).1).1
    simpa only [Fintype.prod_unique] using hh
  have hpq (p : Eisenstein) (hp : p ∈ S) (q : Eisenstein) (hq : q ∈ S) :
      (∑ t ∈ primaryPrimeFactors p ∪ primaryPrimeFactors q, 1/norm t) ≤ 4 := by
    have hh := fullPrime_pair_reciprocal_sum_le (D := L r/2) (by positivity)
      (fun _ : Unit => W r) (fun _ => L r) (fun _ => hB)
      (fun _ => hlo r) (fun _ => hhi r) (fun _ => by linarith) 1 hp hq
    norm_num only [Fintype.card_unique,Nat.cast_one,mul_one] at hh
    apply hh.trans
    apply (div_le_iff₀ (show 0 < L r/2 by positivity)).mpr
    nlinarith [hL r]
  have hh := hc S hS β u A (L r) hA hB hAhi hN hpq
  have hnon := hn r (fun _ => L r) A 1 u hT (by simp) (fun _ => hrough)
    hAlo hAhi one_ne_zero
    (by simpa only [norm_one_eq] using Real.one_le_rpow (hL r) hσ.le) hu
  change ‖noncubePoissonContribution S β u V A‖ ≤ _ at hnon
  change ‖smoothedDispersionVariance S β u V A‖ ≤ (Kc+Kn)*(
    A*(∑ p ∈ S, ‖β p‖^2) +
    A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2 +
    A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k)
  apply (hh.trans (add_le_add (le_refl _) hnon)).trans
  have he : 0 ≤ A*(∑ p ∈ S, ‖β p‖^2) :=
    mul_nonneg hA.le (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hm : 0 ≤ A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2 := by positivity
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  have hq : 0 ≤ A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k := by positivity
  calc
    _ = Kc*(A*(∑ p ∈ S, ‖β p‖^2)) +
        Kc*(A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2) +
        Kn*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) := by ring
    _ ≤ (Kc+Kn)*(A*(∑ p ∈ S, ‖β p‖^2)) +
        (Kc+Kn)*(A^(2/3:ℝ)*(L r)^(-(1/3:ℝ))*(∑ p ∈ S, ‖β p‖)^2) +
        (Kc+Kn)*(A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(1+Real.log (L r))^k) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (by linarith) he)
        (mul_le_mul_of_nonneg_right (by linarith) hm))
        (mul_le_mul_of_nonneg_right (by linarith) hq)
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
