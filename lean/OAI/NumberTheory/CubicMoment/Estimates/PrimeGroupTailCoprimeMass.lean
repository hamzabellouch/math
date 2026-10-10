import OAI.NumberTheory.CubicMoment.Estimates.DivisorCharacterMass
import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailAllFrequency
import OAI.NumberTheory.CubicMoment.Estimates.UniformNormHeight

namespace OAI

/-! Small-B power saving with every common divisor retained. The only
loss in the genuine coprimality expansion is the proved divisor energy. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeGroupTail_divisor_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B → (Z:ℝ)^(1/50:ℝ) ≤ T →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hpower⟩ := primeGroupTail_all_frequency_height_power hMV hC hHuxley
  obtain ⟨D,hD,henergy⟩ := divisor_row_energy_small_power (by norm_num : (0:ℝ) < 1/40000)
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro S H U β Z B T u hZ hB hT hU hS hsize hH
  have hz : 0 < (Z:ℝ) := zero_lt_one.trans_le hZ
  let F := fun d : Finset Eisenstein => S.filter (fun a => (∏ p ∈ d, p) ∣ a)
  have hrow (d : Finset Eisenstein) :
      dyadicHeightMean (fun t => finiteCharacterMass (F d) H β (t+u)) T ≤
        K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*∑ a ∈ F d, ‖β a‖^2 := by
    simpa only [finiteCharacterMass,theta_zero,mul_one] using
      hpower (F d) H β Z B T u 0 hZ hB hT
        (fun a ha => hS a (Finset.mem_filter.mp ha).1) hsize hH
  have hsum : dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
      K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*
        (∑ d ∈ U.powerset, ∑ a ∈ F d, ‖β a‖^2) := by
    unfold divisorCharacterMass
    rw [dyadicHeightMean_sum U.powerset
      (fun d t => finiteCharacterMass (F d) H β (t+u))
      (fun d _ => (finiteCharacterMass_continuous (F d) H β).comp
        (continuous_id.add continuous_const)),Finset.mul_sum]
    exact Finset.sum_le_sum (fun d _ => hrow d)
  have he := henergy S U β (Z:ℝ) hU hS
  calc
    _ ≤ K*(Z:ℝ)^(1-1/20000:ℝ)*B^(1/3:ℝ)*
        (D*(Z:ℝ)^(1/40000:ℝ)*∑ a ∈ S, ‖β a‖^2) :=
      hsum.trans (mul_le_mul_of_nonneg_left he (by positivity))
    _ = (K*D)*((Z:ℝ)^(1-1/20000:ℝ)*(Z:ℝ)^(1/40000:ℝ))*
        B^(1/3:ℝ)*∑ a ∈ S, ‖β a‖^2 := by ring
    _ = _ := by rw [← Real.rpow_add hz]; norm_num

theorem primeGroupTail_coprime_mellin_height_power
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ)
    (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (q : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T u ρ N : ℝ), 1 ≤ (Z:ℝ) → 1 ≤ B →
      (Z:ℝ)^(1/50:ℝ) ≤ T → 0 ≤ ρ → 0 < N →
      (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      8*B ≤ (Z:ℝ)^(19/20:ℝ) → (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      (1+ρ)^q*dyadicHeightMean (fun t => ∫ s : ℝ,
        ‖normDenominatorMellinCoefficient M hM V hV hV' ρ s‖*
          twistedCoprimeMellinMass S H U β (fun a => norm a/N) (t+u) s) T ≤
        K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨K,hK,hpower⟩ := primeGroupTail_divisor_height_power hMV hC hHuxley
  obtain ⟨D,hD,hmean⟩ := normMellin_signed_height_uniform M hM V hV hV' q
  refine ⟨D*K,mul_pos hD hK,?_⟩
  intro S H U β Z B T u ρ N hZ hB hT hρ hN hU hS hsize hH
  let G := divisorCharacterMass S H U β
  let A := K*(Z:ℝ)^(1-1/40000:ℝ)*B^(1/3:ℝ)*∑ a ∈ S, ‖β a‖^2
  let E := ∑ d ∈ U.powerset, (H.card:ℝ)*(S.filter (fun a => (∏ p ∈ d, p) ∣ a)).card*
    ∑ a ∈ S.filter (fun a => (∏ p ∈ d, p) ∣ a), ‖β a‖^2
  have hTp : 0 < T := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _).trans_le hT
  have hh := hmean ρ hρ G (divisorCharacterMass_continuous S H U β) E A T u
    (by dsimp [A]; positivity) hTp
    (fun t => divisorCharacterMass_bound S H U β (fun a ha => (hS a ha).1) t)
    (fun v => hpower S H U β Z B T v hZ hB hT hU hS hsize hH)
  have he (t s : ℝ) := twistedCoprimeMellinMass_eq_divisor_mass S H U β
    (fun a ha => (hS a ha).1) (t+u) s hN
  simp_rw [he]
  convert hh using 1
  dsimp [A]
  ring

end CubicFirstMoment

end

end OAI
