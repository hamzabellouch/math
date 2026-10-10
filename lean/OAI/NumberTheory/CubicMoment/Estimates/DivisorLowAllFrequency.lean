import OAI.NumberTheory.CubicMoment.Estimates.DivisorLowLogSaving
import OAI.NumberTheory.CubicMoment.Estimates.DivisorLowCube

namespace OAI

/-! All nonzero frequencies in the actual coprimality expansion at
polylogarithmic height, uniformly in the common height shift. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem divisor_all_frequency_low_log_saving (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (k : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (S H U : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z : ℕ) (B T M u : ℝ), 65536 ≤ (Z:ℝ) → 1 ≤ B → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → (∀ p ∈ U, primaryPrime p) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ norm b ≤ (Z:ℝ)) →
      (∀ b ∈ S, ‖β b‖ ≤ M) → 8*B ≤ (Z:ℝ)^(3/4:ℝ) →
      (∀ h ∈ H, h ≠ 0 ∧ norm h ≤ B) →
      dyadicHeightMean (fun t => divisorCharacterMass S H U β (t+u)) T ≤
        K*M^2*(Z:ℝ)^2*B^(1/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨Kn,Cn,hKn,hn⟩ := divisor_noncube_low_log_saving hpnt hMV hC hHuxley k
  obtain ⟨Kc,Cc,hKc,hc⟩ := divisor_cube_low_log_saving hpnt hMV hC k
  refine ⟨Kn+Kc,max Cn Cc,by positivity,?_⟩
  intro S H U β Z B T M u hZ hB hM hT hU hS hβ hsize hH
  have hN1 : 1 ≤ (Z:ℝ) := by linarith
  have hL1 : 1 ≤ 1+Real.log (Z:ℝ) := by linarith [Real.log_nonneg hN1]
  have hTn := (pow_le_pow_right₀ hL1 (le_max_left Cn Cc)).trans hT
  have hTc := (pow_le_pow_right₀ hL1 (le_max_right Cn Cc)).trans hT
  let HC := H.filter (fun h => ∃ a : Eisenstein, a^3 = h)
  let HN := H.filter (fun h => ¬∃ a : Eisenstein, a^3 = h)
  let F := fun (J : Finset Eisenstein) t => divisorCharacterMass S J U β (t+u)
  have hCsub : HC ⊆ nonzeroCubeNormBall B := by
    intro h hh
    obtain ⟨hh,hcube⟩ := Finset.mem_filter.mp hh
    exact mem_nonzeroCubeNormBall (hH h hh).1 (hH h hh).2 hcube
  have hnon := hn S HN U β Z B T M u hZ hB hM hTn hU hS hβ hsize
    (fun h hh => ⟨(hH h (Finset.mem_filter.mp hh).1).1,
      (hH h (Finset.mem_filter.mp hh).1).2,(Finset.mem_filter.mp hh).2⟩)
  have hcube := hc S HC U β Z B T M u hZ (zero_le_one.trans hB) hM hTc hU hS hβ hCsub
  have hcont (J : Finset Eisenstein) : Continuous (F J) :=
    (divisorCharacterMass_continuous S J U β).comp (continuous_id.add continuous_const)
  have heq : F H = fun t => F HC t+F HN t := by
    funext t
    unfold F divisorCharacterMass
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    exact (Finset.sum_filter_add_sum_filter_not H
      (fun h => ∃ a : Eisenstein, a^3 = h) _).symm
  change dyadicHeightMean (F H) T ≤ _
  rw [heq,dyadicHeightMean_add (hcont HC) (hcont HN)]
  exact (add_le_add hcube hnon).trans_eq (by ring)

end CubicFirstMoment

end

end OAI
