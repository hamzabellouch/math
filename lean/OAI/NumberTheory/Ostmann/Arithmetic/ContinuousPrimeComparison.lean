import OAI.NumberTheory.Ostmann.Arithmetic.ContinuousIntervalMesh

namespace OAI

/-! # Comparing the full continuous weight with the retained Page measure -/

namespace Ostmann
open MeasureTheory

/-- A continuous weight with a uniform variation budget can be used directly
in the published progression estimate. No mesh parameter survives. -/
theorem PublishedProgressionInput.continuous_prime_comparison (P : PublishedProgressionInput)
    {Q q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    (u v : ℝ) (hu : 1 ≤ u) (huv : u ≤ v) (hshort : v ≤ u + 1)
    (w : ℝ → ℂ) (hwc : ContinuousOn w (Set.Icc u v)) (V : ℝ)
    (hV : ∀ (s : ℕ → ℝ), Monotone s → ∀ N, s 0 = u → s N = v →
      discreteVariation (fun j => w (s j)) N ≤ V) :
    ‖complexPrimeInterval q a u v w -
        ∫ y in Set.Ioc u v, w y * (selectedPrimeLogDensity P Q q a y : ℂ)‖ ≤
      V * (18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
        Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ)))) := by
  let M := reciprocalPrimeInterval q a (Real.exp u) (Real.exp v) + 2 * (v - u)
  have hM : 0 ≤ M := add_nonneg (reciprocalPrimeInterval_nonneg q a _ _)
    (mul_nonneg (by norm_num) (sub_nonneg.mpr huv))
  have hM1 : 0 < M + 1 := by linarith
  have hE : 0 ≤ 18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt u) +
      Real.exp (-P.kappa * u / Real.log (4 * (Q : ℝ))) := by
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.errorConstant_nonneg)
      (Real.exp_pos _).le) (Real.exp_pos _).le
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε / (M + 1)
  have hη : 0 < η := div_pos hε hM1
  obtain ⟨s, N, _hN, hs, hs0, hsN, hosc⟩ := continuous_interval_mesh u v huv w hwc η hη
  have hc : ContinuousOn w (Set.Icc (s 0) (s N)) := by simpa only [hs0, hsN] using hwc
  have hb := P.prime_partition_variation hQ hq hqQ ha s hs
    (by simpa only [hs0] using hu) N (by simpa only [hs0, hsN] using hshort)
    w hc η hη.le hosc
  rw [hs0, hsN] at hb
  apply hb.trans
  have hvar := mul_le_mul_of_nonneg_right (hV s hs N hs0 hsN) hE
  have hsmall : η * M ≤ ε := by
    have hid : η * (M + 1) = ε := by dsimp [η]; field_simp
    nlinarith
  exact add_le_add hvar hsmall

end Ostmann

end OAI
