import OAI.NumberTheory.TwoPoint.Bounds.ActualPrimeScale
import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinMassTotal

namespace OAI

/-! The retained divisor bins carry at least half the original harmonic
mass, and the exact tuple mass is at least W^J. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical

theorem ModFiveThetaInput.eventually_canonical_retained_mass
    (hprime : ModFiveThetaInput) (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∀ᶠ L : ℝ in atTop, ∀ (_hL : 1 ≤ L) (η : ℝ), 0 < η →
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let V := ∏ j, primeHarmonicMass (P j)
      W ^ J ≤ V ∧
        paddingTiltNormalizer (paddingPrimeSupply E L) * V / 2 ≤
          totalPaddingBinMass (primeTupleDivisors P) (paddingPrimeSupply E L) L η := by
  filter_upwards [hprime.eventually_actual_prime_supplies E W hW,
    hprime.eventually_totalPaddingBinMass E] with L hs hm
  intro hL η hη
  dsimp only
  let J := primeSupplyCount W L
  let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
  have hp : ∀ j, ∀ p ∈ P j, p.Prime := centeredPrimeBands_prime _ _ _ _
  have hd : ∀ j l, l ≠ j → Disjoint (P j) (P l) :=
    centeredPrimeBands_disjoint _ _ _ _ (Real.rpow_nonneg (by linarith) _) (by linarith)
  have hmass (j : Fin J) : W ≤ primeHarmonicMass (P j) := by
    simpa only [primeHarmonicMass_eq_sum, P, centeredPrimeBands] using (hs.2.2 j.val).2.1
  constructor
  · calc
      W ^ J = ∏ _j : Fin J, W := by simp
      _ ≤ _ := prod_le_prod₀ (fun _ _ => by linarith) (fun j _ => hmass j)
  · have ht := (hm (primeTupleDivisors P) η hη (fun d hd =>
        centeredPrimeTuple_log_bound (Real.rpow_pos_of_pos (by linarith) _) hW
          (primeSupplyScale_endpoint W L (by linarith) hL) hd)).1
    rw [primeTupleDivisors_mass P hp hd] at ht
    have he : (∏ j, ∑ p ∈ P j, 1 / (p : ℝ)) = ∏ j, primeHarmonicMass (P j) := by
      simp only [primeHarmonicMass_eq_sum]
    rw [he] at ht
    linarith

end TwoPointCorrelations

end OAI
