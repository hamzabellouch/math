import OAI.NumberTheory.Ostmann.ZeroDensity.PageSelection
import OAI.NumberTheory.Ostmann.ZeroDensity.PrimeLogDensityBounds

namespace OAI

/-! # Uniform prime intervals with one retained Page character

The second error below accounts for local exceptional zeros outside Page's
common region. This derives simultaneous compatibility across moduli from
the published zero uniqueness, rather than assuming compatibility of the
short-interval estimates.
-/

namespace Ostmann

open MeasureTheory

theorem PublishedProgressionInput.uniform_log_interval (P : PublishedProgressionInput)
    {q Q a : ℕ} (hQ : 2 ≤ Q) (hq : 1 ≤ q) (hqQ : q ≤ Q) (ha : a.Coprime q)
    {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) (hshort : t ≤ s + 1) :
    |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
      ∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
        (pageBeta (pageAtModulus q (selectedPageZero P Q))) y| ≤
      18 * P.errorConstant * Real.exp (-P.decay * Real.sqrt s) +
        Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ))) := by
  have hlocal := P.local_log_interval q a hq ha hs hst hshort
  rcases localZero_selected_alternative P hQ hq hqQ with heq | ⟨e, he, hfar, hn⟩
  · rw [heq] at hlocal
    exact hlocal.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
  · have hφ : (1 : ℝ) ≤ Nat.totient q := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
    have hlog : 0 < Real.log (4 * (Q : ℝ)) := by
      apply Real.log_pos
      have : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      linarith
    have hcorr := primeLogDensity_integral_correction_le (Nat.totient q)
      (pageCoefficient (some e) a) e.beta (P.kappa / Real.log (4 * (Q : ℝ)))
      hφ (pageCoefficient_abs_le_one _ _) (div_nonneg P.kappa_pos.le hlog.le)
      hfar.le hs hst hshort
    rw [he] at hlocal
    rw [hn]
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (reciprocalPrimeInterval q a (Real.exp s) (Real.exp t))
      (∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
        (pageCoefficient (some e) a) e.beta y)
      (∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q) 0 1 y)
    simp only [Real.norm_eq_abs] at htri
    have hbound := htri.trans (add_le_add hlocal hcorr)
    have hexp : Real.exp (-(P.kappa / Real.log (4 * (Q : ℝ))) * s) =
        Real.exp (-P.kappa * s / Real.log (4 * (Q : ℝ))) := by
      congr 1
      ring
    rw [hexp] at hbound
    exact hbound

end Ostmann

end OAI
