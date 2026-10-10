import OAI.NumberTheory.Ostmann.ZeroDensity.ProgressionErrorRates

namespace OAI

/-! # Giant and bulk progression rows used in the arithmetic comparison -/

namespace Ostmann

open Filter

inductive ArithmeticProgressionRow
  | giant
  | bulk
  deriving DecidableEq

namespace ArithmeticProgressionRow

noncomputable def leftExponent : ArithmeticProgressionRow → ℝ
  | giant => 49 / 1000
  | bulk => 39 / 10000

noncomputable def modulusExponent : ArithmeticProgressionRow → ℝ
  | giant => 12 / 1000
  | bulk => 12 / 10000

noncomputable def errorExponent : ArithmeticProgressionRow → ℝ
  | giant => 18 / 1000
  | bulk => 16 / 10000

theorem gaps (r : ArithmeticProgressionRow) :
    0 < r.leftExponent ∧ 0 < r.modulusExponent ∧
      r.errorExponent < r.leftExponent / 2 ∧
      r.errorExponent < r.leftExponent - r.modulusExponent ∧
      0 < r.leftExponent - r.modulusExponent := by
  cases r <;> norm_num [leftExponent, modulusExponent, errorExponent]

end ArithmeticProgressionRow

/-- Exactly the two rows of the manuscript's progression table, with one
exceptional character for all moduli in the row. The logarithmic interval
estimate is proved from the published theta and Page inputs. -/
theorem PublishedProgressionInput.row_log_interval (P : PublishedProgressionInput)
    (r : ArithmeticProgressionRow) :
    ∀ᶠ L : ℝ in atTop, ∀ (q Q a : ℕ), 2 ≤ Q → 1 ≤ q → q ≤ Q → a.Coprime q →
      Real.log (Q : ℝ) ≤ Real.exp (r.modulusExponent * L) →
      ∀ s t : ℝ, 1 ≤ s → Real.exp (r.leftExponent * L) ≤ s → s ≤ t → t ≤ s + 1 →
      |reciprocalPrimeInterval q a (Real.exp s) (Real.exp t) -
        ∫ y in Set.Ioc s t, primeLogDensity (Nat.totient q)
          (pageCoefficient (pageAtModulus q (selectedPageZero P Q)) a)
          (pageBeta (pageAtModulus q (selectedPageZero P Q))) y| ≤
        2 * Real.exp (-Real.exp (r.errorExponent * L)) := by
  obtain ⟨ha, hμ, hδa, hδμ, haμ⟩ := r.gaps
  filter_upwards [P.log_interval_rate r.leftExponent r.modulusExponent r.errorExponent
      ha hδa hδμ haμ,
    eventually_ge_atTop (Real.log 4 / r.modulusExponent)] with L hL hLlarge
  intro q Q a hQ hq hqQ hcop hlog
  apply hL q Q a hQ hq hqQ hcop
  have hQ0 : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hQ0]
  have hm : Real.log 4 ≤ r.modulusExponent * L := by
    have h := (div_le_iff₀ hμ).mp hLlarge
    nlinarith
  have he := Real.add_one_le_exp (r.modulusExponent * L)
  linarith

end Ostmann

end OAI
