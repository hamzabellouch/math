import OAI.NumberTheory.Ostmann.Arithmetic.MovingReducedCRT

namespace OAI

/-! # The retained Page term in the actual regular-prime average -/

namespace Ostmann
open scoped Classical BigOperators

/-- The deletion prescribed before the nongiant priors prevents an exceptional
conductor from using any prime in the regular block, including its powers. -/
theorem pageAtModulus_regular_factor (z : Option PrimitiveRealZero) (C R T : ℕ)
    (hC : ∀ p, p.Prime → p ∣ C → T ≤ p)
    (hexcluded : ∀ e, z = some e → ∀ p,
      deletedConductorPrime e.modulus T = some p → ¬p ∣ C * R) :
    pageAtModulus (C * R) z = pageAtModulus R z := by
  cases z with
  | none => rfl
  | some e =>
    by_cases hd : e.modulus ∣ C * R
    · have hr : e.modulus ∣ R := by
        by_cases hlarge : ∃ p, p.Prime ∧ p ∣ e.modulus ∧ T ≤ p
        · have hp : deletedConductorPrime e.modulus T = some hlarge.choose := by
            simp [deletedConductorPrime, hlarge]
          exact False.elim (hexcluded e rfl _ hp (hlarge.choose_spec.2.1.trans hd))
        · have hc : e.modulus.Coprime C := Nat.coprime_of_dvd fun p hp hpe hpc =>
            hlarge ⟨p, hp, hpe, hC p hp hpc⟩
          exact hc.dvd_of_dvd_mul_left hd
      simp [pageAtModulus, hd, hr]
    · have hr : ¬ e.modulus ∣ R := fun h => hd (dvd_mul_of_dvd_right h C)
      simp [pageAtModulus, hd, hr]

theorem pageGiantWeight_modEq (P : PublishedProgressionInput) (Q r a b : ℕ)
    (h : Nat.ModEq r a b) (y : ℝ) :
    pageGiantWeight P Q r a y = pageGiantWeight P Q r b y := by
  simp only [pageGiantWeight, pageMultiplier, pageCoefficient_eq_of_modEq _ h]

theorem periodic_coefficient_regular_page_average {I : Type*} [Fintype I] [DecidableEq I]
    (P : PublishedProgressionInput) (Q : ℕ)
    (p : I → ℕ) [∀ i, Fact (p i).Prime] [∀ i, NeZero (p i)] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (r : ℕ) [NeZero r] [NeZero ((∏ i, p i) * r)] (hcop : (∏ i, p i).Coprime r)
    (hpage : pageAtModulus ((∏ i, p i) * r) (selectedPageZero P Q) =
      pageAtModulus r (selectedPageZero P Q))
    (active : I → Bool) (s : ℤ) (other : ∀ i, ZMod (p i))
    (hs : ∀ i, (s : ZMod (p i)) ≠ 0) (ho : ∀ i, other i ≠ 0)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) = p i)
    (C : ℕ → ℕ → ℂ)
    (hC : ∀ a b d e, Nat.ModEq r a d → Nat.ModEq r b e → C a b = C d e) (y : ℝ) :
    correctedMixedPairAverage P Q ((∏ i, p i) * r)
      (fun a b => C a b * (guardedRegularMultiplier p active s other g a b : ℂ)) y =
      ((∏ i, if active i then (1 : ℝ) else 1 - (p i : ℝ)⁻¹ : ℝ) : ℂ) *
        correctedMixedPairAverage P Q r C y := by
  have he := periodic_coefficient_regular_average p hc r hcop active s other hs ho g hg henergy
    (fun a b => C a b * pageGiantWeight P Q r b y)
    (fun a b d e ha hb => by rw [hC a b d e ha hb, pageGiantWeight_modEq P Q r b e hb y])
  change _ = _ at he
  convert he using 1
  · unfold correctedMixedPairAverage
    congr 1
    apply Finset.sum_congr rfl
    intro z _
    simp only [pageGiantWeight, hpage]
    ring
  · rfl

end Ostmann

end OAI
