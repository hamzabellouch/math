import OAI.NumberTheory.EgyptianFractions.CompositeBadDensityBound
import OAI.NumberTheory.EgyptianFractions.EightProductRationalSupply
import OAI.NumberTheory.EgyptianFractions.CubeFreeSupplyFromExceptions
import OAI.NumberTheory.EgyptianFractions.CompositeMarkedReduction

namespace OAI
noncomputable section
open Filter

namespace Problem337.CompositeSupply

/-- Absence of global bad conductors gives the actual eight-term rational
representation in the ambient divisor pool. -/
lemma rational_divisor_sum_of_no_bad_divisor {Y q : ℕ}
    (hq : 0 < q) (hqY : q ≤ Y) (hc : q.Coprime (base Y))
    (hgood : ∀ d : ℕ, 2 ≤ d → d ∣ q → ¬ BadModulus d) :
    HasRationalDivisorSum (base Y ^ 2) (q : ℚ) 8 := by
  let : NeZero q := ⟨hq.ne'⟩
  apply rational_divisor_sum_eight_of_divisor_collision (base_pos Y).ne'
  intro d hd hdq
  let : NeZero d := ⟨by omega⟩
  rw [CompositeSpectral.remainderCollisionCount_eq_cast, indexed_divisor_collision_eq]
  exact ambient_collisions_le_of_not_bad hq hqY hdq hc.symm (hgood d hd hdq) hd

/-- The entire remaining arithmetic input is the density bound for the
specified global bad-divisor multiples. -/
theorem eventually_supply_of_bad_multiples
    (hbad : ∀ᶠ Y : ℕ in atTop,
      ((badCoprimeDivisorMultiples Y (base Y) (fun d => ¬ BadModulus d)).card : ℝ)
        < (Y : ℝ) / 12) :
    ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (multiplier m) 16 := by
  have hpow : Tendsto (fun m : ℕ => m ^ 4) atTop atTop :=
    tendsto_pow_atTop (by norm_num : 4 ≠ 0)
  filter_upwards [hpow.eventually hbad] with m hm
  exact marked_rational_supply_of_cube_free_bad_divisors m (base (m ^ 4)) 8
    (fun d => ¬ BadModulus d) (base_pos _) hm
    (fun q hq hqY hc hgood => rational_divisor_sum_of_no_bad_divisor hq hqY hc hgood)

/-- The finite exception set used by cube-free density is contained in the
single global logarithmic-tail exception set. -/
lemma badCoprimeDivisorMultiples_subset_badMultiples (Y : ℕ) :
    badCoprimeDivisorMultiples Y (base Y) (fun d => ¬ BadModulus d) ⊆
      badMultiples Y := by
  intro n hn
  obtain ⟨hn1, hnY, d, hd, hdn, hc, hbad⟩ :=
    mem_badCoprimeDivisorMultiples.mp hn
  by_contra hne
  exact hbad (not_bad_of_not_mem_badMultiples hn1 hnY hdn hc.symm hne (dvd_refl d) hd)

/-- Vanishing density of the actual global exceptional set suffices, with
strict margin between one twenty-fourth and one twelfth. -/
theorem eventually_supply_of_badMultiples_small
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ Y : ℕ in atTop,
      ((badMultiples Y).card : ℝ) ≤ ε * Y) :
    ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (multiplier m) 16 := by
  apply eventually_supply_of_bad_multiples
  filter_upwards [hsmall (1 / 24) (by norm_num), eventually_ge_atTop (1 : ℕ)]
    with Y hY hYpos
  have hcard :
      ((badCoprimeDivisorMultiples Y (base Y) (fun d => ¬ BadModulus d)).card : ℝ) ≤
        (badMultiples Y).card := by
    exact_mod_cast Finset.card_le_card (badCoprimeDivisorMultiples_subset_badMultiples Y)
  have hpos : (0 : ℝ) < Y := by exact_mod_cast hYpos
  linarith

/-- Unconditional sixteen-term supply for the explicit fourth-power prefix
multiplier. Every arithmetic density and energy obligation is discharged. -/
theorem eventually_hasRationalDivisorSupply :
    ∀ᶠ m : ℕ in atTop, HasRationalDivisorSupply m (multiplier m) 16 :=
  eventually_supply_of_badMultiples_small eventually_badMultiples_card_le

/-- The exact marked Egyptian-fraction theorem, proved by the composite
cube-free route without any prime-triple distribution premise. -/
theorem quantitative_marked_length :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, 2 ≤ M ∧
      ∀ m : ℕ, M ≤ m → ∃ k : ℕ, ∃ n : Fin k → ℕ,
        IsOneExpansion n ∧ (∃ i, n i = m) ∧
        (k : ℝ) ≤ (257 / Real.log 2 + ε) * Real.log (Real.log (m : ℝ)) :=
  quantitative_marked_length_of_supply eventually_hasRationalDivisorSupply

end Problem337.CompositeSupply

end

end OAI
