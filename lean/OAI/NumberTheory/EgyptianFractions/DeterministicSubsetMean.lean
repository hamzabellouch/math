import OAI.NumberTheory.EgyptianFractions.DeterministicMeanBound
import OAI.NumberTheory.EgyptianFractions.ResidueDenominator

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

/-- All entries of the canonical deterministic binary block have the right
size for the high-level reciprocal-phase theorem. -/
theorem subsetEntry_le_exp_of_power_pool {S : ℝ} (hS : 1 < S)
    {m : ℕ} (hm : (m : ℝ) ≤ S / Real.log S) (p : Fin m → ℕ)
    (hp : ∀ j, (p j).Prime) (hsize : ∀ j, (p j : ℝ) ≤ S ^ (101 : ℕ))
    (I : Fin m → Fin 2) :
    (ResidueConstruction.subsetEntry p I : ℝ) ≤ Real.exp (101 * S) := by
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hSpos : 0 < S := by linarith
  have hp0 : ∀ j, 0 < p j := fun j => (hp j).pos
  have hlogs : ∀ j, Real.log (p j : ℝ) ≤ 101 * Real.log S := by
    intro j
    have hj : (0 : ℝ) < p j := by exact_mod_cast hp0 j
    have hh := Real.log_le_log hj (hsize j)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hbound := ResidueConstruction.log_subsetEntry_le p hp0 I
    (101 * Real.log S) (by positivity) hlogs
  have hmS : (m : ℝ) * Real.log S ≤ S := (le_div_iff₀ hlog).mp hm
  have hentry : (0 : ℝ) < ResidueConstruction.subsetEntry p I := by
    exact_mod_cast ResidueConstruction.subsetEntry_pos p hp0 I
  apply (Real.log_le_iff_le_exp hentry).mp
  nlinarith

/-- The unconditional deterministic second moment specialized to the actual
prime-subset block. Its exact `2^m` normalization and distinctness are proved,
rather than left as hypotheses for the residue-family assembler. -/
theorem deterministic_subset_mean_two_errors (D : ℝ) (hD : 255 ≤ D) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
      ∀ᶠ S : ℝ in atTop, ∀ (m : ℕ) (X C ell : ℝ),
        (m : ℝ) ≤ S / Real.log S →
        Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
        Real.exp (D * S) ≤ C → C ≤ Real.exp (2 * D * S) →
        1 ≤ ell → ell ≤ Real.exp ((m : ℝ) / 2500) →
        ∀ p : Fin m → ℕ, (∀ j, (p j).Prime) → Function.Injective p →
          (∀ j, (p j : ℝ) ≤ S ^ (101 : ℕ)) →
          (∑ u ∈ Finset.Icc (⌊Real.exp (-(m : ℝ) / 10000) * X⌋₊ + 1) ⌊X⌋₊,
            ‖(∑ I : Fin m → Fin 2,
                differencingPhase (ell * C * (ResidueConstruction.subsetEntry p I : ℝ) /
                  (u : ℝ))) / (2 : ℂ) ^ m‖ ^ 2) ≤
            X * (Real.exp (-Real.log 2 * (m : ℝ)) + A * Real.exp (-c * S)) := by
  obtain ⟨A, c, hA, hc, hmean⟩ := deterministic_mean_two_errors D hD
  refine ⟨A, c, hA, hc, ?_⟩
  filter_upwards [hmean, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with S hmean hS hlog
  intro m X C ell hm hXlo hXhi hClo hChi hell hellhi p hp hinj hsize
  have hmS : (m : ℝ) ≤ S := by
    have hm' := (le_div_iff₀ (Real.log_pos hS)).mp hm
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hcard : Real.exp (Real.log 2 * (m : ℝ)) ≤
      ((Finset.univ : Finset (Fin m → Fin 2)).card : ℝ) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    simp
  have hh := hmean m X C ell hmS hXlo hXhi hClo hChi hell hellhi
    (Finset.univ : Finset (Fin m → Fin 2)) (ResidueConstruction.subsetEntry p)
    (ResidueConstruction.subsetEntry_injective p hp hinj).injOn hcard
    (fun I _ => subsetEntry_le_exp_of_power_pool hS hm p hp hsize I)
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] using hh

/-- The high-level deterministic moment estimate for the actual binary
prime-product block, with the manuscript's final exponential rate. -/
theorem eventually_deterministic_subset_mean (D : ℝ) (hD : 255 ≤ D) :
    ∀ᶠ S : ℝ in atTop, ∀ (m : ℕ) (X C ell : ℝ),
      S / (2 * Real.log S) ≤ (m : ℝ) → (m : ℝ) ≤ S / Real.log S →
      Real.exp S ≤ X → X ≤ Real.exp (D * S / 4) →
      Real.exp (D * S) ≤ C → C ≤ Real.exp (2 * D * S) →
      1 ≤ ell → ell ≤ Real.exp ((m : ℝ) / 2500) →
      ∀ p : Fin m → ℕ, (∀ j, (p j).Prime) → Function.Injective p →
        (∀ j, (p j : ℝ) ≤ S ^ (101 : ℕ)) →
        (∑ u ∈ Finset.Icc (⌊Real.exp (-(m : ℝ) / 10000) * X⌋₊ + 1) ⌊X⌋₊,
          ‖(∑ I : Fin m → Fin 2,
              differencingPhase (ell * C * (ResidueConstruction.subsetEntry p I : ℝ) /
                (u : ℝ))) / (2 : ℂ) ^ m‖ ^ 2) ≤
          X * Real.exp (-(m : ℝ) / 100) := by
  filter_upwards [deterministic_mean_bound D hD, eventually_gt_atTop (1 : ℝ)]
    with S hmean hS
  intro m X C ell hmlo hmhi hXlo hXhi hClo hChi hell hellhi p hp hinj hsize
  have hcard : Real.exp (Real.log 2 * (m : ℝ)) ≤
      ((Finset.univ : Finset (Fin m → Fin 2)).card : ℝ) := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    simp
  have hh := hmean m X C ell hmlo hmhi hXlo hXhi hClo hChi hell hellhi
    (Finset.univ : Finset (Fin m → Fin 2)) (ResidueConstruction.subsetEntry p)
    (ResidueConstruction.subsetEntry_injective p hp hinj).injOn hcard
    (fun I _ => subsetEntry_le_exp_of_power_pool hS hmhi p hp hsize I)
  simpa only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat] using hh

end Problem337

end

end OAI
