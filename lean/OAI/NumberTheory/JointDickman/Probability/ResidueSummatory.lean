import OAI.NumberTheory.JointDickman.Analysis.CharacterResidues

namespace OAI

/-! # The uniform progression estimate for rough squarefree integers -/

namespace JointDickman

open Finset Filter
open scoped Topology

noncomputable def roughResidueSummatory {q : ℕ} (r : ZMod q)
    (E : Finset ℕ) (z Y : ℝ) : ℝ :=
  progressionSum (Ioc 0 ⌊Y⌋₊) (roughSquarefreeWeight E z) r

theorem auxiliary_modulus_le_cutoff {B q : ℕ} (hB : 1 ≤ B)
    (hq : (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ)) : q ≤ auxiliaryCutoff B := by
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hcut : (auxiliaryCutoff B : ℝ) = (B : ℝ) ^ (1000 : ℝ) := by
    norm_num [auxiliaryCutoff]
  have hle := hq.trans (Real.rpow_le_rpow_of_exponent_le hB1 (by norm_num : (100 : ℝ) ≤ 1000))
  rw [← hcut] at hle
  exact_mod_cast hle

/-- Equidistribution in the unit classes, before partial summation. -/
theorem roughResidueSummatory_error
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
      (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
      ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
      ∀ r : (ZMod q)ˣ,
      |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient| ≤
        K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨K, hK, hbound⟩ := moving_rough_character_bound hSW hM hz hD
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with B hboundB hB
  intro Y hY hY9 q _ hq r
  have hqP := auxiliary_modulus_le_cutoff hB hq
  exact progressionSum_error_le (Ioc 0 ⌊Y⌋₊)
    (roughSquarefreeWeight (Nat.primesLE (auxiliaryCutoff B)) z) r (by positivity)
    (fun n _ hn => (ZMod.isUnit_iff_coprime n q).mpr
      (roughSquarefreeWeight_coprime (NeZero.ne q) hqP z hn))
    (fun χ hχ => hboundB Y hY hY9 q hq χ hχ)

/-- The same actual coefficients as the untwisted expansion serve in
all unit progressions; the error is uniform in every modulus up to `B^100`. -/
theorem roughResidueSummatory_expansion
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hSW : PublishedInputs.SquarefreeCharacterEstimateInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {z D : ℝ}
    (hz : z = 1 / 4 ∨ z = 1 / 2) (hD : 0 ≤ D) :
    ∃ c : ℕ → ℝ, c 0 = squarefreeLeadingConstant z ∧ 0 < c 0 ∧
      ∃ H : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ B : ℕ in atTop, ∀ Y : ℝ,
        (B : ℝ) ^ (89 / 100 : ℝ) ≤ Real.log Y → 9 ≤ Y →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ (B : ℝ) ^ (100 : ℝ) →
        ∀ r : (ZMod q)ˣ,
        |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
          (Y * ∑ ν ∈ range (H + 1),
            roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν *
              (Real.log Y) ^ (z - 1 - ν)) / q.totient| ≤
          K * Y * (B : ℝ) ^ (-D) := by
  obtain ⟨c, hc0, hcpos, H, K, hK, hbound⟩ := moving_rough_auxiliary_expansion hSD hM hz D
  obtain ⟨K', hK', hres⟩ := roughResidueSummatory_error hSW hM hz hD
  refine ⟨c, hc0, hcpos, H, K + K', add_nonneg hK hK', ?_⟩
  filter_upwards [hbound, hres] with B hboundB hresB
  intro Y hY hY9 q _ hq r
  have hφ : (1 : ℝ) ≤ q.totient := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q))
  have hφ0 : (0 : ℝ) < q.totient := by linarith
  have hu := hboundB Y hY hY9
  have hr := hresB Y hY hY9 q hq r
  let T := Y * ∑ ν ∈ range (H + 1),
    roughCoefficient c (Nat.primesLE (auxiliaryCutoff B)) z ν * (Real.log Y) ^ (z - 1 - ν)
  have hdiv : |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient -
      T / q.totient| ≤ K * Y * (B : ℝ) ^ (-D) := by
    rw [← sub_div, abs_div, abs_of_pos hφ0]
    exact (div_le_self (abs_nonneg _) hφ).trans hu
  calc
    _ ≤ |roughResidueSummatory (r : ZMod q) (Nat.primesLE (auxiliaryCutoff B)) z Y -
        roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient| +
        |roughSquarefreeSummatory (Nat.primesLE (auxiliaryCutoff B)) z Y / q.totient -
          T / q.totient| := abs_sub_le _ _ _
    _ ≤ K' * Y * (B : ℝ) ^ (-D) + K * Y * (B : ℝ) ^ (-D) := add_le_add hr hdiv
    _ = _ := by ring

end JointDickman

end OAI
