import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace OAI

/-!
# Finite spectral resolvents

The finite-alphabet arguments in Sections 3 and 5 of the manuscript use
the unique solution of `∑ a, ρ a / (b - eig a) = x` above all eigenvalues.
The solution is unique and satisfies deterministic bounds.
The weights may vanish; their sum being one is the only normalization.
-/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- The Cauchy transform of a finite spectral probability law. -/
def finiteResolvent (ρ eig : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ a, ρ a / (b - eig a)

/-- The second resolvent moment, which controls the derivative of the inverse. -/
def finiteSecondResolvent (ρ eig : ι → ℝ) (b : ℝ) : ℝ :=
  ∑ a, ρ a / (b - eig a) ^ 2

theorem exists_pos_spectral_weight {ρ : ι → ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1) :
    ∃ a, 0 < ρ a := by
  by_contra h
  push Not at h
  have hz : ∑ a, ρ a = 0 := Finset.sum_eq_zero fun a _ =>
    le_antisymm (h a) (hρ a)
  linarith

theorem finiteResolvent_pos {ρ eig : ι → ℝ} {b : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hb : ∀ a, eig a < b) :
    0 < finiteResolvent ρ eig b := by
  obtain ⟨a, ha⟩ := exists_pos_spectral_weight hρ hρsum
  unfold finiteResolvent
  exact Finset.sum_pos' (fun a _ => div_nonneg (hρ a) (sub_pos.mpr (hb a)).le)
    ⟨a, Finset.mem_univ a, div_pos ha (sub_pos.mpr (hb a))⟩

theorem finiteResolvent_strictAnti {ρ eig : ι → ℝ} {b c : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hb : ∀ a, eig a < b) (hbc : b < c) :
    finiteResolvent ρ eig c < finiteResolvent ρ eig b := by
  obtain ⟨a, ha⟩ := exists_pos_spectral_weight hρ hρsum
  apply Finset.sum_lt_sum
  · intro j _
    exact div_le_div_of_nonneg_left (hρ j) (sub_pos.mpr (hb j)) (by linarith)
  · exact ⟨a, Finset.mem_univ a,
      div_lt_div_of_pos_left ha (sub_pos.mpr (hb a)) (by linarith)⟩

/-- The finite-alphabet inverse is unique on its required branch. -/
theorem finiteResolvent_solution_unique {ρ eig : ι → ℝ} {b c x : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hb : ∀ a, eig a < b) (hc : ∀ a, eig a < c)
    (hbx : finiteResolvent ρ eig b = x) (hcx : finiteResolvent ρ eig c = x) :
    b = c := by
  rcases lt_trichotomy b c with h | h | h
  · have := finiteResolvent_strictAnti hρ hρsum hb h
    linarith
  · exact h
  · have := finiteResolvent_strictAnti hρ hρsum hc h
    linarith

theorem finiteResolvent_le {ρ eig : ι → ℝ} {b u : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (heig : ∀ a, eig a ≤ u) (hb : u < b) :
    finiteResolvent ρ eig b ≤ 1 / (b - u) := by
  calc
    finiteResolvent ρ eig b ≤ ∑ a, ρ a / (b - u) := by
      apply Finset.sum_le_sum
      intro a _
      exact div_le_div_of_nonneg_left (hρ a) (sub_pos.mpr hb) (by linarith [heig a])
    _ = 1 / (b - u) := by rw [← Finset.sum_div, hρsum]

theorem le_finiteResolvent {ρ eig : ι → ℝ} {b l : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (heig : ∀ a, l ≤ eig a) (hb : ∀ a, eig a < b) :
    1 / (b - l) ≤ finiteResolvent ρ eig b := by
  calc
    1 / (b - l) = ∑ a, ρ a / (b - l) := by rw [← Finset.sum_div, hρsum]
    _ ≤ finiteResolvent ρ eig b := by
      apply Finset.sum_le_sum
      intro a _
      exact div_le_div_of_nonneg_left (hρ a) (sub_pos.mpr (hb a)) (by linarith [heig a])

/-- Section 6's bound for the uncapped inverse transform. -/
theorem finiteR_bounds {ρ eig : ι → ℝ} {b x l u : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1)
    (hl : ∀ a, l ≤ eig a) (hu : ∀ a, eig a ≤ u)
    (hb : u < b) (hx : 0 < x) (hbx : finiteResolvent ρ eig b = x) :
    l ≤ b - 1 / x ∧ b - 1 / x ≤ u := by
  have hbeig : ∀ a, eig a < b := fun a => lt_of_le_of_lt (hu a) hb
  have hupper := finiteResolvent_le hρ hρsum hu hb
  have hlower := le_finiteResolvent hρ hρsum hl hbeig
  rw [hbx] at hupper hlower
  obtain ⟨a, _⟩ := exists_pos_spectral_weight hρ hρsum
  have hbl : 0 < b - l := by linarith [hl a, hbeig a]
  have hbu : 0 < b - u := sub_pos.mpr hb
  have hbux : (b - u) * x ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ hbu).mp hupper
  have hblx : 1 ≤ (b - l) * x := by
    simpa only [mul_comm] using (div_le_iff₀ hbl).mp hlower
  constructor
  · have : 1 / x ≤ b - l := (div_le_iff₀ hx).mpr hblx
    linarith
  · have : b - u ≤ 1 / x := (le_div_iff₀ hx).mpr hbux
    linarith

theorem finiteResolvent_translate (ρ eig : ι → ℝ) (b c : ℝ) :
    finiteResolvent ρ (fun a => eig a + c) (b + c) = finiteResolvent ρ eig b := by
  unfold finiteResolvent
  congr 1
  ext a
  congr 1
  ring

/-- The transform of a point mass is the constant equal to its atom. -/
theorem finiteResolvent_constant {ρ : ι → ℝ} (hρsum : ∑ a, ρ a = 1)
    (b c : ℝ) :
    finiteResolvent ρ (fun _ => c) b = 1 / (b - c) := by
  unfold finiteResolvent
  rw [← Finset.sum_div, hρsum]

theorem constant_spectrum_solution {ρ : ι → ℝ}
    (hρsum : ∑ a, ρ a = 1) {x c : ℝ} (hx : 0 < x) :
    finiteResolvent ρ (fun _ => c) (c + 1 / x) = x := by
  rw [finiteResolvent_constant hρsum]
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

theorem finiteResolvent_sq_le_second {ρ eig : ι → ℝ} {b : ℝ}
    (hρ : ∀ a, 0 ≤ ρ a) (hρsum : ∑ a, ρ a = 1) :
    finiteResolvent ρ eig b ^ 2 ≤ finiteSecondResolvent ρ eig b := by
  let r := finiteResolvent ρ eig b
  have hnonneg : 0 ≤ ∑ a, ρ a * (1 / (b - eig a) - r) ^ 2 := by
    exact Finset.sum_nonneg fun a _ => mul_nonneg (hρ a) (sq_nonneg _)
  have hexpand :
      (∑ a, ρ a * (1 / (b - eig a) - r) ^ 2) =
        finiteSecondResolvent ρ eig b - 2 * r * finiteResolvent ρ eig b + r ^ 2 := by
    calc
      _ = ∑ a, (ρ a / (b - eig a) ^ 2 -
          2 * r * (ρ a / (b - eig a)) + r ^ 2 * ρ a) := by
        apply Finset.sum_congr rfl
        intro a _
        simp only [div_eq_mul_inv, ← inv_pow]
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, hρsum, mul_one, finiteSecondResolvent, finiteResolvent]
  rw [hexpand] at hnonneg
  dsimp [r] at hnonneg
  nlinarith

end InvariantIsing

end

end OAI
