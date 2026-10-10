import OAI.NumberTheory.Ostmann.Preliminaries.Stability
import OAI.NumberTheory.Ostmann.Construction.OppositeBiasTransfer

namespace OAI

/-! # Collision stability controls every chosen bounded residue test -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def residueTestError (S : Finset ℕ) (μ f : ℕ → ℝ) : ℝ :=
  (∑ r ∈ S, μ r * f r) - residueTestMean S f

theorem residueTestError_eq (S : Finset ℕ) (μ f : ℕ → ℝ) :
    residueTestError S μ f = ∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) * f r := by
  simp only [residueTestError, residueTestMean, sub_mul, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

theorem residueTestError_sq_le (S : Finset ℕ) (μ f : ℕ → ℝ) (p : ℕ)
    (hcard : S.card ≤ p) (hf : ∀ r ∈ S, |f r| ≤ 1) :
    residueTestError S μ f ^ 2 ≤ (p : ℝ) * ∑ r ∈ S, (μ r - 1 / (S.card : ℝ)) ^ 2 := by
  rw [residueTestError_eq]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun r => μ r - 1 / (S.card : ℝ)) f
  have henergy : (∑ r ∈ S, f r ^ 2) ≤ (p : ℝ) := by
    calc
      _ ≤ ∑ _r ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun r hr => by
        have hh := hf r hr
        have ha := abs_nonneg (f r)
        nlinarith [sq_abs (f r)])
      _ = (S.card : ℝ) := by simp
      _ ≤ p := by exact_mod_cast hcard
  have hm := mul_le_mul_of_nonneg_left henergy
    (Finset.sum_nonneg (s := S) (fun r _ => sq_nonneg (μ r - 1 / (S.card : ℝ))))
  exact hCS.trans (by simpa only [mul_comm] using hm)

theorem collisionDefect_controls_tests (p : ℕ) (S T : Finset ℕ) (μ ν f g : ℕ → ℝ)
    (hS : S.Nonempty) (hT : T.Nonempty) (hcard : S.card + T.card ≤ p)
    (hf : ∀ r ∈ S, |f r| ≤ 1) (hg : ∀ r ∈ T, |g r| ≤ 1) :
    residueTestError S μ f ^ 2 + residueTestError T ν g ^ 2 ≤
      (p : ℝ) * collisionDefect p S T μ ν := by
  have hs := residueTestError_sq_le S μ f p (by omega) hf
  have ht := residueTestError_sq_le T ν g p (by omega) hg
  have hgap := four_div_le_inverse_add_inverse
    (by exact_mod_cast hS.card_pos : (0 : ℝ) < S.card)
    (by exact_mod_cast hT.card_pos : (0 : ℝ) < T.card)
    (by exact_mod_cast hcard : (S.card : ℝ) + T.card ≤ p)
  have hpgap := mul_nonneg (Nat.cast_nonneg (α := ℝ) p) (sub_nonneg.mpr hgap)
  unfold collisionDefect
  nlinarith only [hs, ht, hpgap]

/-- The complete weighted collision budget bounds the empirical test errors,
even when each test is chosen independently at its prime. -/
theorem weighted_collision_test_errors (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν f g : ℕ → ℕ → ℝ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card ≤ p)
    (hf : ∀ p ∈ P, ∀ r ∈ S p, |f p r| ≤ 1)
    (hg : ∀ p ∈ P, ∀ r ∈ T p, |g p r| ≤ 1) :
    (∑ p ∈ P, (Real.log (p : ℝ) / p) *
      (residueTestError (S p) (μ p) (f p) ^ 2 + residueTestError (T p) (ν p) (g p) ^ 2)) ≤
    ∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p) := by
  apply Finset.sum_le_sum
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (hP p hp).one_le)
  have hb := collisionDefect_controls_tests p (S p) (T p) (μ p) (ν p) (f p) (g p)
    (hS p hp) (hT p hp) (hcard p hp) (hf p hp) (hg p hp)
  have hd : (residueTestError (S p) (μ p) (f p) ^ 2 +
      residueTestError (T p) (ν p) (g p) ^ 2) / p ≤
      collisionDefect p (S p) (T p) (μ p) (ν p) := by
    apply (div_le_iff₀ hp0).mpr
    simpa only [mul_comm] using hb
  have hh := mul_le_mul_of_nonneg_left hd hlog
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using hh

end Ostmann

end OAI
