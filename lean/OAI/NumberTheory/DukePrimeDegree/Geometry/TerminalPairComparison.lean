import OAI.NumberTheory.DukePrimeDegree.Dynamics.FixedTerminalShearing
import OAI.NumberTheory.DukePrimeDegree.Dynamics.TerminalGenericWindows

namespace OAI

/-!
# Comparing two generic terminal windows

This is the finite-test form of the shearing contradiction. Uniform
closeness of the paired paths and two generic average estimates bound
the actual measure-invariance defect. Neither path is assumed to stay
in a compact set.
-/

noncomputable section
open MeasureTheory Set

namespace DukePrimeDegree
open PrimeDegreePackets

lemma normalized_interval_average_sub_bound
    (F G : ℝ → ℝ) (a b ε : ℝ) (hab : a < b)
    (hF : IntervalIntegrable F volume a b)
    (hG : IntervalIntegrable G volume a b)
    (hclose : ∀ t ∈ Icc a b, |F t - G t| ≤ ε) :
    |(b - a)⁻¹ * (∫ t in a..b, F t) -
      (b - a)⁻¹ * (∫ t in a..b, G t)| ≤ ε := by
  have hpos : 0 < b - a := sub_pos.mpr hab
  rw [← mul_sub, ← intervalIntegral.integral_sub hF hG,
    abs_mul, abs_of_pos (inv_pos.mpr hpos)]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => F t - G t) (a := a) (b := b) (C := ε)
    (fun t ht => by
      rw [uIoc_of_le hab.le] at ht
      simpa only [Real.norm_eq_abs] using hclose t ⟨ht.1.le, ht.2⟩)
  have hbnd : |∫ t in a..b, F t - G t| ≤ ε * (b - a) := by
    simpa only [Real.norm_eq_abs, abs_of_pos hpos] using hnorm
  calc
    _ ≤ (b - a)⁻¹ * (ε * (b - a)) :=
      mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr hpos.le)
    _ = ε := by field_simp

lemma abs_sub_le_three_errors (a b c d ε : ℝ)
    (hab : |a - b| ≤ ε) (hbc : |b - c| ≤ ε) (hcd : |c - d| ≤ ε) :
    |a - d| ≤ 3 * ε := by
  calc
    |a - d| ≤ |a - b| + |b - d| := abs_sub_le a b d
    _ ≤ |a - b| + (|b - c| + |c - d|) :=
      add_le_add (le_refl _) (abs_sub_le b c d)
    _ ≤ ε + (ε + ε) := add_le_add hab (add_le_add hbc hcd)
    _ = 3 * ε := by ring

theorem terminal_pair_invarianceDefect_bound {n : ℕ}
    (μ : Measure (X n))
    (f : CompactlySupportedContinuousMap (X n) ℝ) (h : G n)
    (p q : ℝ → X n) (hp : Continuous p) (hq : Continuous q)
    (δ T ε : ℝ) (hδ : 0 < δ) (hT : 0 < T)
    (hleft : |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
      f (rightAction (p t) h)) - ∫ x, f (rightAction x h) ∂μ| ≤ ε)
    (hright : |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T, f (q t)) -
      ∫ x, f x ∂μ| ≤ ε)
    (hclose : ∀ t ∈ Icc ((1 - δ) * T) T,
      |f (rightAction (p t) h) - f (q t)| ≤ ε) :
    |invarianceDefect μ f h| ≤ 3 * ε := by
  have hab : (1 - δ) * T < T := by nlinarith
  have hF := ((f.continuous.comp (continuous_rightAction h)).comp hp).intervalIntegrable
    (μ := volume)
    ((1 - δ) * T) T
  have hG := (f.continuous.comp hq).intervalIntegrable (μ := volume) ((1 - δ) * T) T
  have hmiddle := normalized_interval_average_sub_bound
    (fun t => f (rightAction (p t) h)) (fun t => f (q t))
    ((1 - δ) * T) T ε hab hF hG hclose
  have hlength : T - (1 - δ) * T = δ * T := by ring
  rw [hlength] at hmiddle
  exact abs_sub_le_three_errors _ _ _ _ ε
    (by simpa only [abs_sub_comm] using hleft) hmiddle hright

/-- A test separating a compact transverse shell contradicts paired
genericity at error one quarter of that separation. -/
theorem no_terminal_pair_with_separated_defect {n : ℕ}
    (μ : Measure (X n))
    (f : CompactlySupportedContinuousMap (X n) ℝ) (h : G n)
    (p q : ℝ → X n) (hp : Continuous p) (hq : Continuous q)
    (δ T ε : ℝ) (hδ : 0 < δ) (hT : 0 < T) (hε : 0 < ε)
    (hsep : ε < |invarianceDefect μ f h|)
    (hleft : |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
      f (rightAction (p t) h)) - ∫ x, f (rightAction x h) ∂μ| ≤ ε / 4)
    (hright : |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T, f (q t)) -
      ∫ x, f x ∂μ| ≤ ε / 4)
    (hclose : ∀ t ∈ Icc ((1 - δ) * T) T,
      |f (rightAction (p t) h) - f (q t)| ≤ ε / 4) : False := by
  have hbound := terminal_pair_invarianceDefect_bound μ f h p q hp hq
    δ T (ε / 4) hδ hT hleft hright hclose
  linarith

end DukePrimeDegree

end

end OAI
