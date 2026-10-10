import OAI.Combinatorics.BalancedRyser.Probability.PatternCenteredAssembly
import OAI.Combinatorics.BalancedRyser.Probability.PatternSupportCompatibility
import OAI.Combinatorics.BalancedRyser.Probability.PatternWeightExtensions

namespace OAI

open scoped BigOperators

namespace Balanced.PatternModel

theorem centered_moment_le_of_exposure_bounds
    (P : PatternModel) (K₀ : Finset P.Color) (x : P.Sample)
    (r s : ℕ) (q Cf Ct : ℝ) (hq : 1 ≤ q) (hCf : 0 ≤ Cf) (hCt : 0 ≤ Ct)
    (hsupport : ∀ a, (P.support a).card ≤ r)
    (htotal : ∀ K : Finset P.Color, K.card ≤ (2 * s) * r → ∀ y,
      P.fixedExpectation (K₀ ∪ K) y P.count ≤ Cf * q)
    (hoverlap : ∀ K : Finset P.Color, K.card ≤ (2 * s) * r → ∀ y,
      P.fixedExpectation (K₀ ∪ K) y (P.overlapCount K₀ K) ≤ Ct) :
    P.fixedExpectation K₀ x
      (fun ω => |P.count ω - P.fixedExpectation K₀ x P.count| ^ (2 * s)) ≤
        ((2 * s).factorial : ℝ) * 2 ^ (2 * s) *
          (2 * max Cf Ct) ^ (2 * s) * q ^ s := by
  classical
  apply PatternModelMoments.centered_moment_bound_of_productWeight_costs
    P K₀ x s q (2 * max Cf Ct) hq (by positivity)
  · intro pre hpre
    have hK : (P.additionalSupport K₀ pre).card ≤ (2 * s) * r :=
      (P.additionalSupport_card_le K₀ pre r hsupport).trans
        (Nat.mul_le_mul_right r (by omega))
    have h := P.productWeight_free_extension_le K₀ x pre (Cf * q)
      (mul_nonneg hCf (by linarith)) (htotal _ hK)
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (P.productWeight_nonneg K₀ x pre)
    calc
      2 * (Cf * q) = (2 * Cf) * q := by ring
      _ ≤ (2 * max Cf Ct) * q := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (le_max_left Cf Ct) (by norm_num)) (by linarith)
  · intro pre hpre
    have hK : (P.additionalSupport K₀ pre).card ≤ (2 * s) * r :=
      (P.additionalSupport_card_le K₀ pre r hsupport).trans
        (Nat.mul_le_mul_right r (by omega))
    have h := P.productWeight_overlap_extension_le K₀ x pre Ct hCt (hoverlap _ hK)
    have heq :
        (∑ a, if PatternMoments.supportOverlap P.support K₀ pre a then
          P.productWeight K₀ x (a :: pre) else 0) =
        (∑ a, if Disjoint (P.support a \ K₀) (P.additionalSupport K₀ pre) then
          0 else P.productWeight K₀ x (a :: pre)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [P.additionalSupport_eq_freshPrefixSupport]
      unfold PatternMoments.supportOverlap PatternModel.freshPrefixSupport
      split_ifs <;> simp_all
    rw [heq]
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_max_right Cf Ct) (by norm_num))
      (P.productWeight_nonneg K₀ x pre))

end Balanced.PatternModel

namespace Balanced.PatternFamilies

universe u v

theorem uniform_raw_moments_of_exposure_bounds
    (I : ℕ → Type v) (P : ∀ q, I q → PatternModel.{u})
    (K₀ : ∀ q i, Finset (P q i).Color)
    (hsupport : ∃ r : ℕ, ∀ q i a, ((P q i).support a).card ≤ r)
    (htotal : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q, q₀ ≤ q → ∀ i, ∀ K : Finset (P q i).Color, K.card ≤ m →
        ∀ x, (P q i).fixedExpectation (K₀ q i ∪ K) x (P q i).count ≤ C) :
    ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q, q₀ ≤ q → ∀ i x,
        (P q i).fixedExpectation (K₀ q i) x (fun ω => (P q i).count ω ^ s) ≤ C := by
  obtain ⟨r, hr⟩ := hsupport
  intro s _hs
  obtain ⟨C, hC, q₀, hc⟩ := htotal ((s - 1) * r)
  refine ⟨C ^ s, pow_pos hC s, q₀, ?_⟩
  intro q hq i x
  exact (P q i).fixed_moment_le_pow (K₀ q i) x r s C hC.le (hr q i)
    (hc q hq i)

theorem uniform_centered_moments_of_exposure_bounds
    (I : ℕ → Type v) (P : ∀ q, I q → PatternModel.{u})
    (K₀ : ∀ q i, Finset (P q i).Color)
    (hsupport : ∃ r : ℕ, ∀ q i a, ((P q i).support a).card ≤ r)
    (htotal : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q, q₀ ≤ q → ∀ i, ∀ K : Finset (P q i).Color, K.card ≤ m →
        ∀ x, (P q i).fixedExpectation (K₀ q i ∪ K) x (P q i).count ≤ C * (q : ℝ))
    (hoverlap : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q, q₀ ≤ q → ∀ i, ∀ K : Finset (P q i).Color, K.card ≤ m →
        ∀ x, (P q i).fixedExpectation (K₀ q i ∪ K) x
          ((P q i).overlapCount (K₀ q i) K) ≤ C) :
    ∀ s : ℕ, 0 < s → ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ,
      ∀ q, q₀ ≤ q → ∀ i x,
        (P q i).fixedExpectation (K₀ q i) x
          (fun ω => |(P q i).count ω -
            (P q i).fixedExpectation (K₀ q i) x (P q i).count| ^ (2 * s)) ≤
              C * (q : ℝ) ^ s := by
  obtain ⟨r, hr⟩ := hsupport
  intro s _hs
  obtain ⟨Cf, hCf, qf, hf⟩ := htotal ((2 * s) * r)
  obtain ⟨Ct, hCt, qt, ht⟩ := hoverlap ((2 * s) * r)
  refine ⟨((2 * s).factorial : ℝ) * 2 ^ (2 * s) *
    (2 * max Cf Ct) ^ (2 * s), by positivity, max (max qf qt) 1, ?_⟩
  intro q hq i x
  have hq₁ : (1 : ℝ) ≤ q := by
    exact_mod_cast (le_max_right (max qf qt) 1).trans hq
  exact (P q i).centered_moment_le_of_exposure_bounds (K₀ q i) x r s q Cf Ct
    hq₁ hCf.le hCt.le (hr q i)
    (hf q ((le_max_left qf qt).trans ((le_max_left _ _).trans hq)) i)
    (ht q ((le_max_right qf qt).trans ((le_max_left _ _).trans hq)) i)

end Balanced.PatternFamilies

end OAI
