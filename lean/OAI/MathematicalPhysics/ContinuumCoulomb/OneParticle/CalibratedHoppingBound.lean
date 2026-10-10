import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedHubbard

namespace OAI

/-! Explicit total hopping bounds for actual Coulomb-calibrated contacts. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem calibrated_hopping_sum_bound {Edge : Type*} [Fintype Edge]
    (freq scale τ B : ℝ) (hτ : 0 ≤ τ) (distance K : Edge → ℝ)
    (hK : ∀ e, 0 ≤ K e) (hB : ∀ e, K e ≤ B)
    (hcal : ∀ e, scale * planarHopping (distance e) = coulombHoppingTarget freq τ (K e) (distance e)) :
    4 * ∑ e, |scale * planarHopping (distance e)| ≤
      4 * (Fintype.card Edge : ℝ) * (τ * Real.sqrt (B * localizedCoulombProfile freq 0)) := by
  have hpoint (e : Edge) : |scale * planarHopping (distance e)| ≤
      τ * Real.sqrt (B * localizedCoulombProfile freq 0) := by
    rw [hcal e, coulombHoppingTarget, abs_of_nonneg (mul_nonneg hτ (Real.sqrt_nonneg _))]
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hτ
    calc
      _ ≤ K e * localizedCoulombProfile freq 0 := mul_le_mul_of_nonneg_left
        (sub_le_self _ (localizedCoulombProfile_nonnegative freq (distance e))) (hK e)
      _ ≤ _ := mul_le_mul_of_nonneg_right (hB e) (localizedCoulombProfile_nonnegative freq 0)
  have h := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (s := Finset.univ) (fun e _ => hpoint e)) (by norm_num : (0 : ℝ) ≤ 4)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc] using h

def calibratedTau (freq ε B : ℝ) (r : ℕ) : ℝ :=
  ε * localizedGramConstant freq /
    (4 * ((r : ℝ) + 1) * (Real.sqrt (B * localizedCoulombProfile freq 0) + 1))

theorem calibratedTau_nonnegative {freq ε B : ℝ} (hfreq : 0 < freq) (hε : 0 ≤ ε) (r : ℕ) :
    0 ≤ calibratedTau freq ε B r := by
  unfold calibratedTau
  exact div_nonneg (mul_nonneg hε (localizedGramConstant_positive hfreq).le) (by positivity)

theorem calibratedTau_budget {freq ε B : ℝ} (hfreq : 0 < freq) (hε : 0 ≤ ε) (r : ℕ) :
    4 * (r : ℝ) * (calibratedTau freq ε B r * Real.sqrt (B * localizedCoulombProfile freq 0)) ≤
      ε * localizedGramConstant freq := by
  let q := Real.sqrt (B * localizedCoulombProfile freq 0)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hd : 0 < 4 * ((r : ℝ) + 1) * (q + 1) := by positivity
  have hεc : 0 ≤ ε * localizedGramConstant freq :=
    mul_nonneg hε (localizedGramConstant_positive hfreq).le
  have hratio : 4 * (r : ℝ) * q ≤ 4 * ((r : ℝ) + 1) * (q + 1) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) r]
  unfold calibratedTau
  change 4 * (r : ℝ) * (ε * localizedGramConstant freq / (4 * ((r : ℝ) + 1) * (q + 1)) * q) ≤ _
  rw [show 4 * (r : ℝ) * (ε * localizedGramConstant freq / (4 * ((r : ℝ) + 1) * (q + 1)) * q) =
    (ε * localizedGramConstant freq) * (4 * (r : ℝ) * q) / (4 * ((r : ℝ) + 1) * (q + 1)) by ring]
  exact (div_le_iff₀ hd).mpr (mul_le_mul_of_nonneg_left hratio hεc)

end ContinuumCoulomb

end

end OAI
