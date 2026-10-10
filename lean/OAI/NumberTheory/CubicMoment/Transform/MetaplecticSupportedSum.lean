import OAI.NumberTheory.CubicMoment.Estimates.SmallEulerProduct
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryProductCoefficients
import OAI.NumberTheory.CubicMoment.Estimates.IdealMellinSeries

namespace OAI

/-! Supported primary factors in the retained metaplectic sum have
convergent weighted Euler products with arbitrarily small level loss. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma idealExponent_support_of_dvd_power {b r : Eisenstein}
    (hb : b ≠ 0) (hr : r ≠ 0) (hd : ∃ k : ℕ, b ∣ r^k) :
    (idealExponentOf b).support ⊆ (idealExponentOf r).support := by
  obtain ⟨k,hk⟩ := hd
  have hle := idealExponentOf_le_of_dvd hb (pow_ne_zero k hr) hk
  rw [idealExponentOf_pow hr k] at hle
  intro p hp
  by_contra hpr
  have hz := Finsupp.notMem_support_iff.mp hpr
  have he := hle p
  simp only [Finsupp.coe_smul,Pi.smul_apply,hz,smul_zero] at he
  exact (Finsupp.mem_support_iff.mp hp) (Nat.eq_zero_of_le_zero he)

/-- The exponent δ of the convergent supported sum is fixed independently
of the arbitrarily small loss ε in the level. -/
theorem primary_supported_norm_sum {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Eisenstein, primary r →
      ∀ (S : Finset Eisenstein) (J : ℝ), (∀ b ∈ S, primary b) →
      (∀ b ∈ S, ∃ k : ℕ, b ∣ r^k) → (∀ b ∈ S, norm b ≤ J) →
      (∑ b ∈ S, norm b^(-δ)) ≤ C*norm r^ε := by
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  obtain ⟨C,hC,hEuler⟩ := supported_euler_small_power hη
  refine ⟨C,hC,?_⟩
  intro r hr S J hS hsupport hJ
  let T := S.image idealExponentOf
  have hT : ∀ ν ∈ T, ν.support ⊆ (idealExponentOf r).support ∧ idealExponentNorm ν ≤ J := by
    intro ν hν
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hν
    refine ⟨idealExponent_support_of_dvd_power (primary_ne_zero (hS b hb))
      (primary_ne_zero hr) (hsupport b hb),?_⟩
    rw [idealExponentOf_norm (primary_ne_zero (hS b hb))]
    exact hJ b hb
  have hs := ideal_supported_rankin_sum hη (idealExponentOf r).support T hT
  have he : (∑ ν ∈ T, idealExponentNorm ν^(-η)) = ∑ b ∈ S, norm b^(-η) := by
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro b hb
      rw [idealExponentOf_norm (primary_ne_zero (hS b hb))]
    · intro b hb c hc hbc
      exact primary_eq_of_idealExponentOf_eq (hS b hb) (hS c hc) hbc
  rw [he] at hs
  calc
    _ ≤ ∑ b ∈ S, norm b^(-η) := by
      apply Finset.sum_le_sum
      intro b hb
      exact Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero (hS b hb)))
        (neg_le_neg (min_le_right ε δ))
    _ ≤ ∏ p ∈ (idealExponentOf r).support,
        (1-(normNat (idealPrimeRepresentative p):ℝ)^(-η))⁻¹ := hs
    _ ≤ C*idealExponentNorm (idealExponentOf r)^η := hEuler (idealExponentOf r)
    _ = C*norm r^η := by rw [idealExponentOf_norm (primary_ne_zero hr)]
    _ ≤ C*norm r^ε := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (one_le_norm (primary_ne_zero hr)) (min_le_left ε δ)) hC.le

end CubicFirstMoment

end

end OAI
