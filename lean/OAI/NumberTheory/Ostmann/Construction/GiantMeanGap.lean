import OAI.NumberTheory.Ostmann.Preliminaries.MertensShortBlockMass

namespace OAI

/-! # The numerical margin for the positive giant mean -/

namespace Ostmann
open scoped Classical BigOperators

theorem giant_mean_numeric_gap (M B F h G γ c : ℝ)
    (hM0 : 0 ≤ M) (hB0 : 0 ≤ B) (hh : 0 < h) (hG : 0 < G)
    (hγ : 0 < γ) (hc : 0 < c)
    (hM : M ≤ 2 * h / G) (hB : B ≤ γ ^ 2 * c ^ 2 * h / 512)
    (hF : c * h / (2 * G) ≤ F) :
    (γ * c / 32) * M + Real.sqrt M * Real.sqrt (B / G) < (γ / 2) * F := by
  have hroot0 : 0 ≤ Real.sqrt M * Real.sqrt (B / G) := by positivity
  have hrootSq : (Real.sqrt M * Real.sqrt (B / G)) ^ 2 = M * (B / G) := by
    rw [mul_pow, Real.sq_sqrt hM0, Real.sq_sqrt (div_nonneg hB0 hG.le)]
  have hb' : B / G ≤ (γ ^ 2 * c ^ 2 * h / 512) / G :=
    div_le_div_of_nonneg_right hB hG.le
  have hs : M * (B / G) ≤ (γ * c * h / (16 * G)) ^ 2 := by
    apply (mul_le_mul hM hb' (div_nonneg hB0 hG.le) (by positivity)).trans_eq
    field_simp
    ring
  have hr : Real.sqrt M * Real.sqrt (B / G) ≤ γ * c * h / (16 * G) := by
    have hpos : 0 < γ * c * h / (16 * G) := by positivity
    rw [← hrootSq] at hs
    nlinarith
  have hm : (γ * c / 32) * M ≤ γ * c * h / (16 * G) := by
    apply (mul_le_mul_of_nonneg_left hM (by positivity : 0 ≤ γ * c / 32)).trans_eq
    field_simp
    ring
  have hf : γ * c * h / (4 * G) ≤ (γ / 2) * F := by
    apply le_trans _ (mul_le_mul_of_nonneg_left hF (by positivity : 0 ≤ γ / 2))
    field_simp
    ring_nf
    exact le_refl _
  have hpos : 0 < γ * c * h / G := by positivity
  have hid : γ * c * h / (4 * G) = 4 * (γ * c * h / (16 * G)) := by ring
  have hid' : γ * c * h / G = 16 * (γ * c * h / (16 * G)) := by ring
  rw [hid] at hf
  rw [hid'] at hpos
  linarith

theorem favorable_block_harmonic_lower (F : Finset ℕ) (G c h : ℝ)
    (hG : 0 < G) (hlog : ∀ p ∈ F, Real.log (p : ℝ) ≤ 2 * G)
    (hmass : c * h ≤ ∑ p ∈ F, Real.log (p : ℝ) / p) :
    c * h / (2 * G) ≤ ∑ p ∈ F, (p : ℝ)⁻¹ := by
  apply (div_le_iff₀ (by positivity : 0 < 2 * G)).mpr
  apply hmass.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  simpa only [div_eq_mul_inv, mul_comm] using
    mul_le_mul_of_nonneg_right (hlog p hp) (by positivity : 0 ≤ (p : ℝ)⁻¹)

theorem logBlock_giant_mean_gap {C : ℝ} (hMertens : MertensEstimate C)
    (P F : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (lo h γ c B : ℝ)
    (hlo : 5 ≤ lo) (hh : 0 < h) (hγ : 0 < γ) (hc : 0 < c) (hB0 : 0 ≤ B)
    (hwidth : 8 + Real.log 2 + 2 * C ≤ h)
    (hupper : lo + h ≤ 2 * (lo - 4))
    (hFlog : ∀ p ∈ F, Real.log (p : ℝ) ≤ lo + h)
    (hFmass : c * h ≤ ∑ p ∈ F, Real.log (p : ℝ) / p)
    (hB : B ≤ γ ^ 2 * c ^ 2 * h / 512) :
    (γ * c / 32) *
        (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo (lo + h)) p) +
      Real.sqrt (∑ p ∈ P, (p : ℝ)⁻¹ * logCellFamilyWeight (logBlockCenters lo (lo + h)) p) *
        Real.sqrt (B / (lo - 4)) < (γ / 2) * ∑ p ∈ F, (p : ℝ)⁻¹ := by
  apply giant_mean_numeric_gap _ B _ h (lo - 4) γ c
    (Finset.sum_nonneg fun p _ => mul_nonneg (by positivity) (logCellFamilyWeight_nonneg _ _))
    hB0 hh (by linarith) hγ hc
  · apply (logBlock_family_mass_upper hMertens P hP lo (lo + h) hlo (by linarith)).trans
    apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ lo - 4)
    linarith
  · exact hB
  · exact favorable_block_harmonic_lower F (lo - 4) c h (by linarith)
      (fun p hp => (hFlog p hp).trans hupper) hFmass

end Ostmann

end OAI
