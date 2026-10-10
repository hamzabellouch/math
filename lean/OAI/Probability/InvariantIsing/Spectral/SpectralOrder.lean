import OAI.Probability.InvariantIsing.Spectral.SpectralCovariance

namespace OAI

/-! Order and uniform perturbation bounds for finite spectral transforms. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

theorem finiteResolvent_mono_eig (ρ eig eig' : ι → ℝ) (hρ : ∀ a, 0 ≤ ρ a)
    (heig : ∀ a, eig a ≤ eig' a) {b : ℝ} (hb : ∀ a, eig' a < b) :
    finiteResolvent ρ eig b ≤ finiteResolvent ρ eig' b := by
  apply Finset.sum_le_sum
  intro a _
  exact div_le_div_of_nonneg_left (hρ a) (sub_pos.mpr (hb a)) (by linarith [heig a])

theorem finiteInverse_mono_eig (ρ eig eig' : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (heig : ∀ a, eig a ≤ eig' a) {x : ℝ} (hx : 0 < x) :
    finiteInverse ρ eig hρ hρsum x ≤ finiteInverse ρ eig' hρ hρsum x := by
  have hs := finiteInverse_spec ρ eig hρ hρsum hx
  have hs' := finiteInverse_spec ρ eig' hρ hρsum hx
  by_contra! h
  have hlt := finiteResolvent_strictAnti (fun a => (hρ a).le) hρsum
    (fun a => lt_of_le_of_lt (heig a) (hs'.1 a)) h
  have hle := finiteResolvent_mono_eig ρ eig eig' (fun a => (hρ a).le) heig hs'.1
  rw [hs.2] at hlt
  rw [hs'.2] at hle
  linarith

theorem finiteR_mono_eig (ρ eig eig' : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (heig : ∀ a, eig a ≤ eig' a) (x : ℝ) :
    finiteR ρ eig hρ hρsum x ≤ finiteR ρ eig' hρ hρsum x := by
  by_cases hx : 0 < x
  · simp only [finiteR, ite_eq_left hx]
    exact sub_le_sub_right (finiteInverse_mono_eig ρ eig eig' hρ hρsum heig hx) _
  · simp only [finiteR, ite_eq_right hx]
    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (heig a) (hρ a).le

/-- Uniform coordinate perturbations give the same uniform error in `R`. -/
theorem finiteR_perturbation (ρ eig eig' : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) {δ : ℝ} (heig : ∀ a, |eig a - eig' a| ≤ δ)
    {x : ℝ} (hx : 0 ≤ x) :
    |finiteR ρ eig hρ hρsum x - finiteR ρ eig' hρ hρsum x| ≤ δ := by
  have hupper := finiteR_mono_eig ρ eig (fun a => eig' a + δ) hρ hρsum
    (fun a => by have h := (abs_le.mp (heig a)).2; linarith) x
  have hlower := finiteR_mono_eig ρ eig' (fun a => eig a + δ) hρ hρsum
    (fun a => by have h := (abs_le.mp (heig a)).1; linarith) x
  rw [finiteR_translate ρ eig' hρ hρsum hx δ] at hupper
  rw [finiteR_translate ρ eig hρ hρsum hx δ] at hlower
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end InvariantIsing

end

end OAI
