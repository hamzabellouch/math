import Mathlib
import OAI.Analysis.HardSphere.Model

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere.Variational
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype J]

def energy (u : H × (J → H)) : ℝ := ∑ i, ‖u.2 i‖ ^ 2

def gradientPairing (u v : H × (J → H)) : ℂ := ∑ i, inner ℂ (u.2 i) (v.2 i)

omit [InnerProductSpace ℂ H] in
lemma energy_nonneg (u : H × (J → H)) : 0 ≤ energy u :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

lemma energy_smul (c : ℂ) (u : H × (J → H)) :
    energy (c • u) = ‖c‖ ^ 2 * energy u := by
  simp [energy, norm_smul, mul_pow, Finset.mul_sum]

theorem rayleigh (M : Submodule ℂ (H × (J → H))) (u : H × (J → H))
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) :
    energy u * ‖v.1‖ ^ 2 ≤ energy v := by
  by_cases hz : ‖v.1‖ = 0
  · simpa [hz] using energy_nonneg v
  · let c : ℂ := ((‖v.1‖ : ℂ))⁻¹
    have hc : ‖c‖ = ‖v.1‖⁻¹ := by simp [c, Complex.norm_real]
    have hv' : ‖(c • v).1‖ = 1 := by
      simp only [Prod.smul_fst, norm_smul, hc]
      exact inv_mul_cancel₀ hz
    have h := hmin (c • v) (M.smul_mem c hv) hv'
    rw [energy_smul, hc] at h
    calc
      energy u * ‖v.1‖ ^ 2 ≤ (‖v.1‖⁻¹ ^ 2 * energy v) * ‖v.1‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h (sq_nonneg _)
      _ = energy v := by field_simp

lemma norm_add_real_smul_sq (x y : H) (t : ℝ) :
    ‖x + (t : ℂ) • y‖ ^ 2 =
      ‖x‖ ^ 2 + 2 * t * (inner ℂ x y).re + t ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, mul_pow]
  simp [Complex.norm_real, sq_abs, mul_assoc]

lemma energy_add_real_smul (u v : H × (J → H)) (t : ℝ) :
    energy (u + (t : ℂ) • v) =
      energy u + 2 * t * (gradientPairing u v).re + t ^ 2 * energy v := by
  change (∑ i, ‖u.2 i + (t : ℂ) • v.2 i‖ ^ 2) = _
  simp_rw [norm_add_real_smul_sq]
  simp only [energy, gradientPairing, Finset.sum_add_distrib, Finset.mul_sum,
    Complex.re_sum]

lemma linear_term_zero {a b : ℝ} (ha : 0 ≤ a)
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t) : b = 0 := by
  have hd : 0 < a + 1 := by linarith
  have hh := mul_nonneg (h (-b / (a + 1))) (sq_nonneg (a + 1))
  have heq : (a * (-b / (a + 1)) ^ 2 + 2 * b * (-b / (a + 1))) *
      (a + 1) ^ 2 = -(a + 2) * b ^ 2 := by
    field_simp
    ring
  rw [heq] at hh
  have hb := sq_nonneg b
  have hprod := mul_nonneg ha hb
  nlinarith

theorem ground_pairing (M : Submodule ℂ (H × (J → H)))
    (u : H × (J → H)) (hu : u ∈ M) (hnorm : ‖u.1‖ = 1)
    (hmin : ∀ v ∈ M, ‖v.1‖ = 1 → energy u ≤ energy v)
    (v : H × (J → H)) (hv : v ∈ M) :
    gradientPairing u v = (energy u : ℂ) * inner ℂ u.1 v.1 := by
  have hre (w : H × (J → H)) (hw : w ∈ M) :
      (gradientPairing u w).re = energy u * (inner ℂ u.1 w.1).re := by
    have ha : 0 ≤ energy w - energy u * ‖w.1‖ ^ 2 :=
      sub_nonneg.mpr (rayleigh M u hmin w hw)
    have hpoly (t : ℝ) : 0 ≤
        (energy w - energy u * ‖w.1‖ ^ 2) * t ^ 2 +
          2 * ((gradientPairing u w).re - energy u * (inner ℂ u.1 w.1).re) * t := by
      have h := rayleigh M u hmin (u + (t : ℂ) • w) (M.add_mem hu (M.smul_mem _ hw))
      rw [energy_add_real_smul] at h
      simp only [Prod.fst_add, Prod.smul_fst, norm_add_real_smul_sq, hnorm, one_pow] at h
      nlinarith
    exact sub_eq_zero.mp (linear_term_zero ha hpoly)
  have hI := hre (Complex.I • v) (M.smul_mem _ hv)
  have hr := hre v hv
  apply Complex.ext
  · simpa using hr
  · simpa [gradientPairing, inner_smul_right, ← Finset.mul_sum, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.mul_im] using hI

end HardSphere.Variational

end
end
end
end

end OAI
