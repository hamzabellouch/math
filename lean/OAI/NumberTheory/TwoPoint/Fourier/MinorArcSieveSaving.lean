import OAI.NumberTheory.TwoPoint.Fourier.MinorArcParameters
import OAI.NumberTheory.TwoPoint.Bounds.SievePrimeEnergy

namespace OAI

/-! The four-prime estimate in corrected MRT, equation (3.3). -/

namespace TwoPointCorrelations

open Finset Filter

/-- The additive-energy sieve and rational kernel give the required uniform
four-prime saving. The prime set may be any subset of the dyadic prime block. -/
theorem minor_arc_sieve_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ R : ℝ in atTop,
      ∀ (P : Finset ℕ) (N : ℕ),
      (∀ p ∈ P, p.Prime ∧ p ≠ 2 ∧ p ≤ N) → (N : ℝ) ≤ 2 * R →
      ∀ H W V : ℝ, 1 ≤ W → W ≤ R →
      ∀ (a : ℤ) (q : ℕ), 2 ≤ q → W ≤ (q : ℝ) → (q : ℝ) ≤ H / W →
      R ≤ H / W → 0 ≤ V → V ≤ H / R →
      ∀ α : ℝ, IsCoprime (q : ℤ) a →
      |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ p₁ ∈ P, ∑ p₂ ∈ P, ∑ p₃ ∈ P, ∑ p₄ ∈ P,
        minorArcGeometricBound V (α * ((p₁ : ℝ) + p₂ - p₃ - p₄))) ≤
          C * H * R ^ 3 * (1 + Real.log H) / (W * Real.log R ^ 4) := by
  obtain ⟨C, hC, henergy⟩ := sieve_prime_additive_energy
  refine ⟨192 * C, by positivity, ?_⟩
  filter_upwards [henergy, eventually_ge_atTop (1 : ℝ)] with R henergy hR
  intro P N hP hN H W V hW hWR a q hq hWq hqH hRH hV hVR α hcop happ
  have hE := henergy P (fun p hp =>
    ⟨(hP p hp).1, (hP p hp).2.1,
      (show (p : ℝ) ≤ N by exact_mod_cast (hP p hp).2.2).trans hN⟩)
  have hkernel := minor_arc_prime_kernel_rational P N (fun p hp => (hP p hp).2.2)
    α V hV a q hq hcop happ
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hparam := minor_arc_parameter_bound R H W (q : ℝ) V hR hW hWR hWq hqH hRH hV hVR
  have hmon :
      2 * (3 * (2 * (N : ℝ) + 1) / q + 1) *
        (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) ≤
      2 * (3 * (4 * R + 1) / q + 1) *
        (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) := by
    have hnum : 3 * (2 * (N : ℝ) + 1) ≤ 3 * (4 * R + 1) := by linarith
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact add_le_add (div_le_div_of_nonneg_right hnum hqpos.le) le_rfl
  have hparam0 : 0 ≤ 192 * H * (1 + Real.log H) / W :=
    (by positivity : 0 ≤
      2 * (3 * (2 * (N : ℝ) + 1) / q + 1) *
        (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)))) |>.trans (hmon.trans hparam)
  calc
    _ ≤ (Finset.addEnergy P P : ℝ) *
        (192 * H * (1 + Real.log H) / W) :=
      hkernel.trans (mul_le_mul_of_nonneg_left (hmon.trans hparam) (Nat.cast_nonneg _))
    _ ≤ (C * R ^ 3 / Real.log R ^ 4) *
        (192 * H * (1 + Real.log H) / W) := mul_le_mul_of_nonneg_right hE hparam0
    _ = _ := by ring

end TwoPointCorrelations

end OAI
