import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialScalarProfile
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! A uniform large-power threshold for the prescribed-potential scalar inner problem. -/

open Set Filter Topology
namespace DefocusingNLS

theorem scalar_boundary_power_small (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ P : ℕ, 2 ≤ P ∧ ∀ p : ℕ, P ≤ p →
      ∀ lo : ℝ, 0 ≤ lo → lo ≤ q → lo^(p-1) ≤ (3/10 : ℝ) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have he : ∀ᶠ n : ℕ in atTop, q^n < (3/10 : ℝ) :=
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 3/10))
  obtain ⟨N,hN⟩ := eventually_atTop.1 he
  refine ⟨N+2,by omega,?_⟩
  intro p hp lo hlo hloq
  exact (pow_le_pow_left₀ hlo hloq (p-1)).trans (hN (p-1) (by omega)).le

theorem exists_scalar_profiles_large_power (R q : ℝ) (hR : 0 < R)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∃ P : ℕ, 2 ≤ P ∧ ∀ p : ℕ, P ≤ p → ∀ lo : ℝ, 0 < lo → lo ≤ q →
      ∀ V : ℝ → ℝ, Continuous V →
        (∀ r ∈ Icc 0 R, V r ∈ Icc (3/10 : ℝ) (1/2)) →
        ∃ A : ℝ → ℝ, Differentiable ℝ A ∧ A R=lo ∧ HasDerivAt A 0 0 ∧
          (∀ r ∈ Icc 0 R, lo ≤ A r ∧ (A r)^(p-1) ≤ (1/2 : ℝ)) ∧
          (∀ r ∈ Ioo 0 R,
            -deriv (deriv A) r-11/r*deriv A r+(A r)^p=V r*A r) := by
  obtain ⟨P,hP,hSmall⟩ := scalar_boundary_power_small q hq0 hq1
  refine ⟨P,hP,?_⟩
  intro p hp lo hlo hloq V hV hVB
  exact exists_radial_scalar_profile p (hP.trans hp) R lo hR hlo
    (hSmall p hp lo hlo.le hloq) V hV hVB

end DefocusingNLS

end OAI
