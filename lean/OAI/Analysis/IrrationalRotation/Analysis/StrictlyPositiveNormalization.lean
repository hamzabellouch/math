import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Tactic

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra
namespace Invariant233

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_one_sub_normalization_lt_one {a : A} (ha : IsStrictlyPositive a) :
    ‖1 - (‖a‖ + 1)⁻¹ • a‖ < 1 := by
  have hden : 0 < ‖a‖ + 1 := by positivity
  have he : cfc (fun x : ℝ => 1 - (‖a‖ + 1)⁻¹ * x) a =
      1 - (‖a‖ + 1)⁻¹ • a := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => (‖a‖ + 1)⁻¹ * x) a
      (by fun_prop) (by fun_prop), cfc_const 1 a ha.isSelfAdjoint,
      cfc_const_mul_id _ a ha.isSelfAdjoint]
    simp
  rw [← he]
  apply norm_cfc_lt zero_lt_one
  intro x hx
  have hxpos : 0 < x := ha.spectrum_pos hx
  have hxle : x ≤ ‖a‖ :=
    (Real.le_norm_self x).trans (IsometricContinuousFunctionalCalculus.norm_spectrum_le a hx ha.isSelfAdjoint)
  have hlo : 0 < (‖a‖ + 1)⁻¹ * x := mul_pos (inv_pos.mpr hden) hxpos
  have hhi : (‖a‖ + 1)⁻¹ * x < 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_lt_one hden).mpr (lt_of_le_of_lt hxle (lt_add_one _))
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith

theorem exists_pos_norm_one_sub_smul_lt_one {a : A} (ha : IsStrictlyPositive a) :
    ∃ c : ℝ, 0 < c ∧ ‖1 - c • a‖ < 1 :=
  ⟨(‖a‖ + 1)⁻¹, by positivity, norm_one_sub_normalization_lt_one ha⟩

theorem exists_pos_normalization_uniform_nhds {a : A} (ha : IsStrictlyPositive a) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ r < 1 ∧
      ∀ᶠ b in 𝓝 a, ‖1 - c • b‖ < r := by
  obtain ⟨c, hc, hn⟩ := exists_pos_norm_one_sub_smul_lt_one ha
  obtain ⟨r, hr, hr1⟩ := exists_between hn
  refine ⟨c, r, hc, (norm_nonneg _).trans_lt hr, hr1, ?_⟩
  have hcont : Continuous (fun b : A => ‖1 - c • b‖) := by fun_prop
  exact hcont.continuousAt.eventually_lt continuousAt_const hr

theorem exists_pos_normalization_uniform_along
    {X : Type*} [TopologicalSpace X] {f : X → A} {x : X}
    (hf : ContinuousAt f x) (ha : IsStrictlyPositive (f x)) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ r < 1 ∧
      ∀ᶠ y in 𝓝 x, ‖1 - c • f y‖ < r := by
  obtain ⟨c, r, hc, hr, hr1, hloc⟩ := exists_pos_normalization_uniform_nhds ha
  exact ⟨c, r, hc, hr, hr1, hf.eventually hloc⟩

end Invariant233

end

end OAI
