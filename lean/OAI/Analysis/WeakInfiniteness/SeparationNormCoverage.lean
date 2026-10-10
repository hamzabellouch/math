import Mathlib
import OAI.Analysis.WeakInfiniteness.SeparationScalar

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section

variable {B : Type*} [CStarAlgebra B]

lemma separation_detection_alternative (a x₀ D K : B) {r l τ : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hτ : τ=r*Real.sqrt l/8)
    (ha : r ≤ ‖a‖) (haeq : a=x₀+D*K) (hK : ‖K‖ ≤ (Real.sqrt l)⁻¹) :
    r/2 ≤ ‖x₀‖ ∨ τ ≤ max (‖D‖-2*τ) 0 := by
  by_cases hx : r/2 ≤ ‖x₀‖
  · exact Or.inl hx
  right
  have hroot : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hn : r ≤ ‖x₀‖+‖D‖*(Real.sqrt l)⁻¹ := by
    apply ha.trans
    rw [haeq]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ((norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left hK (norm_nonneg _))))
  have hmul := mul_le_mul_of_nonneg_right hn hroot.le
  have hinv : (Real.sqrt l)⁻¹*Real.sqrt l=1 := inv_mul_cancel₀ (ne_of_gt hroot)
  have hnorm : ‖D‖*(Real.sqrt l)⁻¹*Real.sqrt l=‖D‖ := by rw [mul_assoc,hinv,mul_one]
  have hsmall := mul_lt_mul_of_pos_right (lt_of_not_ge hx) hroot
  have hτeq : 8*τ=r*Real.sqrt l := by rw [hτ]; ring
  exact (by nlinarith : τ ≤ ‖D‖-2*τ).trans (le_max_left _ _)

lemma separation_normalized_column_lower (F Y : B) {r l τ c : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hτ : τ=r*Real.sqrt l/8)
    (hF : ‖F‖ ≤ τ⁻¹) (hY : c ≤ ‖F*Y‖) :
    r*c/8 ≤ ‖(((Real.sqrt l)⁻¹ : ℝ) : ℂ) • Y‖ := by
  have hroot : 0 < Real.sqrt l := Real.sqrt_pos.mpr hl
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hn : c ≤ τ⁻¹*‖Y‖ := hY.trans ((norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right hF (norm_nonneg _)))
  have hmul := mul_le_mul_of_nonneg_left hn hτpos.le
  have hinv : τ*τ⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hτpos)
  have hy : τ*c ≤ ‖Y‖ := by simpa only [← mul_assoc,hinv,one_mul] using hmul
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hroot),mul_comm ((Real.sqrt l)⁻¹) ‖Y‖,← div_eq_mul_inv]
  apply (le_div_iff₀ hroot).mpr
  rw [hτ] at hy
  nlinarith

lemma separation_column_coverage (a x₀ C N K F Y : B) {r l τ c : ℝ}
    (hr : 0 < r) (hl : 0 < l) (hτ : τ=r*Real.sqrt l/8) (hc : c ≤ 4)
    (ha : r ≤ ‖a‖) (haeq : a=x₀+(C*N)*K) (hK : ‖K‖ ≤ (Real.sqrt l)⁻¹)
    (hF : ‖F‖ ≤ τ⁻¹)
    (hdet : τ ≤ max (‖C*N‖-2*τ) 0 → c ≤ ‖F*Y‖) :
    r*c/8 ≤ max ‖x₀‖ ‖(((Real.sqrt l)⁻¹ : ℝ) : ℂ) • Y‖ := by
  obtain hx | hd := separation_detection_alternative a x₀ (C*N) K hr hl hτ ha haeq hK
  · exact (by nlinarith : r*c/8 ≤ ‖x₀‖).trans (le_max_left _ _)
  · exact (separation_normalized_column_lower F Y hr hl hτ hF (hdet hd)).trans (le_max_right _ _)

end

section

variable {B : Type*} [CStarAlgebra B]

lemma separation_LN_decomposition (a T : B) (hT : IsSelfAdjoint T) (l : ℝ) :
    a=a*cfc (separationL l) T+a*cfc (separationN l) T := by
  rw [← mul_add]
  have he : cfc (separationL l) T+cfc (separationN l) T=1 := by
    rw [← cfc_add _ _ _ (continuous_separationL l).continuousOn (continuous_separationN l).continuousOn]
    have hfun : (fun s => separationL l s+separationN l s)=(fun _ => (1 : ℝ)) := by
      funext s
      unfold separationL
      ring
    rw [hfun,cfc_const_one ℝ T hT]
  rw [he,mul_one]

end

end

end WeakPureInfiniteness
end

end OAI
