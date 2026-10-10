import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.EigenOrder

namespace OAI

noncomputable section
open Set Module

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma inverse_difference_pullback_identity {D B R S : E →L[ℝ] E}
    (hB : B.toLinearMap.IsSymmetric)
    (hBR : ∀ v, B (R v)=v) (hDS : ∀ v, S (D v)=v) (w : E) :
    inner ℝ (R (D w)-S (D w)) (D w)=
      inner ℝ ((D-B) w) w+inner ℝ (R ((D-B) w)) ((D-B) w) := by
  have hRB := left_inverse_of_right_inverse hBR
  have hRw : R (D w)-S (D w)=R ((D-B) w) := by
    simp only [sub_apply,map_sub,hDS,hRB]
  rw [hRw]
  have hsplit : D w=B w+(D-B) w := by simp
  conv_lhs => rhs; rw [hsplit]
  rw [inner_add_right]
  have H : inner ℝ (R ((D-B) w)) (B w)=inner ℝ ((D-B) w) w := by
    calc
      _ = inner ℝ (B (R ((D-B) w))) w := (hB _ _).symm
      _ = _ := congrArg (fun v => inner ℝ v w) (hBR ((D-B) w))
  rw [H]

lemma inverse_difference_pullback_lower {D B R S : E →L[ℝ] E} {c : ℝ}
    (hB : B.toLinearMap.IsSymmetric)
    (hBR : ∀ v, B (R v)=v) (hDS : ∀ v, S (D v)=v)
    (hR : ∀ v, 0≤ inner ℝ (R v) v)
    (hcross : ∀ v, c*‖v‖^2≤ inner ℝ ((D-B) v) v) (w : E) :
    c*‖w‖^2≤ inner ℝ (R (D w)-S (D w)) (D w) := by
  rw [inverse_difference_pullback_identity hB hBR hDS]
  exact (hcross w).trans (le_add_of_nonneg_right (hR _))

lemma inverse_difference_isotropic_of_factor
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {D B R S : E →L[ℝ] E} {J : F →L[ℝ] E} {C : E →L[ℝ] F} {a c : ℝ}
    (ha : 0<a) (hc : 0≤c)
    (hB : B.toLinearMap.IsSymmetric)
    (hBR : ∀ v, B (R v)=v) (hDS : ∀ v, S (D v)=v)
    (hR : ∀ v, 0≤ inner ℝ (R v) v)
    (hcross : ∀ v, c*‖v‖^2≤ inner ℝ ((D-B) v) v)
    (hfactor : ∀ v, D v=J (C v)) (hC : Function.Surjective C)
    (hbound : ∀ v, ‖C v‖≤a*‖v‖) (w : F) :
    (c/a^2)*‖w‖^2≤ inner ℝ (R (J w)-S (J w)) (J w) := by
  obtain ⟨v,rfl⟩ := hC w
  have H := inverse_difference_pullback_lower hB hBR hDS hR hcross v
  rw [hfactor v] at H
  apply le_trans _ H
  have hn : ‖C v‖^2≤a^2*‖v‖^2 := by
    nlinarith only [hbound v,sq_nonneg (a*‖v‖-‖C v‖),norm_nonneg (C v),
      mul_nonneg ha.le (norm_nonneg v)]
  calc
    (c/a^2)*‖C v‖^2≤(c/a^2)*(a^2*‖v‖^2) :=
      mul_le_mul_of_nonneg_left hn (div_nonneg hc (sq_nonneg a))
    _=c*‖v‖^2 := by field_simp

end WeakMTWTransport

end

end OAI
