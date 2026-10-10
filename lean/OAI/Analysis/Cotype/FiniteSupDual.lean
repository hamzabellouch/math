import OAI.Analysis.Cotype.FiniteL2Dual

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω]

theorem exists_unit_eval_gt (φ : X →L[ℝ] ℝ) {a : ℝ} (ha : a < ‖φ‖) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ a < φ x := by
  by_cases han : a < 0
  · exact ⟨0, by simp, by simpa using han⟩
  have hap : 0 ≤ a := le_of_not_gt han
  by_contra hn
  push Not at hn
  have hbound : ‖φ‖ ≤ a := by
    apply φ.opNorm_le_of_unit_norm hap
    intro x hx
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have h := hn (-x) (by simp [hx])
      simpa only [map_neg, neg_le] using h
    · exact hn x hx.le
  exact (not_le_of_gt ha) hbound

def finiteSupDualLinear (g : Ω → (X →L[ℝ] ℝ)) : (Ω → X) →ₗ[ℝ] ℝ where
  toFun f := ∑ a, g a (f a)
  map_add' f h := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

theorem finiteSupDualLinear_bound (g : Ω → (X →L[ℝ] ℝ)) (f : Ω → X) :
    ‖finiteSupDualLinear g f‖ ≤ (∑ a, ‖g a‖) * ‖f‖ := by
  calc
    _ ≤ ∑ a, ‖g a (f a)‖ := norm_sum_le _ _
    _ ≤ ∑ a, ‖g a‖ * ‖f‖ := Finset.sum_le_sum (fun a _ =>
      ((g a).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm f a) (norm_nonneg _)))
    _ = _ := (Finset.sum_mul _ _ _).symm

def finiteSupDual (g : Ω → (X →L[ℝ] ℝ)) : (Ω → X) →L[ℝ] ℝ :=
  (finiteSupDualLinear g).mkContinuous (∑ a, ‖g a‖) (finiteSupDualLinear_bound g)

@[simp] theorem finiteSupDual_apply (g : Ω → (X →L[ℝ] ℝ)) (f : Ω → X) :
    finiteSupDual g f = ∑ a, g a (f a) := rfl

theorem finiteSupDual_norm (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteSupDual g‖ = ∑ a, ‖g a‖ := by
  apply le_antisymm
  · exact (finiteSupDual g).opNorm_le_bound (Finset.sum_nonneg (fun a _ => norm_nonneg _))
      (finiteSupDualLinear_bound g)
  · apply le_of_forall_pos_le_add
    intro ε hε
    let δ := ε / (Fintype.card Ω + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    choose x hx he using (fun a => exists_unit_eval_gt (g a) (by linarith : ‖g a‖ - δ < ‖g a‖))
    have hxn : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr hx
    have hv : (finiteSupDual g) x ≤ ‖finiteSupDual g‖ :=
      (le_abs_self _).trans ((finiteSupDual g).le_opNorm x |>.trans
        ((mul_le_mul_of_nonneg_left hxn (norm_nonneg _)).trans_eq (mul_one _)))
    have hδcard : (Fintype.card Ω : ℝ) * δ ≤ ε := by
      have hh : (Fintype.card Ω + 1) * δ = ε := by dsimp [δ]; field_simp
      nlinarith
    calc
      ∑ a, ‖g a‖ ≤ ∑ a, (g a (x a) + δ) := Finset.sum_le_sum (fun a _ => by linarith [he a])
      _ = finiteSupDual g x + (Fintype.card Ω : ℝ) * δ := by simp [Finset.sum_add_distrib]
      _ ≤ _ := by linarith

end Cotype

end

end OAI
