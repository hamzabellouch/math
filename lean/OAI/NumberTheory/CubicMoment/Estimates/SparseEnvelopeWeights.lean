import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! The fixed product envelope in the sparse branch gives an actual
uniform family of inner weights on every fixed outer norm dyad. -/
noncomputable section
open Set
open scoped ContDiff
namespace CubicFirstMoment

lemma scaled_exp_log {s : ℝ} (hs : 0 < s) (u : ℝ) :
    s*Real.exp (-u) = Real.exp (-(u-Real.log s)) := by
  rw [neg_sub,Real.exp_sub,Real.exp_log hs,div_eq_mul_inv,←Real.exp_neg]

/-- A bounded logarithmic dilation preserves the given uniform smooth
weight bounds. Its support and all derivatives are derived explicitly. -/
def UniformLogWeights.logDilate {γ : Type*} {W : γ → ℝ → ℂ}
    (h : UniformLogWeights W) (D : ℝ) (hD : 0 ≤ D) :
    UniformLogWeights (fun z : γ × {s : ℝ // 0 < s ∧ |Real.log s| ≤ D} =>
      fun x => W z.1 (z.2*x)) := by
  refine ⟨?_,?_,?_,h.radius+D,add_nonneg h.radius_nonneg hD,?_,?_⟩
  · intro z
    exact (h.compact z.1).comp_homeomorph
      (Homeomorph.mulLeft₀ (z.2:ℝ) z.2.property.1.ne')
  · intro z x hx
    have hs : (z.2:ℝ)*x ∈ tsupport (W z.1) :=
      tsupport_comp_subset_preimage (W z.1) (f := fun x : ℝ => (z.2:ℝ)*x) (by fun_prop) hx
    have hp := h.positive z.1 hs
    change 0 < (z.2:ℝ)*x at hp
    exact (mul_pos_iff_of_pos_left z.2.property.1).mp hp
  · intro z
    exact (h.smooth z.1).comp (contDiff_const.mul contDiff_id)
  · intro z u hu
    have he : (fun v : ℝ => W z.1 ((z.2:ℝ)*Real.exp (-v))) =
        (fun v : ℝ => W z.1 (Real.exp (-v))) ∘ (fun v : ℝ => v-Real.log (z.2:ℝ)) := by
      ext v
      simp only [Function.comp_apply,scaled_exp_log z.2.property.1]
    rw [he] at hu
    have hs : u-Real.log (z.2:ℝ) ∈ tsupport (fun v : ℝ => W z.1 (Real.exp (-v))) :=
      tsupport_comp_subset_preimage _ (f := fun v : ℝ => v-Real.log (z.2:ℝ)) (by fun_prop) hu
    calc
      |u| = |(u-Real.log (z.2:ℝ))+Real.log (z.2:ℝ)| := by congr 1; ring
      _ ≤ |u-Real.log (z.2:ℝ)|+|Real.log (z.2:ℝ)| := abs_add_le _ _
      _ ≤ _ := add_le_add (h.support_bound z.1 _ hs) z.2.property.2
  · intro n
    obtain ⟨B,hB,hbound⟩ := h.derivative_bound n
    refine ⟨B,hB,?_⟩
    intro z u
    have he : (fun v : ℝ => W z.1 ((z.2:ℝ)*Real.exp (-v))) =
        (fun v : ℝ => W z.1 (Real.exp (-(v-Real.log (z.2:ℝ))))) := by
      ext v
      rw [scaled_exp_log z.2.property.1]
    rw [he]
    rw [iteratedFDeriv_comp_sub (f := fun v : ℝ => W z.1 (Real.exp (-v))) n (Real.log (z.2:ℝ)) u]
    exact hbound z.1 (u-Real.log (z.2:ℝ))

lemma log_dyad_ratio {a A M : ℝ} (hA : 0 < A) (_hM : 1 ≤ M)
    (ha : A ≤ a) (haM : a ≤ M*A) :
    0 < a/A ∧ |Real.log (a/A)| ≤ Real.log M := by
  have hratio : 1 ≤ a/A := (le_div_iff₀ hA).mpr (by simpa using ha)
  have hupper : a/A ≤ M := (div_le_iff₀ hA).mpr (by simpa only [mul_comm] using haM)
  refine ⟨zero_lt_one.trans_le hratio,?_⟩
  rw [abs_of_nonneg (Real.log_nonneg hratio)]
  exact Real.log_le_log (zero_lt_one.trans_le hratio) hupper

end CubicFirstMoment

end

end OAI
