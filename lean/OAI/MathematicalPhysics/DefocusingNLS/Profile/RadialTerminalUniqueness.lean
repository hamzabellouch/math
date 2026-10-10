import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! Backward uniqueness from a decay rate exceeding the bounded ODE coefficient. -/

open Set Filter
namespace DefocusingNLS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_le_backward_gronwall (f f' : ℝ → E) (B T t s : ℝ)
    (hf : ContinuousOn f (Ici T))
    (hd : ∀ r, T ≤ r → HasDerivAt f (f' r) r)
    (hb : ∀ r, T ≤ r → ‖f' r‖ ≤ B*‖f r‖)
    (ht : T ≤ t) (hs : t ≤ s) :
    ‖f t‖ ≤ ‖f s‖*Real.exp (B*(s-t)) := by
  let g : ℝ → E := fun u => f (s-u)
  let g' : ℝ → E := fun u => -(f' (s-u))
  have hc : ContinuousOn g (Icc 0 (s-t)) :=
    hf.comp (continuous_const.sub continuous_id).continuousOn
      (fun u hu => by change T ≤ s-u; have := hu.2; linarith)
  have hder : ∀ u ∈ Ico 0 (s-t), HasDerivWithinAt g (g' u) (Ici u) u := by
    intro u hu
    have hr : T ≤ s-u := by have := hu.2; linarith
    have h := (hd (s-u) hr).scomp u ((hasDerivAt_id u).const_sub s)
    simpa only [g,g',neg_one_smul] using! h.hasDerivWithinAt
  have hbound : ∀ u ∈ Ico 0 (s-t), ‖g' u‖ ≤ B*‖g u‖+0 := by
    intro u hu
    dsimp [g,g']
    rw [norm_neg,add_zero]
    apply hb
    have := hu.2
    linarith
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hc hder
    (show ‖g 0‖ ≤ ‖f s‖ by simp [g]) hbound (s-t) ⟨by linarith,le_rfl⟩
  have he : gronwallBound ‖f s‖ B 0 (s-t)=‖f s‖*Real.exp (B*(s-t)) := by
    by_cases hB : B=0 <;> simp [gronwallBound,hB]
  simpa only [g,sub_sub_cancel,sub_zero,he] using h

theorem eq_zero_of_fast_exponential_decay (f f' : ℝ → E) (B κ C T : ℝ)
    (hf : ContinuousOn f (Ici T))
    (hd : ∀ r, T ≤ r → HasDerivAt f (f' r) r)
    (hb : ∀ r, T ≤ r → ‖f' r‖ ≤ B*‖f r‖)
    (hdec : ∀ r, T ≤ r → ‖f r‖ ≤ C*Real.exp (-κ*r))
    (hκ : B < κ) (t : ℝ) (ht : T ≤ t) : f t=0 := by
  have hlim : Tendsto (fun s : ℝ => C*Real.exp (-B*t)*Real.exp (-(κ-B)*s))
      atTop (nhds 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (sub_pos.mpr hκ))
    have he : Tendsto (fun s : ℝ => Real.exp (-(κ-B)*s)) atTop (nhds 0) := by
      convert h using 1
      funext s
      congr 1
      dsimp
      ring
    simpa only [mul_zero] using he.const_mul (C*Real.exp (-B*t))
  apply norm_le_zero_iff.mp
  apply ge_of_tendsto hlim
  filter_upwards [eventually_ge_atTop t] with s hs
  calc
    ‖f t‖ ≤ ‖f s‖*Real.exp (B*(s-t)) := norm_le_backward_gronwall f f' B T t s hf hd hb ht hs
    _ ≤ (C*Real.exp (-κ*s))*Real.exp (B*(s-t)) :=
      mul_le_mul_of_nonneg_right (hdec s (ht.trans hs)) (Real.exp_nonneg _)
    _ = C*Real.exp (-B*t)*Real.exp (-(κ-B)*s) := by
      simp only [mul_assoc,← Real.exp_add]
      congr 2
      ring

end DefocusingNLS

end OAI
