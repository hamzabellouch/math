import OAI.Analysis.CircleDomains.Sobolev.L2AdditiveMajorant

namespace OAI

/-! The three error terms in the barrier comparison retain their separate
L2 budgets. -/
open Set Function Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem real_l2_add_bound {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (eLpNorm (fun x => f x+g x) 2 μ).toReal ≤
      (eLpNorm f 2 μ).toReal+(eLpNorm g 2 μ).toReal := by
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.ne_top, hg.ne_top⟩)
    (eLpNorm_add_le (f := f) (g := g) (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  rw [show (fun x => f x+g x) = f+g from rfl]
  rw [ENNReal.toReal_add hf.ne_top hg.ne_top] at hh
  exact hh

 theorem real_l2_nonneg_scale {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (eLpNorm (fun x => a*f x) 2 μ).toReal = a*(eLpNorm f 2 μ).toReal := by
  have hh : eLpNorm (fun x => a*f x) 2 μ = ENNReal.ofReal a*eLpNorm f 2 μ := by
    change eLpNorm (a • f) 2 μ = _
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg ha] using eLpNorm_const_smul a f 2 μ
  rw [hh, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha]

 theorem l2_three_term_bound {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {F : X → E} {g h k : X → ℝ}
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hF : AEStronglyMeasurable F μ) (hg : MemLp g 2 μ)
    (hh : MemLp h 2 μ) (hk : MemLp k 2 μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (hh0 : ∀ᵐ x ∂μ, 0 ≤ h x) (hk0 : ∀ᵐ x ∂μ, 0 ≤ k x)
    (hbound : ∀ᵐ x ∂μ, ‖F x‖ ≤ a*g x+b*h x+c*k x) :
    MemLp F 2 μ ∧ (eLpNorm F 2 μ).toReal ≤
      a*(eLpNorm g 2 μ).toReal+b*(eLpNorm h 2 μ).toReal+c*(eLpNorm k 2 μ).toReal := by
  let v := fun x => a*g x+b*h x+c*k x
  have hv : MemLp v 2 μ := ((hg.const_mul a).add (hh.const_mul b)).add (hk.const_mul c)
  have hnorm : ∀ᵐ x ∂μ, ‖F x‖ ≤ ‖v x‖ := by
    filter_upwards [hbound, hg0, hh0, hk0] with x hx hxg hxh hxk
    simpa only [v, Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (add_nonneg (mul_nonneg ha hxg) (mul_nonneg hb hxh)) (mul_nonneg hc hxk))] using hx
  refine ⟨hv.of_le hF hnorm, ?_⟩
  have h₀ := ENNReal.toReal_mono hv.ne_top (eLpNorm_mono_ae hF hnorm)
  have h₁ := real_l2_add_bound ((hg.const_mul a).add (hh.const_mul b)) (hk.const_mul c)
  have h₂ := real_l2_add_bound (hg.const_mul a) (hh.const_mul b)
  rw [real_l2_nonneg_scale μ k hc] at h₁
  rw [real_l2_nonneg_scale μ g ha, real_l2_nonneg_scale μ h hb] at h₂
  simp only [Pi.add_apply] at h₁
  exact h₀.trans (h₁.trans (add_le_add h₂ le_rfl))

end CircleDomainRigidity

end

end OAI
