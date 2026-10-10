import Mathlib
import OAI.Probability.SKSupport.Moments.StripSquareMoment

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
variable {Ω : Type*} [MeasurableSpace Ω]

theorem diffusion_uniqueness (W : BrownianSystem Ω) (γ : OrderParameter)
    {X : ℝ≥0 → Ω → ℝ} (hX : IsDiffusion W γ X) :
    ∀ᵐ ω ∂W.law, ∀ t : ℝ≥0, t ≤ 1 → X t ω = diffusion W γ t ω := by
  let ℱ := Filtration.natural W.B (fun t => (W.measurable t).stronglyMeasurable)
  have hZ : IsProgressive ℱ (fun t ω => X t ω-W.driver t ω) := hX.1.sub W.driver_progressive
  filter_upwards [hX.2,W.driver_indistinguishable] with ω hω hB
  have hbefore (t : ℝ≥0) (ht : (t:ℝ) < 1) : X t ω = diffusion W γ t ω := by
    let T : Time := ⟨t,⟨t.coe_nonneg,ht⟩⟩
    let b := stripDrift W γ T
    have he := b.correction_unique_on ℱ W.driver_progressive hZ t ω
    have hfix : ∀ s ≤ t, X s ω-W.driver s ω =
        timePrimitive (b.action W.driver (fun r ω => X r ω-W.driver r ω)) s ω := by
      intro s hs
      have hst : (s:ℝ) ≤ t := hs
      have hs1 : (s:ℝ) ≤ 1 := hst.trans ht.le
      have hi := hω.2.2 (s:ℝ) ⟨s.coe_nonneg,hs1⟩
      simp only [Real.toNNReal_coe] at hi
      rw [hi,hB s,add_sub_cancel_left]
      unfold timePrimitive BoundedLipschitzDrift.action
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le s.coe_nonneg] at hr
      have hrt : ((Real.toNNReal r):ℝ) ≤ (T:ℝ) := by rw [Real.coe_toNNReal _ hr.1]; exact hr.2.trans hst
      dsimp only
      rw [add_sub_cancel,stripDrift_eq W γ T ⟨(Real.toNNReal r).coe_nonneg,hrt⟩,
        Real.coe_toNNReal _ hr.1]
    have hc := he hfix t le_rfl
    rw [diffusion_eq_strip W γ T t le_rfl]
    change X t ω = W.driver t ω+b.correction W.driver t ω
    rw [hc]
    ring
  intro t ht
  by_cases ht1 : (t:ℝ) < 1
  · exact hbefore t ht1
  have he : t=1 := le_antisymm ht (by exact_mod_cast not_lt.mp ht1)
  subst t
  have hi := hω.2.2 1 ⟨by norm_num,le_rfl⟩
  simp only [Real.toNNReal_one] at hi
  rw [hi,diffusion,hB 1]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)] at hr
  by_cases hr1 : r<1
  · have hrr : ((Real.toNNReal r):ℝ) < 1 := by rw [Real.coe_toNNReal _ hr.1]; exact hr1
    dsimp only
    rw [rawFeedback_eq W γ _ hrr,Real.coe_toNNReal _ hr.1,
      hbefore (Real.toNNReal r) hrr,diffusion_eq_raw W γ _ hrr]
  · have hr_eq : r=1 := le_antisymm hr.2 (not_lt.mp hr1)
    subst r
    simp [extend]

end ZeroTemperatureSK

end
end

end OAI
