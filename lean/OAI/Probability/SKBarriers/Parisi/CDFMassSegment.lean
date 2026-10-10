import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFOverlap

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

def cdfMassSegment (α γ : ℝ → ℝ) (θ s : ℝ) : ℝ := α s+θ*(γ s-α s)

theorem cdfMassSegment_eq (α γ : ℝ → ℝ) (θ s : ℝ) :
    cdfMassSegment α γ θ s=(1-θ)*α s+θ*γ s := by unfold cdfMassSegment; ring

@[simp] theorem cdfMassSegment_zero (α γ : ℝ → ℝ) : cdfMassSegment α γ 0=α := by
  funext s
  simp [cdfMassSegment]

def cdfMassSegmentStieltjes (α γ : StieltjesFunction ℝ) (θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) :
    StieltjesFunction ℝ where
  toFun := cdfMassSegment α γ θ
  mono' := by
    intro s t hst
    rw [cdfMassSegment_eq,cdfMassSegment_eq]
    exact add_le_add (mul_le_mul_of_nonneg_left (α.mono hst) (sub_nonneg.mpr hθ.2))
      (mul_le_mul_of_nonneg_left (γ.mono hst) hθ.1)
  right_continuous' := by
    intro s
    exact (α.right_continuous s).add (((γ.right_continuous s).sub (α.right_continuous s)).const_mul θ)

theorem cdfMassSegment_bounds {α γ : ℝ → ℝ}
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hg : ∀ z, γ z∈Icc (0:ℝ) 1)
    {θ : ℝ} (ht : θ∈Icc (0:ℝ) 1) (s : ℝ) : cdfMassSegment α γ θ s∈Icc (0:ℝ) 1 := by
  rw [cdfMassSegment_eq]
  constructor
  · exact add_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (ha s).1) (mul_nonneg ht.1 (hg s).1)
  · have H₁ := mul_le_mul_of_nonneg_left (ha s).2 (sub_nonneg.mpr ht.2)
    have H₂ := mul_le_mul_of_nonneg_left (hg s).2 ht.1
    linarith

theorem cdfMassSegment_one {α γ : ℝ → ℝ} (ha : α 1=1) (hg : γ 1=1) (θ : ℝ) :
    cdfMassSegment α γ θ 1=1 := by simp [cdfMassSegment,ha,hg]

theorem cdfMassSegment_distance (α γ : ℝ → ℝ) {θ : ℝ} (hθ : 0≤θ) :
    cdfDistance (cdfMassSegment α γ θ) α=θ*cdfDistance γ α := by
  unfold cdfDistance
  simp only [cdfMassSegment,add_sub_cancel_left,abs_mul,abs_of_nonneg hθ,integral_const_mul]

theorem cdfMassSegment_integral (α γ f : ℝ → ℝ) (θ : ℝ) :
    (∫ s in Icc (0:ℝ) 1, (cdfMassSegment α γ θ s-α s)*f s)=
      θ*∫ s in Icc (0:ℝ) 1, (γ s-α s)*f s := by
  simp only [cdfMassSegment,add_sub_cancel_left,mul_assoc,integral_const_mul]

end SK.Analytic

end
end

end OAI
