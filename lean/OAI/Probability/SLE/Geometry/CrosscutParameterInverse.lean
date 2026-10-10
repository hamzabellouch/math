import OAI.Probability.SLE.Geometry.CompactifiedCrosscut
import OAI.Probability.SLE.Geometry.DiskUpperStraightening
import OAI.Probability.SLE.Geometry.HalfPlaneCayleyInverse

namespace OAI

/-! The compactification parameter exactly matches the prescribed vertical ray. -/
noncomputable section
open Set Complex
open scoped NNReal

namespace SLEExactGauge

def rayDiskParameter (t : ℝ≥0) : ℝ := (t:ℝ)/(1+(t:ℝ))

lemma rayDiskParameter_mem (t : ℝ≥0) : rayDiskParameter t ∈ Ico 0 1 := by
  have hd : 0 < 1+(t:ℝ) := by positivity
  refine ⟨div_nonneg t.property hd.le,?_⟩
  exact (div_lt_one hd).mpr (by linarith)

lemma crosscutParameter_rayDiskParameter (t : ℝ≥0) :
    crosscutParameter (rayDiskParameter t)=t := by
  apply NNReal.coe_injective
  have hs := rayDiskParameter_mem t
  have hval : (crosscutParameter (rayDiskParameter t) : ℝ) =
      rayDiskParameter t / (1-rayDiskParameter t) :=
    Real.coe_toNNReal _ (div_nonneg hs.1 (sub_pos.mpr hs.2).le)
  rw [hval]
  dsimp [rayDiskParameter]
  have hd : (1+(t:ℝ)) ≠ 0 := by positivity
  field_simp [hd]
  ring

lemma compactifiedCrosscut_rayDiskParameter (β : ℝ≥0 → ℂ) (t : ℝ≥0) :
    compactifiedCrosscut β (rayDiskParameter t)=halfPlaneCayley (β t) := by
  rw [compactifiedCrosscut_eq β (rayDiskParameter_mem t).2,
    crosscutParameter_rayDiskParameter]

lemma diskDiameter_rayDiskParameter (t : ℝ≥0) :
    diskDiameter (rayDiskParameter t)=halfPlaneCayley ((t:ℂ)*I) := by
  have hd : (1+(t:ℂ)) ≠ 0 := by
    exact_mod_cast (show (1+(t:ℝ)) ≠ 0 by positivity)
  have hi : (t:ℂ)*I+I ≠ 0 := by
    have hh : (t:ℂ)*I+I=(1+(t:ℂ))*I := by ring
    rw [hh]
    exact mul_ne_zero hd Complex.I_ne_zero
  have hr : 2*((t:ℝ)/(1+(t:ℝ)))-1=((t:ℝ)-1)/(1+(t:ℝ)) := by
    have h : (1+(t:ℝ)) ≠ 0 := by positivity
    field_simp
    ring
  unfold diskDiameter rayDiskParameter halfPlaneCayley
  rw [hr]
  push_cast
  apply (div_eq_div_iff hd hi).mpr
  ring

end SLEExactGauge

end

end OAI
