import OAI.Probability.SLE.Loewner.InitialSubarcReparam

namespace OAI

/-! Continuous rescaling onto a fixed initial parameter interval. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

def subarcParameter (b : unitInterval) (hb : b≠0) (t : unitInterval) : unitInterval :=
  ⟨min ((t:ℝ)/(b:ℝ)) 1,
    le_min (div_nonneg t.property.1 (unitInterval.pos_iff_ne_zero.mpr hb).le)
      zero_le_one,min_le_right _ _⟩

lemma subarcParameter_continuous (b : unitInterval) (hb : b≠0) :
    Continuous (subarcParameter b hb) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.div_const (b:ℝ)).min continuous_const

lemma subarcParameter_mul (b : unitInterval) (hb : b≠0) (t : unitInterval) :
    b*subarcParameter b hb t=min t b := by
  have hbpos : 0<(b:ℝ) := unitInterval.pos_iff_ne_zero.mpr hb
  apply Subtype.ext
  change (b:ℝ)*min ((t:ℝ)/(b:ℝ)) 1=min (t:ℝ) (b:ℝ)
  rw [mul_min_of_nonneg _ _ hbpos.le,mul_div_cancel₀ _ hbpos.ne',mul_one]

@[simp] lemma subarcParameter_self (b : unitInterval) (hb : b≠0) :
    subarcParameter b hb b=1 := by
  have hbpos : 0<(b:ℝ) := unitInterval.pos_iff_ne_zero.mpr hb
  apply Subtype.ext
  change min ((b:ℝ)/(b:ℝ)) 1=1
  rw [div_self hbpos.ne',min_self]

lemma subarcParameter_mul_of_le (b : unitInterval) (hb : b≠0)
    {t : unitInterval} (ht : t≤b) : b*subarcParameter b hb t=t := by
  rw [subarcParameter_mul,min_eq_left ht]

end SLEExactGauge

end

end OAI
