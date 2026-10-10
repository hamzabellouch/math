import OAI.Geometry.Relativity.CKS.CKSCollarCoordinates

namespace OAI

noncomputable section
namespace CKSBending
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff

def primitive (a : ℝ) (q : ℝ → ℝ) (r : ℝ) : ℝ := ∫ s in a..r, q s

lemma positive_uIcc {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : uIcc a r ⊆ Ioi 0 := by
  intro s hs
  exact lt_of_lt_of_le (lt_min ha hr) hs.1

lemma positive_interval_integrable {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : IntervalIntegrable q volume a r :=
  (hq.mono (positive_uIcc ha hr)).intervalIntegrable

lemma primitive_hasDerivAt {q : ℝ → ℝ} (hq : ContinuousOn q (Ioi 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) : HasDerivAt (primitive a q) (q r) r := by
  exact intervalIntegral.integral_hasDerivAt_right (positive_interval_integrable hq ha hr)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hq r hr)
    (hq.continuousAt (isOpen_Ioi.mem_nhds hr))

lemma primitive_smooth {q : ℝ → ℝ} (hq : ContDiffOn ℝ ∞ q (Ioi 0))
    {a : ℝ} (ha : 0 < a) : ContDiffOn ℝ ∞ (primitive a q) (Ioi 0) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  constructor
  · intro r hr
    exact (primitive_hasDerivAt hq.continuousOn ha hr).differentiableAt.differentiableWithinAt
  · exact hq.congr (fun r hr => (primitive_hasDerivAt hq.continuousOn ha hr).deriv)

def paddingDensity (r : ℝ) : ℝ := 1/(r * Real.sqrt r)
lemma paddingDensity_smooth : ContDiffOn ℝ ∞ paddingDensity (Ioi 0) := by
  exact contDiffOn_const.div (contDiffOn_id.mul (contDiffOn_id.sqrt (fun r hr => ne_of_gt hr)))
    (fun r hr => mul_ne_zero (ne_of_gt hr) (Real.sqrt_ne_zero'.mpr hr))
lemma paddingDensity_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ paddingDensity r := by
  unfold paddingDensity
  positivity

lemma padding_antideriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s : ℝ => -2 / Real.sqrt s) (paddingDensity r) r := by
  have hs := Real.hasDerivAt_sqrt hr.ne'
  have hh := (hasDerivAt_const r (-2:ℝ)).div hs (Real.sqrt_ne_zero'.mpr hr)
  convert! hh using 1
  unfold paddingDensity
  have he := Real.sq_sqrt hr.le
  field_simp
  nlinarith [Real.sqrt_pos.mpr hr]

lemma paddingDensity_integral {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    primitive a paddingDensity r = 2/Real.sqrt a - 2/Real.sqrt r := by
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => padding_antideriv (positive_uIcc ha hr hs))
    (positive_interval_integrable paddingDensity_smooth.continuousOn ha hr)
  unfold primitive
  rw [hh]
  ring

end
end CKSBending

end

end OAI
