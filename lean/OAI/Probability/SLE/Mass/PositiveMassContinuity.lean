import OAI.Probability.SLE.Loewner.StoppedInversePaths

namespace OAI

/-! Positive compact tests determine continuity of every real compact test. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped Topology NNReal ENNReal CompactlySupported

namespace SLEExactGauge

lemma PositiveMassPaths.continuous_real_tests
    {N : ℝ≥0 → Measure upperHalfPlane} {ν : Measure upperHalfPlane}
    (h : PositiveMassPaths N ν) (f : C_c(upperHalfPlane,ℝ)) :
    Continuous (fun t => ∫ z, f z ∂N t) := by
  let fp : C_c(upperHalfPlane,ℝ) := f ⊔ 0
  let fm : C_c(upperHalfPlane,ℝ) := -f ⊔ 0
  have hp : ∀ z, 0 ≤ fp z := fun z => le_max_right _ _
  have hm : ∀ z, 0 ≤ fm z := fun z => le_max_right _ _
  have he (t : ℝ≥0) : (∫ z, f z ∂N t) = (∫ z, fp z ∂N t)-(∫ z, fm z ∂N t) := by
    let := (h.radon t).2
    rw [← integral_sub fp.integrable fm.integrable]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by
      change f z = max (f z) 0-max (-f z) 0
      rcases le_total 0 (f z) with hz | hz
      · rw [max_eq_left hz,max_eq_right (neg_nonpos.mpr hz)]; ring
      · rw [max_eq_right hz,max_eq_left (neg_nonneg.mpr hz)]; ring)
  have hcont : Continuous (fun t => (∫ z, fp z ∂N t)-(∫ z, fm z ∂N t)) :=
    (h.continuous_tests fp hp).sub (h.continuous_tests fm hm)
  exact hcont.congr (fun t => (he t).symm)

end SLEExactGauge

end

end OAI
