import OAI.Analysis.CircleDomains.Sobolev.RectangleSobolev

namespace OAI

/-! Fubini data for a single rectangle, retaining the actual measurable
predicate and the actual L² density on almost every coordinate line. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem rectangle_ae_slices {a b c d : ℝ} {P : ℝ × ℝ → Prop}
    (hP : MeasurableSet {p | P p})
    (hae : ∀ᵐ p ∂volume.restrict (Icc a b ×ˢ Icc c d), P p) :
    (∀ᵐ y ∂volume.restrict (Icc c d), ∀ᵐ x ∂volume.restrict (Icc a b), P (x,y)) ∧
    (∀ᵐ x ∂volume.restrict (Icc a b), ∀ᵐ y ∂volume.restrict (Icc c d), P (x,y)) := by
  rw [Measure.volume_eq_prod,← Measure.prod_restrict] at hae
  have h := (Measure.ae_prod_iff_ae_ae hP).mp hae
  exact ⟨(Measure.ae_ae_comm hP).mp h,h⟩

 theorem rectangle_L2_line_integrable {P : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hP : MemLp P 2 (volume.restrict (Icc a b ×ˢ Icc c d))) :
    (∀ᵐ y ∂volume.restrict (Icc c d),
      IntervalIntegrable (fun x => P (x,y)) volume a b) ∧
    (∀ᵐ x ∂volume.restrict (Icc a b),
      IntervalIntegrable (fun y => P (x,y)) volume c d) := by
  let : IsFiniteMeasure (volume.restrict (Icc a b ×ˢ Icc c d) : Measure (ℝ × ℝ)) :=
    isFiniteMeasure_restrict.mpr (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have hi := hP.integrable (by norm_num)
  rw [Measure.volume_eq_prod,← Measure.prod_restrict] at hi
  constructor
  · filter_upwards [hi.prod_left_ae] with y hy
    exact intervalIntegrable_iff.mpr ((show IntegrableOn (fun x => P (x,y)) (Icc a b) volume from hy).mono_set
      (by simpa only [uIoc_of_le hab] using Ioc_subset_Icc_self))
  · filter_upwards [hi.prod_right_ae] with x hx
    exact intervalIntegrable_iff.mpr ((show IntegrableOn (fun y => P (x,y)) (Icc c d) volume from hx).mono_set
      (by simpa only [uIoc_of_le hcd] using Ioc_subset_Icc_self))

end CircleDomainRigidity

end

end OAI
