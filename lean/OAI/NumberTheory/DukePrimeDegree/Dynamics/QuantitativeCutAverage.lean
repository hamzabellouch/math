import OAI.NumberTheory.DukePrimeDegree.Entropy.SummablePartitionBoundaries

namespace OAI

/-! # Quantitative selection of a real cut

A nonnegative cost with bounded total integral has a cut in any given
interval with cost at most twice the interval average. This will control
all dyadic boundary widths at once.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

theorem exists_cut_cost_le
    (F : ℝ → ℝ≥0∞) {C a b : ℝ} (hC : 0 < C) (hab : a < b)
    (hI : (∫⁻ r, F r) ≤ ENNReal.ofReal C) :
    ∃ r ∈ Ioo a b, F r ≤ ENNReal.ofReal (2*C/(b-a)) := by
  by_contra h
  have hall : ∀ r ∈ Ioo a b, ENNReal.ofReal (2*C/(b-a)) ≤ F r := by
    intro r hr
    exact (lt_of_not_ge (fun hle => h ⟨r,hr,hle⟩)).le
  have hlower : ENNReal.ofReal (2*C/(b-a))*volume (Ioo a b) ≤
      ∫⁻ r in Ioo a b, F r := by
    rw [← setLIntegral_const]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact hall r hr
  have hbound : ENNReal.ofReal (2*C) ≤ ENNReal.ofReal C := by
    have he : ENNReal.ofReal (2*C/(b-a))*volume (Ioo a b) = ENNReal.ofReal (2*C) := by
      rw [Real.volume_Ioo,←ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp [(sub_pos.mpr hab).ne']
    rw [he] at hlower
    exact hlower.trans ((lintegral_mono' Measure.restrict_le_self le_rfl).trans hI)
  have := (ENNReal.ofReal_le_ofReal_iff hC.le).mp hbound
  linarith

end DukePrimeDegree

end

end OAI
