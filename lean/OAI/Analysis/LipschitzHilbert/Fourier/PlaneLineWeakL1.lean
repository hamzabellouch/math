import OAI.Analysis.LipschitzHilbert.Trees.ThreeGridWeakL1
import OAI.Analysis.LipschitzHilbert.Trees.SourceAxisMaximal

namespace OAI

/-! Weak L1 bounds for actual line averages on the plane, by Fubini. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace LipschitzHilbert.DyadicLineGrid

def horizontalSup (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  threeGridSup (fun x => f (x,z.2)) z.1

theorem horizontalSup_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Measurable (horizontalSup f) := by
  have hq (q : GridChoice) : Measurable (fun z : ℝ × ℝ =>
      allDyadicSup q.val (fun x => f (x,z.2)) z.1) :=
    Measurable.iSup (fun k => (horizontalCellMean_measurable q.val k hf).norm.ennreal_ofReal)
  have h (s : Finset GridChoice) : Measurable (fun z : ℝ × ℝ =>
      s.sup (fun q => allDyadicSup q.val (fun x => f (x,z.2)) z.1)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert q s hqs ih => simpa only [Finset.sup_insert] using (hq q).max ih
  exact h Finset.univ

theorem horizontalSup_weak_L1 {f : ℝ × ℝ → ℝ} (hfm : Measurable f)
    (hf : Integrable f (volume.prod volume)) (t : ℝ) (ht : 0 < t) :
    (volume.prod volume) {z | ENNReal.ofReal t < horizontalSup f z} ≤
      ENNReal.ofReal (3*t⁻¹) * ∫⁻ z, ‖f z‖ₑ ∂volume.prod volume := by
  rw [Measure.prod_apply_symm (measurableSet_lt measurable_const (horizontalSup_measurable hfm))]
  calc
    _ ≤ ∫⁻ y, ENNReal.ofReal (3*t⁻¹) * ∫⁻ x, ‖f (x,y)‖ₑ := by
      apply lintegral_mono_ae
      filter_upwards [hf.prod_left_ae] with y hy
      have h := threeGridSup_weak_L1 hy t ht
      change volume {x | ENNReal.ofReal t < threeGridSup (fun x => f (x,y)) x} ≤ _
      refine h.trans_eq ?_
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 3*t⁻¹),
        show (∫ x, |f (x,y)|) = ∫ x, ‖f (x,y)‖ from rfl,
        ofReal_integral_norm_eq_lintegral_enorm hy]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [lintegral_prod_symm _ hfm.enorm.aemeasurable]

def verticalSup (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ≥0∞ :=
  horizontalSup (f ∘ Prod.swap) z.swap

theorem verticalSup_measurable {f : ℝ × ℝ → ℝ} (hf : Measurable f) :
    Measurable (verticalSup f) :=
  (horizontalSup_measurable (hf.comp measurable_swap)).comp measurable_swap

theorem verticalSup_weak_L1 {f : ℝ × ℝ → ℝ} (hfm : Measurable f)
    (hf : Integrable f (volume.prod volume)) (t : ℝ) (ht : 0 < t) :
    (volume.prod volume) {z | ENNReal.ofReal t < verticalSup f z} ≤
      ENNReal.ofReal (3*t⁻¹) * ∫⁻ z, ‖f z‖ₑ ∂volume.prod volume := by
  have h := horizontalSup_weak_L1 (hfm.comp measurable_swap)
    (Measure.measurePreserving_swap.integrable_comp_of_integrable hf) t ht
  change (volume.prod volume) (Prod.swap ⁻¹' {z | ENNReal.ofReal t < horizontalSup (f ∘ Prod.swap) z}) ≤ _
  have hE : MeasurableSet {z : ℝ × ℝ | ENNReal.ofReal t < horizontalSup (f ∘ Prod.swap) z} :=
    measurableSet_lt measurable_const (horizontalSup_measurable (hfm.comp measurable_swap))
  rw [(Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).measure_preimage hE.nullMeasurableSet]
  refine h.trans_eq ?_
  congr 1
  exact lintegral_prod_swap (fun z => ‖f z‖ₑ)

end LipschitzHilbert.DyadicLineGrid

end

end OAI
