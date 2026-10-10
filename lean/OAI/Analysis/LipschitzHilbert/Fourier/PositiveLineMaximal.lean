import OAI.Analysis.LipschitzHilbert.Estimates.RankedMaximal
import OAI.Analysis.LipschitzHilbert.Estimates.DyadicSquareWeakL1
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Positive line maximal functions. Extended integrals give pointwise
monotonicity, including on exceptional lines, which is needed by the
finite rectangle removal algorithm. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace LipschitzHilbert.DyadicLineGrid

abbrev LineCellIndex := ℤ × ℤ

def positiveGridLine (q : ℤ) (f : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  rankedMaximal volume (fun p : LineCellIndex => cell q p.1 p.2) f

theorem positiveGridLine_weak_L1 (q : ℤ) (f : ℝ → ℝ≥0∞)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    volume {x | t < positiveGridLine q f x} ≤ t⁻¹ * ∫⁻ x, f x := by
  exact rankedMaximal_weak_L1 volume (fun p : LineCellIndex => cell q p.1 p.2)
    (fun p => p.1) (fun p => cell_measurable q p.1 p.2)
    (fun p => by rw [cell_volume]; exact ne_of_gt (ENNReal.ofReal_pos.mpr (scale_pos _)))
    (fun p => by rw [cell_volume]; exact ENNReal.ofReal_ne_top)
    (fun i j hij hint => cell_subset_of_intersect hij (by simpa only [inter_comm] using hint))
    f t ht htop

def positiveGridHorizontal (q : ℤ) (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  positiveGridLine q (fun x => f (x,z.2)) z.1

theorem positiveGridHorizontal_measurable (q : ℤ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (positiveGridHorizontal q f) := by
  change Measurable (fun z : ℝ × ℝ => ⨆ p : LineCellIndex,
    (cell q p.1 p.2).indicator (fun _ =>
      (∫⁻ x in cell q p.1 p.2, f (x,z.2)) / volume (cell q p.1 p.2)) z.1)
  apply Measurable.iSup
  intro p
  have hm : Measurable (fun z : ℝ × ℝ =>
      (∫⁻ x in cell q p.1 p.2, f (x,z.2)) / volume (cell q p.1 p.2)) :=
    (hf.lintegral_prod_left'.comp measurable_snd).div_const _
  convert hm.indicator ((cell_measurable q p.1 p.2).preimage measurable_fst) using 1
  ext z
  by_cases hz : z.1 ∈ cell q p.1 p.2 <;> simp [hz]

theorem positiveGridHorizontal_weak_L1 (q : ℤ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    (volume.prod volume) {z | t < positiveGridHorizontal q f z} ≤
      t⁻¹ * ∫⁻ z, f z ∂volume.prod volume := by
  rw [Measure.prod_apply_symm (measurableSet_lt measurable_const (positiveGridHorizontal_measurable q hf))]
  calc
    _ ≤ ∫⁻ y, t⁻¹ * ∫⁻ x, f (x,y) := lintegral_mono (fun y => positiveGridLine_weak_L1 q (fun x => f (x,y)) t ht htop)
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr ht),lintegral_prod_symm _ hf.aemeasurable]

def positiveHorizontal (f : ℝ × ℝ → ℝ≥0∞) (z : ℝ × ℝ) : ℝ≥0∞ :=
  Finset.univ.sup (fun q : GridChoice => positiveGridHorizontal q.val f z)

theorem positiveHorizontal_measurable {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    Measurable (positiveHorizontal f) := by
  have h (s : Finset GridChoice) : Measurable (fun z => s.sup (fun q => positiveGridHorizontal q.val f z)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert q s hqs ih => simpa only [Finset.sup_insert] using (positiveGridHorizontal_measurable q.val hf).max ih
  exact h Finset.univ

theorem positiveHorizontal_mono {f g : ℝ × ℝ → ℝ≥0∞} (h : f ≤ g) :
    positiveHorizontal f ≤ positiveHorizontal g := by
  intro z
  apply Finset.sup_mono_fun
  intro q _
  exact rankedMaximal_mono volume _ (fun x => h (x,z.2)) z.1

theorem positiveHorizontal_weak_L1 {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f)
    (t : ℝ≥0∞) (ht : t ≠ 0) (htop : t ≠ ∞) :
    (volume.prod volume) {z | t < positiveHorizontal f z} ≤
      3 * t⁻¹ * ∫⁻ z, f z ∂volume.prod volume := by
  have hsub : {z | t < positiveHorizontal f z} ⊆
      ⋃ q : GridChoice, {z | t < positiveGridHorizontal q.val f z} := by
    intro z hz
    change t < Finset.univ.sup (fun q : GridChoice => positiveGridHorizontal q.val f z) at hz
    obtain ⟨q,_,hq⟩ := Finset.lt_sup_iff.mp hz
    exact mem_iUnion.mpr ⟨q,hq⟩
  calc
    _ ≤ (volume.prod volume) (⋃ q : GridChoice, {z | t < positiveGridHorizontal q.val f z}) := measure_mono hsub
    _ ≤ ∑ q : GridChoice, (volume.prod volume) {z | t < positiveGridHorizontal q.val f z} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _q : GridChoice, t⁻¹ * ∫⁻ z, f z ∂volume.prod volume :=
      Finset.sum_le_sum (fun q _ => positiveGridHorizontal_weak_L1 q.val hf t ht htop)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,gridChoice_card,nsmul_eq_mul]; norm_num; rw [mul_assoc]

end LipschitzHilbert.DyadicLineGrid

end

end OAI
