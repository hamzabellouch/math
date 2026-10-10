import OAI.Analysis.LipschitzHilbert.Fourier.FiniteLineCells
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! The martingale of actual nested line-cell averages. -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace LipschitzHilbert.FiniteLineGrid

theorem measurable_index (g : FiniteLineGrid) (n : ℕ) : Measurable (g.index n) :=
  measurable_to_countable' (g.measurable_index_fiber n)

private def nextParent (g : FiniteLineGrid) (n : ℕ)
    (i : Fin (g.branching ^ g.depth)) : Fin (g.branching ^ g.depth) :=
  if n < g.depth then g.parent i else i

private theorem index_nextParent (g : FiniteLineGrid) (n : ℕ) :
    g.index n = g.nextParent n ∘ g.index (n + 1) := by
  funext x
  by_cases hn : n < g.depth
  · simpa only [nextParent, ite_eq_left hn, Function.comp_apply] using g.index_parent hn x
  · have hdn : g.depth ≤ n := le_of_not_gt hn
    simp only [nextParent, ite_eq_right hn, Function.comp_apply, index,
      Nat.min_eq_right hdn, Nat.min_eq_right (hdn.trans (Nat.le_succ n))]

/-- At level `n`, the sigma algebra consists precisely of unions of
the concrete mesh-index fibers. The grid is frozen after its final depth. -/
def filtration (g : FiniteLineGrid) : Filtration ℕ (inferInstance : MeasurableSpace ℝ) where
  seq n := MeasurableSpace.comap (g.index n) inferInstance
  mono' := monotone_nat_of_le_succ fun n => by
    rw [g.index_nextParent n, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_of_countable (g.nextParent n)).comap_le
  le' n := (g.measurable_index n).comap_le

def average (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  μ[f | g.filtration n]

theorem average_martingale (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) : Martingale (g.average μ f) g.filtration μ :=
  martingale_condExp f g.filtration μ

theorem average_memLp (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : MemLp f 2 μ) (n : ℕ) : MemLp (g.average μ f n) 2 μ :=
  hf.condExp (by norm_num)

theorem average_constant (g : FiniteLineGrid) (μ : Measure ℝ) (f : ℝ → ℝ)
    (n : ℕ) {x y : ℝ} (hxy : g.index n x = g.index n y) :
    g.average μ f n x = g.average μ f n y := by
  exact (show StronglyMeasurable[g.filtration n] (g.average μ f n) from
    stronglyMeasurable_condExp).factorsThrough hxy

/-- Conditional expectation is the actual integral average on every
positive-measure index fiber, pointwise for its canonical representative. -/
theorem average_eq_fiber_mean (g : FiniteLineGrid) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) (n : ℕ) (x : ℝ)
    (hpos : μ.real {y | g.index n y = g.index n x} ≠ 0) :
    g.average μ f n x =
      (∫ y in {y | g.index n y = g.index n x}, f y ∂μ) /
        μ.real {y | g.index n y = g.index n x} := by
  let s := {y | g.index n y = g.index n x}
  have hs : MeasurableSet[g.filtration n] s :=
    (comap_measurable (g.index n)) (measurableSet_singleton _)
  have hsambient : MeasurableSet s := (g.filtration.le n) _ hs
  apply (eq_div_iff hpos).mpr
  calc
    g.average μ f n x * μ.real s = ∫ y in s, g.average μ f n x ∂μ := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ = ∫ y in s, g.average μ f n y ∂μ := by
      apply setIntegral_congr_fun hsambient
      intro y hy
      exact g.average_constant μ f n hy.symm
    _ = ∫ y in s, f y ∂μ := setIntegral_condExp (g.filtration.le n) hf hs

def lineMeasure (g : FiniteLineGrid) : Measure ℝ := volume.restrict g.root

instance lineMeasure_finite (g : FiniteLineGrid) : IsFiniteMeasure g.lineMeasure := ⟨by
  change (volume.restrict g.root) Set.univ < ∞
  rw [Measure.restrict_apply_univ, root, Real.volume_Ico]
  exact ENNReal.ofReal_lt_top⟩

theorem lineMeasure_fiber (g : FiniteLineGrid) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level) :
    g.lineMeasure {x | (g.index level x).val = i} = ENNReal.ofReal (g.meshWidth level) := by
  rw [lineMeasure, Measure.restrict_apply]
  · have heq : {x | (g.index level x).val = i} ∩ g.root = g.cell level i := by
      rw [inter_comm]
      exact g.index_fiber_inter_root hl hi
    rw [heq, cell, Real.volume_Ico]
    congr 1
    ring
  · exact ((measurable_of_countable (fun j : Fin (g.branching ^ g.depth) => j.val)).comp
      (g.measurable_index level)) (measurableSet_singleton i)

/-- On a nonempty mesh interval, the canonical dyadic conditional
expectation is exactly the usual Lebesgue average over that interval. -/
theorem average_eq_cell_mean (g : FiniteLineGrid) (f : ℝ → ℝ)
    (hf : Integrable f g.lineMeasure) {level i : ℕ}
    (hl : level ≤ g.depth) (hi : i < g.branching ^ level)
    {x : ℝ} (hx : x ∈ g.cell level i) :
    g.average g.lineMeasure f level x =
      (∫ y in g.cell level i, f y) / g.meshWidth level := by
  have hix : (g.index level x).val = i :=
    (g.index_eq_iff_mem_cell hl (g.cell_subset_root level hi hx) i).mpr hx
  have hfiber : {y | g.index level y = g.index level x} =
      {y | (g.index level y).val = i} := by
    ext y
    simp only [Fin.ext_iff, hix, Set.mem_ofPred_eq]
  have hmass : g.lineMeasure.real {y | g.index level y = g.index level x} =
      g.meshWidth level := by
    rw [measureReal_def, hfiber, g.lineMeasure_fiber hl hi,
      ENNReal.toReal_ofReal (g.meshWidth_pos level).le]
  rw [g.average_eq_fiber_mean g.lineMeasure f hf level x
    (by rw [hmass]; exact (g.meshWidth_pos level).ne'), hmass]
  congr 1
  rw [lineMeasure, Measure.restrict_restrict (g.measurable_index_fiber level _)]
  congr 1
  rw [hfiber, inter_comm]
  congr 1
  exact g.index_fiber_inter_root hl hi

end LipschitzHilbert.FiniteLineGrid

end

end OAI
