import OAI.NumberTheory.DukePrimeDegree.Geometry.LeafLusinGoodSet
import Mathlib.Dynamics.BirkhoffSum.Basic

namespace OAI

/-!
# The finite maximal ergodic inequality

The maximal recurrence estimate used in EKL (2006), Section 4.3, follows
from this elementary finite Hopf inequality. The running maximum is built
recursively, so its integrability and its coboundary bound require no
pointwise ergodic theorem.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree

def positiveRunningSum {Y : Type*} (T : Y → Y) (f : Y → ℝ) : ℕ → Y → ℝ
  | 0 => 0
  | n + 1 => fun x => max 0 (f x + positiveRunningSum T f n (T x))

lemma positiveRunningSum_nonneg {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (n : ℕ) (x : Y) : 0 ≤ positiveRunningSum T f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

lemma positiveRunningSum_mono {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (x : Y) : Monotone (fun n => positiveRunningSum T f n x) := by
  suffices h : ∀ n x, positiveRunningSum T f n x ≤ positiveRunningSum T f (n + 1) x
    from monotone_nat_of_le_succ (fun n => h n x)
  intro n
  induction n with
  | zero => exact fun x => positiveRunningSum_nonneg T f 1 x
  | succ n ih =>
    intro x
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

lemma birkhoffSum_le_positiveRunningSum {Y : Type*} (T : Y → Y) (f : Y → ℝ)
    (n : ℕ) (x : Y) : birkhoffSum T f n x ≤ positiveRunningSum T f n x := by
  induction n generalizing x with
  | zero => simp [positiveRunningSum]
  | succ n ih =>
    rw [birkhoffSum_succ_apply']
    exact (add_le_add le_rfl (ih (T x))).trans (le_max_right _ _)

lemma measurable_positiveRunningSum {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} {f : Y → ℝ} (hT : Measurable T) (hf : Measurable f) (n : ℕ) :
    Measurable (positiveRunningSum T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact measurable_const.max (hf.add (ih.comp hT))

lemma integrable_positiveRunningSum {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {T : Y → Y} {f : Y → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (n : ℕ) :
    Integrable (positiveRunningSum T f n) μ := by
  induction n with
  | zero => exact integrable_zero _ _ _
  | succ n ih =>
    exact (integrable_zero _ _ _).sup (hf.add (hT.integrable_comp_of_integrable ih))

/-- A finite running maximum has nonnegative signed mass on its positive set. -/
theorem finite_hopf_maximal {Y : Type*} [MeasurableSpace Y]
    {μ : Measure Y} {T : Y → Y} {f : Y → ℝ}
    (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (hfmeas : Measurable f) (n : ℕ) :
    0 ≤ ∫ x in {x | 0 < positiveRunningSum T f n x}, f x ∂μ := by
  let m := positiveRunningSum T f n
  let E := {x | 0 < m x}
  have hm : Integrable m μ := integrable_positiveRunningSum hT hf n
  have hmmeas : Measurable m := measurable_positiveRunningSum hT.measurable hfmeas n
  have hE : MeasurableSet E := measurableSet_lt measurable_const hmmeas
  have hpoint (x : Y) : m x - m (T x) ≤ E.indicator f x := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      have hle := positiveRunningSum_mono T f x (Nat.le_succ n)
      change m x ≤ max 0 (f x + m (T x)) at hle
      have hpos : 0 < m x := hx
      have hle' := (le_max_iff.mp hle).resolve_left (not_le_of_gt hpos)
      linarith
    · rw [indicator_of_notMem hx]
      have hz : m x = 0 := le_antisymm (le_of_not_gt hx)
        (positiveRunningSum_nonneg T f n x)
      rw [hz]
      linarith [positiveRunningSum_nonneg T f n (T x)]
  have hcomp : ∫ x, m (T x) ∂μ = ∫ x, m x ∂μ := by
    have hmap : AEStronglyMeasurable m (μ.map T) := by
      simpa only [hT.map_eq] using hm.aestronglyMeasurable
    exact (integral_map hT.measurable.aemeasurable hmap).symm.trans
      (by rw [hT.map_eq])
  have hle := integral_mono (hm.sub (hT.integrable_comp_of_integrable hm))
    (hf.indicator hE) hpoint
  simp only [Pi.sub_apply, Function.comp_apply] at hle
  have hmt : Integrable (fun x => m (T x)) μ := hT.integrable_comp_of_integrable hm
  rw [integral_sub hm hmt, hcomp, sub_self,
    integral_indicator hE] at hle
  exact hle

end DukePrimeDegree

end

end OAI
