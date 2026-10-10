import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem diagonal_bin_mass_le {ι : Type*} [Countable ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (I : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise fun i j => Disjoint (I i) (I j)) (w : ℝ)
    (hdiam : ∀ i x, x ∈ I i → ∀ y, y ∈ I i → |x-y| ≤ w) :
    (∑' i, (μ (I i))^2) ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have hd : Pairwise fun i j => Disjoint (I i ×ˢ I i) (I j ×ˢ I j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.1 hj.1
  calc
    (∑' i, (μ (I i))^2) = ∑' i, (μ.prod μ) (I i ×ˢ I i) := by
      simp only [Measure.prod_prod, pow_two]
    _ = (μ.prod μ) (⋃ i, I i ×ˢ I i) :=
      (measure_iUnion hd (fun i => (hmeas i).prod (hmeas i))).symm
    _ ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
      apply measure_mono
      intro z hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact hdiam i z.1 hi.1 z.2 hi.2

def realBin (w : ℝ) (j : ℤ) : Set ℝ :=
  Set.Ico ((j : ℝ)*w) (((j+1 : ℤ) : ℝ)*w)

theorem realBin_measurable (w : ℝ) (j : ℤ) : MeasurableSet (realBin w j) :=
  measurableSet_Ico

theorem realBin_disjoint {w : ℝ} (hw : 0 < w) :
    Pairwise fun i j => Disjoint (realBin w i) (realBin w j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : ((i+1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxj.1.trans' hm)) hxi.2
  · have hc : ((j+1 : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxi.1.trans' hm)) hxj.2

theorem realBin_diameter (w : ℝ) (j : ℤ) {x y : ℝ}
    (hx : x ∈ realBin w j) (hy : y ∈ realBin w j) : |x-y| ≤ w := by
  simp only [realBin, Set.mem_Ico, Int.cast_add, Int.cast_one] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith

theorem real_bin_collision_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∑' j : ℤ, (μ (realBin w j))^2) ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} :=
  diagonal_bin_mass_le μ (realBin w) (realBin_measurable w) (realBin_disjoint hw) w
    (fun j _ hx _ hy => realBin_diameter w j hx hy)

end PlanarFalconer

end OAI
