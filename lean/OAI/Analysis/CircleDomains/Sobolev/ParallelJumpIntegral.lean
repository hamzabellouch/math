import OAI.Analysis.CircleDomains.Topology.ParallelDiskTolls
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! Integrating the two endpoint errors over the transverse disk projections
produces the exact factor four in the planar distributional estimate. -/
open Set Function MeasureTheory
namespace CircleDomainRigidity

 theorem integral_bound_of_parallel_disk_errors
    {I : Type*} [Fintype I] (c : I → ℂ) (r A : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (C : ℝ) {f g : ℝ × ℝ → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hline : ∀ᵐ y : ℝ,
      |(∫ x : ℝ, f (x, y)) + (∫ x : ℝ, g (x, y))| ≤
        2 * C * ∑ i, (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y) :
    |(∫ p, f p) + (∫ p, g p)| ≤ 4 * C * ∑ i, r i * A i := by
  have hf' : Integrable f ((volume : Measure ℝ).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hf
  have hg' : Integrable g ((volume : Measure ℝ).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hg
  have hi := hf'.integral_prod_right.add hg'.integral_prod_right
  have hc (i : I) : Integrable
      ((Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ : ℝ => A i)) :=
    (integrableOn_const measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hcost := (integrable_finsetSum Finset.univ (fun i _ => hc i)).const_mul (2 * C)
  calc
    _ = |∫ y : ℝ, (∫ x : ℝ, f (x, y)) + (∫ x : ℝ, g (x, y))| := by
      rw [integral_add hf'.integral_prod_right hg'.integral_prod_right,
        ← integral_prod_symm _ hf', ← integral_prod_symm _ hg', ← Measure.volume_eq_prod]
    _ ≤ ∫ y : ℝ, |(∫ x : ℝ, f (x, y)) + (∫ x : ℝ, g (x, y))| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ y : ℝ, 2 * C * ∑ i,
        (Icc ((c i).im - r i) ((c i).im + r i)).indicator (fun _ => A i) y :=
      integral_mono_ae hi.abs hcost hline
    _ = 4 * C * ∑ i, r i * A i := by
      rw [integral_const_mul, integral_parallel_disk_tolls c r A hr]
      have he : (∑ i, 2 * r i * A i) = 2 * ∑ i, r i * A i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [he]
      ring

end CircleDomainRigidity

end OAI
