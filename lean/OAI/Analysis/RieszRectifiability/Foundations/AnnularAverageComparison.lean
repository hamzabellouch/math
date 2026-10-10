import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.ExteriorCellMeans
import OAI.Analysis.RieszRectifiability.Kernel.NativeTruncationDecomposition

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem annular_cell_average_comparison {d : ℕ} (n : ℕ) (hn : 1 ≤ n)
    (G M B : ℝ) (μ : Measure (Ambient d)) (hg : GlobalUpperGrowth n G μ)
    (ε r R : ℝ) (hε : 0 < ε) (hr : 0 < r) (hrR : r ≤ R) (hεr : ε < r / 2)
    (f g h : Ambient d → ℝ) (hf : MemLp f 2 μ) (hhg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (hM : 0 ≤ M) (hgM : ∀ y, |g y| ≤ M) (hhM : ∀ y, |h y| ≤ M)
    (a e : Ambient d) (he : ‖e‖ ≤ 1)
    (hgs : ∀ y, g y ≠ 0 → r ≤ dist a y) (hhs : ∀ y, h y ≠ 0 → R ≤ dist a y)
    (A Q : Set (Ambient d)) (hA : MeasurableSet A) (hQ : MeasurableSet Q)
    (hAfin : μ A < ∞) (hQfin : μ Q < ∞) (hApos : 0 < μ.real A) (hQpos : 0 < μ.real Q)
    (hAnear : ∀ x ∈ A, 2 * dist x a ≤ r) (hQnear : ∀ x ∈ Q, 2 * dist x a ≤ R)
    (hfA : (∫ y, f y ^ 2 ∂μ) ≤ B * μ.real A)
    (hfQ : (∫ y, f y ^ 2 ∂μ) ≤ B * μ.real Q)
    (hgQ : (∫ y, g y ^ 2 ∂μ) ≤ B * μ.real Q)
    (D : ℝ≥0)
    (hRiesz : ∀ u : Ambient d → ℝ, MemLp u 2 μ →
      MemLp (truncated n μ ε u) 2 μ ∧
        eLpNorm (truncated n μ ε u) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm u 2 μ) :
    |inner ℝ e (truncated n μ ε g a)| ≤
      |cellMean (μ.restrict A) (fun x => inner ℝ e
          (truncated n μ ε (fun y => f y + g y + h y) x)) -
        cellMean (μ.restrict Q) (fun x => inner ℝ e
          (truncated n μ ε (fun y => f y + g y + h y) x))| +
      3 * ((D : ℝ) ^ 2 * B + 1) + 3 * exteriorCellMeanConstant n G M := by
  have huf := hRiesz f hf
  have hug := hRiesz g hhg
  have huh := hRiesz h hh
  have hfAb := native_vector_cellMean_bound μ A hAfin hApos f _ hf huf.1 D huf.2 e he B hfA
  have hfQb := native_vector_cellMean_bound μ Q hQfin hQpos f _ hf huf.1 D huf.2 e he B hfQ
  have hgQb := native_vector_cellMean_bound μ Q hQfin hQpos g _ hhg hug.1 D hug.2 e he B hgQ
  have hgAb := hard_exterior_cellMean_near_center n hn G M μ hg g hhg hug.1 hM hgM
    a e he r hr hε hεr hgs A hA hAfin hApos hAnear
  have hhAb := hard_exterior_cellMean_near_center n hn G M μ hg h hh huh.1 hM hhM
    a e he R (hr.trans_le hrR) hε (by linarith) hhs A hA hAfin hApos
    (fun x hx => (hAnear x hx).trans hrR)
  have hhQb := hard_exterior_cellMean_near_center n hn G M μ hg h hh huh.1 hM hhM
    a e he R (hr.trans_le hrR) hε (by linarith) hhs Q hQ hQfin hQpos hQnear
  have hsumA := three_part_truncated_cellMean n hn G μ hg ε hε f g h hf hhg hh
    huf.1 hug.1 huh.1 A hAfin e
  have hsumQ := three_part_truncated_cellMean n hn G μ hg ε hε f g h hf hhg hh
    huf.1 hug.1 huh.1 Q hQfin e
  rw [hsumA, hsumQ]
  rcases abs_le.mp hfAb with ⟨hfAl, hfAu⟩
  rcases abs_le.mp hfQb with ⟨hfQl, hfQu⟩
  rcases abs_le.mp hgQb with ⟨hgQl, hgQu⟩
  rcases abs_le.mp hgAb with ⟨hgAl, hgAu⟩
  rcases abs_le.mp hhAb with ⟨hhAl, hhAu⟩
  rcases abs_le.mp hhQb with ⟨hhQl, hhQu⟩
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs
      (cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x)) +
        cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε g x)) +
        cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε h x)) -
        (cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε f x)) +
        cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε g x)) +
        cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε h x))))]
  · linarith [le_abs_self
      (cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε f x)) +
        cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε g x)) +
        cellMean (μ.restrict A) (fun x => inner ℝ e (truncated n μ ε h x)) -
        (cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε f x)) +
        cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε g x)) +
        cellMean (μ.restrict Q) (fun x => inner ℝ e (truncated n μ ε h x))))]

end

end RieszRectifiability

end OAI
