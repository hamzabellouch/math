import OAI.Geometry.IsometricImmersion.Metrics.RemainderCoefficientBounds
import Mathlib.Topology.Order.Compact

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators Matrix ENNReal NNReal

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

theorem compact_finite_fullJet_bound
    {f : Coord → ℝ} {U S : Set Coord}
    (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U) (hS : IsCompact S) (hSU : S ⊆ U)
    (ell : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k ≤ ell, ∀ p ∈ S, ‖iteratedFDeriv ℝ k f p‖ ≤ M := by
  classical
  have hk : ∀ k : Fin (ell + 1), ∃ A : ℝ, ∀ p ∈ S, ‖iteratedFDeriv ℝ k.val f p‖ ≤ A := by
    intro k
    have hcont : ContinuousOn (iteratedFDeriv ℝ k.val f) S := by
      intro p hp
      exact (((hf.contDiffAt (hU.mem_nhds (hSU hp))).differentiableAt_iteratedFDeriv
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k.val)).continuousAt).continuousWithinAt
    exact hS.exists_bound_of_continuousOn hcont
  choose A hA using hk
  refine ⟨∑ k : Fin (ell + 1), |A k|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro k hk p hp
  let j : Fin (ell + 1) := ⟨k, by omega⟩
  exact (hA j p hp).trans ((le_abs_self (A j)).trans
    (Finset.single_le_sum (fun index _ => abs_nonneg (A index)) (Finset.mem_univ j)))

theorem fixed_metric_closed_data
    {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U) :
    ∃ G d : ℝ, 0 ≤ G ∧ 0 < d ∧
      (∀ i j : Fin 2, ∀ k ≤ 4, ∀ p ∈ modelSquare,
        ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ G) ∧
      (∀ p ∈ modelSquare, d ≤ |(g p).det|) := by
  classical
  have hco : ∀ i j : Fin 2, ∃ A : ℝ, 0 ≤ A ∧
      ∀ k ≤ 4, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k (fun q => g q i j) p‖ ≤ A :=
    fun i j => compact_finite_fullJet_bound (hg.1 i j) hU modelSquare_isCompact hSU 4
  choose A hA0 hA using hco
  obtain ⟨d, hd, hdet⟩ := modelSquare_isCompact.exists_forall_le'
    ((metricDet_contDiffOn hg).continuousOn.abs.mono hSU)
    (fun p hp => abs_pos.mpr (metricDet_ne_zero hg (hSU hp)))
  refine ⟨∑ i : Fin 2, ∑ j : Fin 2, A i j, d,
    Finset.sum_nonneg (fun row _ => Finset.sum_nonneg (fun column _ => hA0 row column)),
    hd, ?_, hdet⟩
  intro i j k hk p hp
  exact (hA i j k hk p hp).trans
    ((Finset.single_le_sum (fun column _ => hA0 i column) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun row _ => Finset.sum_nonneg (fun column _ => hA0 row column))
        (Finset.mem_univ i)))

theorem fixed_metric_uniform_actualHighRemainder_bound
    {g : MetricField} {U : Set Coord} {Z c : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : modelSquare ⊆ U)
    (hZ : 0 ≤ Z) (hc : 0 < c) (m : ℕ) (hm : 8 ≤ m + 3) :
    ∃ G d C : ℝ, 0 ≤ G ∧ 0 < d ∧ 0 ≤ C ∧
      ∀ z : Coord → ℝ, ContDiffOn ℝ ∞ z U →
      (∀ k ≤ 8, ∀ p ∈ modelSquare, ‖iteratedFDeriv ℝ k z p‖ ≤ Z) →
      (∀ p ∈ modelSquare, c ≤ |covHessian g z p 1 1|) →
      ∀ V : Set Coord, MeasurableSet V → V ⊆ modelSquare → volume V < (⊤ : ℝ≥0∞) →
      ∀ B : ℝ, 1 ≤ B → ∀ H : ℝ≥0,
      (∀ n j, n + heightStateBaseOrder j ≤ m + 1 →
        ∀ p ∈ V, |heightStateFactor z n j p| ≤ B) →
      (∀ n j, n + heightStateBaseOrder j ≤ m + 3 →
        eLpNorm (heightStateFactor z n j) 2 (volume.restrict V) ≤ (H : ℝ≥0∞)) →
      eLpNorm (actualHighRemainder g z m) 2 (volume.restrict V) ≤
        actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m ∧
      actualHighRemainderL2Budget C (heightPFirstBound G Z d c) B H V m < (⊤ : ℝ≥0∞) ∧
      MemLp (actualHighRemainder g z m) 2 (volume.restrict V) := by
  obtain ⟨G, d, hG, hd, hgB, hdet⟩ := fixed_metric_closed_data hg hU hSU
  obtain ⟨C, hC, hbound⟩ := exists_uniform_actualHighRemainder_bound_frechet_data
    hg hU hSU hG hZ hd hc hgB hdet m hm
  exact ⟨G, d, C, hG, hd, hC, hbound⟩

end SmoothLocal.HighEquation

end

end OAI
