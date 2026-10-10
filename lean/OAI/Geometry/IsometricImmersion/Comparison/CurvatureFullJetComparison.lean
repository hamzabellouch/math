import OAI.Geometry.IsometricImmersion.Comparison.CurvatureComparisonControl
import OAI.Geometry.IsometricImmersion.Calculus.CoordinateJetNorm

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

theorem metric_word_difference_le_full_jet
    {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) (i j : Fin 2) (ds : List (Fin 2)) {e : ℝ}
    (hjet : ‖iteratedFDeriv ℝ ds.length (fun q => g q i j - h q i j) p‖ ≤ e) :
    |iteratedCoordPartial ds (fun q => g q i j) p -
      iteratedCoordPartial ds (fun q => h q i j) p| ≤ e := by
  rw [← CoordinateBound.iterated_sub (hg.1 i j) (hh.1 i j) hU ds hp]
  exact (norm_iteratedCoordPartial_le_jet ((hg.1 i j).sub (hh.1 i j)) hU ds hp).trans hjet

theorem actual_first_input_difference_le_full_jets
    {g h : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hh : SmoothPositiveOn h U) (hU : IsOpen U)
    {p : Coord} (hp : p ∈ U) {e : ℝ} (he : 0 ≤ e)
    (hjet : ∀ i j : Fin 2, ∀ k ≤ 1,
      ‖iteratedFDeriv ℝ k (fun q => g q i j - h q i j) p‖ ≤ e) :
    ‖actualCurvatureFirstInput g p - actualCurvatureFirstInput h p‖ ≤ e := by
  change max
    ‖(fun i j => g p i j) - (fun i j => h p i j)‖
    ‖(fun d i j => coordPartial d (fun q => g q i j) p) -
      (fun d i j => coordPartial d (fun q => h q i j) p)‖ ≤ e
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact metric_word_difference_le_full_jet hg hh hU hp i j [] (hjet i j 0 (by omega))
  · apply (pi_norm_le_iff_of_nonneg he).mpr
    intro d
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg he).mpr
    intro j
    exact metric_word_difference_le_full_jet hg hh hU hp i j [d] (hjet i j 1 (by omega))

theorem exists_uniform_density_comparison_of_full_jets
    (B : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g h : MetricField) (U : Set Coord),
      SmoothPositiveOn g U → SmoothPositiveOn h U → IsOpen U →
      ∀ p ∈ U, ∀ e : ℝ, 0 ≤ e →
        ‖actualCurvatureFirstInput h p‖ ≤ B → d ≤ (h p).det →
        (∀ i j : Fin 2, ∀ k ≤ 2,
          ‖iteratedFDeriv ℝ k (fun q => g q i j - h q i j) p‖ ≤ e) →
        e ≤ 1 → (4 * max B 0 + 2) * e ≤ d / 2 →
        |curvatureDensity g p - curvatureDensity h p| ≤ C * e := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_curvature_density_comparison B hd
  refine ⟨C, hC, ?_⟩
  intro g h U hg hh hU p hp e he hfirst hdet hjet he1 hsmall
  apply hbound g h U hg hh hU p hp e hfirst hdet
    (actual_first_input_difference_le_full_jets hg hh hU hp he
      (fun i j k hk => hjet i j k (by omega))) he1 hsmall
  intro i j k l
  exact metric_word_difference_le_full_jet hg hh hU hp k l [i, j]
    (hjet k l 2 (by omega))

end SmoothLocal.Pulse

end

end OAI
