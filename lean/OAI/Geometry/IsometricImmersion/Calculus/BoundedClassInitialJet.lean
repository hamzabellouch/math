import OAI.Geometry.IsometricImmersion.Coordinates.BoundedPatchSlabGeometry
import OAI.Geometry.IsometricImmersion.Comparison.ShearFirstJetComparison
import OAI.Geometry.IsometricImmersion.Darboux.QReferenceInitialTolerance

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation SmoothLocal.Flow SmoothLocal.Perturbation

theorem actual_first_input_norm_le {g : MetricField} {p : Coord} {G : ℝ} (hG : 0 ≤ G)
    (hvalue : ∀ i j, |g p i j| ≤ G)
    (hpartial : ∀ a i j, |coordPartial a (fun q => g q i j) p| ≤ G) :
    ‖actualCurvatureFirstInput g p‖ ≤ G := by
  change max ‖(fun i j => g p i j)‖
    ‖(fun a i j => coordPartial a (fun q => g q i j) p)‖ ≤ G
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro j
    exact hvalue i j
  · apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro a
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hG).mpr
    intro j
    exact hpartial a i j

theorem sheared_first_input_norm_le_of_original_jets
    {g : MetricField} {U : Set Coord} {p : Coord} {q0 G : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hp : inverseShearCoordinates q0 p ∈ U)
    (hG : 0 ≤ G) (hq0 : |q0| ≤ 1)
    (hgB : ∀ i j k, k ≤ 1 →
      ‖iteratedFDeriv ℝ k (fun a => g a i j) (inverseShearCoordinates q0 p)‖ ≤ G) :
    ‖actualCurvatureFirstInput (metricInShearCoordinates g q0) p‖ ≤ 8 * G := by
  have hf : ‖actualCurvatureFirstInput g (inverseShearCoordinates q0 p)‖ ≤ G := by
    apply actual_first_input_norm_le hG
    · intro i j
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hgB i j 0 (by omega)
    · intro a i j
      exact (norm_iteratedCoordPartial_le_jet (hg.1 i j) hU [a] hp).trans
        (hgB i j 1 (by omega))
  have hp' : affineCoordinates 0 (inverseShearMatrix q0) p ∈ U := by
    simpa only [← inverseShearCoordinates_eq_affine] using hp
  unfold metricInShearCoordinates
  rw [actualCurvatureFirstInput_affinePullback hg hU 0 (inverseShearMatrix q0) p hp']
  exact affineFirstJetMap_norm_le_eight _ (inverseShearMatrix_entry_le_one hq0) _ hG
    (by simpa only [← inverseShearCoordinates_eq_affine] using hf)

def boundedClassShearedStateBudget (q0 : ℝ) (M : ℕ) : ℝ :=
  max 1 ((2 * (1 + |q0|))^2 * (M : ℝ))

theorem boundedClassShearedStateBudget_pos (q0 : ℝ) (M : ℕ) :
    0 < boundedClassShearedStateBudget q0 M :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem bounded_class_sheared_solution_state_bound
    {g : MetricField} {z : Coord → ℝ} {M : ℕ} (h : BoundedAdmissibleHeight g M z)
    (q0 : ℝ) {p : Coord} (hp : inverseShearCoordinates q0 p ∈ SmoothLocal.Flow.modelSquare)
    (hcoords : |p 0| ≤ 1 ∧ |p 1| ≤ 1) :
    ‖qSolutionJet (heightInShearCoordinates z q0) p‖ ≤ boundedClassShearedStateBudget q0 M := by
  obtain ⟨_, hadm, hjet, _, _⟩ := h
  obtain ⟨U, hU, hSU, _, hz, _, _, _, _⟩ := hadm
  have hzB : CoordinateBound z SmoothLocal.Flow.modelSquare 2 (M : ℝ) := by
    intro ds hds p hp
    exact (norm_iteratedCoordPartial_le_jet hz hU ds (hSU hp)).trans
      (hjet ds.length (by omega) p hp)
  have hshear := SmoothLocal.Pulse.CoordinateBound.inverse_shear hzB hz hU hSU (Nat.cast_nonneg M) q0
  have hstate : ∀ i : Fin 6, |qSolutionJet (heightInShearCoordinates z q0) p i| ≤
      boundedClassShearedStateBudget q0 M := by
    intro i
    fin_cases i
    · exact hcoords.1.trans (le_max_left _ _)
    · exact hcoords.2.trans (le_max_left _ _)
    · exact (hshear [0] (by norm_num) p hp).trans (le_max_right _ _)
    · exact (hshear [1] (by norm_num) p hp).trans (le_max_right _ _)
    · exact (hshear [0, 1] (by norm_num) p hp).trans (le_max_right _ _)
    · exact (hshear [0, 0] (by norm_num) p hp).trans (le_max_right _ _)
  exact (pi_norm_le_iff_of_nonneg (boundedClassShearedStateBudget_pos q0 M).le).mpr hstate

end SmoothLocal.Pulse

end

end OAI
