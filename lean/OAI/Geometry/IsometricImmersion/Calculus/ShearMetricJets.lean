import OAI.Geometry.IsometricImmersion.Calculus.ShearHeightJets
import OAI.Geometry.IsometricImmersion.Coordinates.ActualShearHyperbolicity

namespace OAI

noncomputable section
open Set
open scoped ContDiff Topology BigOperators Matrix

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry

def shearedMetricCoordinateBudget (G q0 : ℝ) (N : ℕ) : ℝ :=
  4 * (1 + |q0|)^2 * (2 * (1 + |q0|))^N * G

theorem shearedMetricCoordinateBudget_nonneg {G : ℝ} (q0 : ℝ) (N : ℕ) (hG : 0 ≤ G) :
    0 ≤ shearedMetricCoordinateBudget G q0 N := by
  unfold shearedMetricCoordinateBudget
  positivity

private theorem coordinateBound_add_on {f h : Coord → ℝ} {U S : Set Coord}
    {N : ℕ} {A B : ℝ} (hf : ContDiffOn ℝ ∞ f U) (hh : ContDiffOn ℝ ∞ h U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hA : CoordinateBound f S N A) (hB : CoordinateBound h S N B) :
    CoordinateBound (fun p => f p + h p) S N (A + B) := by
  intro ds hds p hp
  rw [CoordinateBound.iterated_add hf hh hU ds (hSU hp)]
  exact (abs_add_le _ _).trans (add_le_add (hA ds hds p hp) (hB ds hds p hp))

private theorem coordinateBound_const_mul_on {f : Coord → ℝ} {U S : Set Coord}
    {N : ℕ} {A : ℝ} (hf : ContDiffOn ℝ ∞ f U)
    (hU : IsOpen U) (hSU : S ⊆ U) (hA : CoordinateBound f S N A) (c : ℝ) :
    CoordinateBound (fun p => c * f p) S N (|c| * A) := by
  intro ds hds p hp
  rw [CoordinateBound.iterated_const_mul hf hU c ds (hSU hp), abs_mul]
  exact mul_le_mul_of_nonneg_left (hA ds hds p hp) (abs_nonneg _)

theorem inverseShearMatrix_entry_bound (q0 : ℝ) (i j : Fin 2) :
    |inverseShearMatrix q0 i j| ≤ 1 + |q0| := by
  fin_cases i <;> fin_cases j <;> simp [inverseShearMatrix]
  positivity

theorem metricInShearCoordinates_four_terms (g : MetricField) (q0 : ℝ) (i j : Fin 2) :
    (fun p => metricInShearCoordinates g q0 p i j) =
      (fun p =>
        ((inverseShearMatrix q0 0 i * inverseShearMatrix q0 0 j) *
            heightInShearCoordinates (fun r => g r 0 0) q0 p +
          (inverseShearMatrix q0 0 i * inverseShearMatrix q0 1 j) *
            heightInShearCoordinates (fun r => g r 0 1) q0 p) +
        ((inverseShearMatrix q0 1 i * inverseShearMatrix q0 0 j) *
            heightInShearCoordinates (fun r => g r 1 0) q0 p +
          (inverseShearMatrix q0 1 i * inverseShearMatrix q0 1 j) *
            heightInShearCoordinates (fun r => g r 1 1) q0 p)) := by
  funext p
  simp only [metricInShearCoordinates, affinePullbackMetric, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_two, heightInShearCoordinates,
    Function.comp_apply, ← inverseShearCoordinates_eq_affine]
  ring

theorem metric_coordinate_bound_inverse_shear
    {g : MetricField} {U S : Set Coord} {N : ℕ} {G : ℝ}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) (hSU : S ⊆ U) (hG : 0 ≤ G)
    (hgB : ∀ i j, CoordinateBound (fun p => g p i j) S N G) (q0 : ℝ) :
    ∀ i j, CoordinateBound (fun p => metricInShearCoordinates g q0 p i j)
      (inverseShearCoordinates q0 ⁻¹' S) N (shearedMetricCoordinateBudget G q0 N) := by
  let V := inverseShearCoordinates q0 ⁻¹' U
  let T := inverseShearCoordinates q0 ⁻¹' S
  let A := (2 * (1 + |q0|))^N * G
  let B := (1 + |q0|)^2 * A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hVU : IsOpen V := hU.preimage (inverseShearCoordinates_contDiff q0).continuous
  have hTV : T ⊆ V := fun p hp => hSU hp
  have hs (a b : Fin 2) : ContDiffOn ℝ ∞ (heightInShearCoordinates (fun p => g p a b) q0) V :=
    heightInShearCoordinates_contDiffOn (hg.1 a b) q0
  have hb (a b : Fin 2) :
      CoordinateBound (heightInShearCoordinates (fun p => g p a b) q0) T N A :=
    SmoothLocal.Pulse.CoordinateBound.inverse_shear (hgB a b) (hg.1 a b) hU hSU hG q0
  intro i j
  let term (a b : Fin 2) : Coord → ℝ := fun p =>
    (inverseShearMatrix q0 a i * inverseShearMatrix q0 b j) *
      heightInShearCoordinates (fun r => g r a b) q0 p
  have htS (a b : Fin 2) : ContDiffOn ℝ ∞ (term a b) V := contDiffOn_const.mul (hs a b)
  have htB (a b : Fin 2) : CoordinateBound (term a b) T N B := by
    have hh := coordinateBound_const_mul_on (hs a b) hVU hTV (hb a b)
      (inverseShearMatrix q0 a i * inverseShearMatrix q0 b j)
    apply hh.mono le_rfl
    have hc : |inverseShearMatrix q0 a i * inverseShearMatrix q0 b j| ≤ (1 + |q0|)^2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul (inverseShearMatrix_entry_bound q0 a i) (inverseShearMatrix_entry_bound q0 b j)
        (abs_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_right hc hA
  have hrow0 := coordinateBound_add_on (htS 0 0) (htS 0 1) hVU hTV (htB 0 0) (htB 0 1)
  have hrow1 := coordinateBound_add_on (htS 1 0) (htS 1 1) hVU hTV (htB 1 0) (htB 1 1)
  have hsum := coordinateBound_add_on ((htS 0 0).add (htS 0 1))
    ((htS 1 0).add (htS 1 1)) hVU hTV hrow0 hrow1
  rw [metricInShearCoordinates_four_terms]
  have hbudget : B + B + (B + B) = shearedMetricCoordinateBudget G q0 N := by
    dsimp [B, A, shearedMetricCoordinateBudget]
    ring
  rw [hbudget] at hsum
  exact hsum

theorem metricDet_in_shear_coordinates (g : MetricField) (q0 : ℝ) (p : Coord) :
    (metricInShearCoordinates g q0 p).det = (g (inverseShearCoordinates q0 p)).det := by
  simp only [metricInShearCoordinates, det_affinePullbackMetric,
    inverseShearMatrix_det, one_pow, one_mul, ← inverseShearCoordinates_eq_affine]

end SmoothLocal.Pulse

end

end OAI
