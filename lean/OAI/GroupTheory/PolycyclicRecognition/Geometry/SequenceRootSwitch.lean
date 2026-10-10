import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootSwitchBounds
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Sublinear root switches with subexponential coordinate bounds

At a contact facet the exponential root amplitude cancels its scalar
contraction. The remaining polynomial correction contributes only a
sublinear distance, uniformly in the translated sheet and position.
-/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra LieModule Filter
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]

theorem sublinear_root_switch_sequence
    {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
    (H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)) [H.IsCartanSubalgebra]
    (χ : Weight ℝ H (GroupLieAlgebra (𝓘(ℝ, EG)) G)) (hχ : χ.IsNonZero)
    (Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G) (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (v : rootSpace H χ) (scale RH R : ℕ → ℝ)
    (hs : Tendsto scale atTop atTop)
    (hRH0 : ∀ n, 0 ≤ RH n) (hR0 : ∀ n, 0 ≤ R n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ (x : G) (h : H) (t : ℝ),
        ‖(finBasis ℝ H).equivFun h‖ ≤ RH n →
        |t| * Real.exp (-χ h) ≤ R n →
        dist (x * Exp h)
          (x * Exp (t • (v : GroupLieAlgebra (𝓘(ℝ, EG)) G)) * Exp h) ≤ ε * scale n := by
  obtain ⟨C, D, hC, hD, hb⟩ :=
    root_switch_bound_of_published_realization T H χ hχ Exp hExp realize
  let d := finrank ℝ (rootSpace H χ)
  let P := fun n => C * (1 + RH n) ^ d * R n * ‖(rootCoordinates H χ) v‖
  have hbase : HasSubexponentialUpperBoundSeq scale (fun n => 1 + RH n) :=
    (sequence_subexponential_upper_const hs 1).add hRH hs
  have hbase0 : ∀ n, 0 ≤ 1 + RH n := fun n => by linarith [hRH0 n]
  have hpow := hbase.pow hs (Eventually.of_forall hbase0) d
  have hP : HasSubexponentialUpperBoundSeq scale P :=
    (((sequence_subexponential_upper_const hs C).mul hpow
      (Eventually.of_forall (fun _ => hC.le))).mul hR
      (Eventually.of_forall (fun n => mul_nonneg hC.le (pow_nonneg (hbase0 n) d)))).mul
      (sequence_subexponential_upper_const hs _)
      (Eventually.of_forall (fun n => mul_nonneg
        (mul_nonneg hC.le (pow_nonneg (hbase0 n) d)) (hR0 n)))
  have hsum := (sequence_subexponential_upper_const hs 2).add hP hs
  intro ε hε
  filter_upwards [hsum (ε / D) (div_pos hε hD)] with n hn
  intro x h t hh ht
  have hinside : C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ d *
      Real.exp (-χ h) * ‖(rootCoordinates H χ) (t • v)‖ ≤ P n := by
    rw [map_smul, norm_smul, Real.norm_eq_abs]
    calc
      _ = C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ d *
          (|t| * Real.exp (-χ h)) * ‖(rootCoordinates H χ) v‖ := by ring
      _ ≤ C * (1 + RH n) ^ d * R n * ‖(rootCoordinates H χ) v‖ := by
        gcongr
        exact mul_nonneg hC.le (pow_nonneg (hbase0 n) d)
      _ = _ := rfl
  have hlog : Real.log (2 + P n) ≤ (ε / D) * scale n := by
    have hP0 : 0 ≤ P n := mul_nonneg
      (mul_nonneg (mul_nonneg hC.le (pow_nonneg (hbase0 n) d)) (hR0 n)) (norm_nonneg _)
    exact (Real.log_le_log (by linarith) hn).trans_eq (Real.log_exp _)
  calc
    _ ≤ D * Real.log (2 + C * (1 + ‖(finBasis ℝ H).equivFun h‖) ^ d *
        Real.exp (-χ h) * ‖(rootCoordinates H χ) (t • v)‖) := hb x h (t • v)
    _ ≤ D * Real.log (2 + P n) := by
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact Real.log_le_log (by positivity) (by linarith)
    _ ≤ D * ((ε / D) * scale n) := mul_le_mul_of_nonneg_left hlog hD.le
    _ = ε * scale n := by field_simp

end PolycyclicRecognition

end

end OAI
