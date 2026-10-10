import OAI.GroupTheory.PolycyclicRecognition.Analysis.Packing
import Mathlib.Topology.MetricSpace.IsometricSMul

namespace OAI

/-!
# Uniform multiplicity of a coarse embedding

The recognition proof counts points in an intrinsic subgroup word ball using
the ambient group's fixed word metric. Its lower quasi-isometry bound gives a
uniform bound for the number of points mapping into a fixed-radius target ball.
No undistortion of the subgroup is used.
-/

namespace PolycyclicRecognition

theorem exists_uniform_ball_multiplicity
    {H X : Type*} [Group H] [MetricSpace H] [PseudoMetricSpace X]
    [IsIsometricSMul H H] (f : H → X)
    (hfinite : ∀ R : ℝ, (Metric.closedBall (1 : H) R).Finite)
    {K C r : ℝ} (hK : 0 ≤ K)
    (hlower : ∀ x y, dist x y ≤ K * dist (f x) (f y) + C) :
    ∃ M : ℕ, ∀ (c : X) (A : Finset H),
      (∀ h ∈ A, dist (f h) c ≤ r) → A.card ≤ M := by
  classical
  let R := K * (r + r) + C
  let ball := (hfinite R).toFinset
  refine ⟨ball.card, fun c A hA => ?_⟩
  by_cases hne : A.Nonempty
  · obtain ⟨a, ha⟩ := hne
    have hinj : Function.Injective (fun h : H => a⁻¹ * h) := fun _ _ h => mul_left_cancel h
    have himage : A.image (fun h => a⁻¹ * h) ⊆ ball := by
      intro h hh
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
      apply (hfinite R).mem_toFinset.mpr
      change dist (a⁻¹ * b) 1 ≤ R
      have hd : dist (f a) (f b) ≤ r + r := by
        exact (dist_triangle (f a) c (f b)).trans
          (add_le_add (hA a ha) (by simpa only [dist_comm] using hA b hb))
      have hs := (hlower a b).trans
        (add_le_add (mul_le_mul_of_nonneg_left hd hK) le_rfl)
      have heq : dist (a⁻¹ * b) 1 = dist a b := by
        rw [dist_comm]
        simpa only [mul_one, mul_inv_cancel_left] using
          (dist_mul_left a (1 : H) (a⁻¹ * b)).symm
      rwa [heq]
    simpa only [Finset.card_image_of_injective A hinj] using Finset.card_le_card himage
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty, Nat.zero_le]

/-- The same multiplicity constant works on any injectively parametrized
subset, in particular on a subgroup equipped with its intrinsic word metric. -/
theorem ball_multiplicity_comp_injective
    {H J X : Type*} [PseudoMetricSpace X] [DecidableEq H]
    (f : H → X) (ι : J → H) (hι : Function.Injective ι) (M : ℕ) (r : ℝ)
    (hM : ∀ (c : X) (A : Finset H),
      (∀ h ∈ A, dist (f h) c ≤ r) → A.card ≤ M) :
    ∀ (c : X) (A : Finset J), (∀ j ∈ A, dist (f (ι j)) c ≤ r) → A.card ≤ M := by
  intro c A hA
  have h := hM c (A.image ι) (by
    intro h hh
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
    exact hA j hj)
  simpa only [Finset.card_image_of_injective A hι] using h

end PolycyclicRecognition

end OAI
