import OAI.GroupTheory.PolycyclicRecognition.Geometry.PositiveWeightCones
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace OAI

/-! # The ray and two-ray trace tests determine the offset

After the volume comparison in both directions, the ray trace and all
independent two-ray traces vanish. Positivity of their coefficients then
forces every generator weight to vanish on the offset.
-/

noncomputable section
namespace PolycyclicRecognition

variable {W I : Type*} [AddCommGroup W] [Module ℝ W]

/-- One ray test and one test for each independent generator weight suffice.
Dependent weights require no additional test. -/
theorem eq_zero_of_ray_two_ray_trace_tests
    (α : W →ₗ[ℝ] ℝ) (hα : α ≠ 0) (β : I → W →ₗ[ℝ] ℝ)
    (hsep : ∀ w : W, (∀ i, β i w = 0) → w = 0)
    (ray : W →ₗ[ℝ] ℝ) (test : I → W →ₗ[ℝ] ℝ)
    (hray : ∃ c : ℝ, 0 < c ∧ ray = c • α)
    (htest : ∀ i, LinearIndependent ℝ ![α, β i] →
      ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ test i = c • α + d • β i)
    (w : W) (hr : ray w = 0)
    (ht : ∀ i, LinearIndependent ℝ ![α, β i] → test i w = 0) : w = 0 := by
  classical
  obtain ⟨c, hc, rfl⟩ := hray
  have hαw : α w = 0 := by
    have hz : c * α w = 0 := hr
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hc)
  apply hsep w
  intro i
  by_cases hi : LinearIndependent ℝ ![α, β i]
  · obtain ⟨a, b, _, hb, he⟩ := htest i hi
    have hh := ht i hi
    rw [he, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      smul_eq_mul, smul_eq_mul, hαw, mul_zero, zero_add] at hh
    exact (mul_eq_zero.mp hh).resolve_left (ne_of_gt hb)
  · have hdep : ∃ a : ℝ, a • α = β i := by
      simpa only [LinearIndependent.pair_iff' hα, not_forall, not_not] using hi
    obtain ⟨a, ha⟩ := hdep
    rw [← ha, LinearMap.smul_apply, hαw, smul_zero]

/-- Applying the same volume test to the reversed pair converts the two
inequalities into equality before the trace-separation argument. -/
theorem eq_of_ray_two_ray_trace_inequalities
    (α : W →ₗ[ℝ] ℝ) (hα : α ≠ 0) (β : I → W →ₗ[ℝ] ℝ)
    (hsep : ∀ w : W, (∀ i, β i w = 0) → w = 0)
    (ray : W →ₗ[ℝ] ℝ) (test : I → W →ₗ[ℝ] ℝ)
    (hray : ∃ c : ℝ, 0 < c ∧ ray = c • α)
    (htest : ∀ i, LinearIndependent ℝ ![α, β i] →
      ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ test i = c • α + d • β i)
    (x y : W) (hr : ray (y - x) ≤ 0) (hr' : ray (x - y) ≤ 0)
    (ht : ∀ i, LinearIndependent ℝ ![α, β i] → test i (y - x) ≤ 0)
    (ht' : ∀ i, LinearIndependent ℝ ![α, β i] → test i (x - y) ≤ 0) : x = y := by
  have hz : y - x = 0 := eq_zero_of_ray_two_ray_trace_tests α hα β hsep ray test hray htest
    (y - x) (by
      simp only [map_sub] at hr hr' ⊢
      linarith) (by
      intro i hi
      have hp := ht i hi
      have hn := ht' i hi
      simp only [map_sub] at hp hn ⊢
      linarith)
  exact (sub_eq_zero.mp hz).symm

end PolycyclicRecognition

end

end OAI
