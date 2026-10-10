import OAI.GroupTheory.PolycyclicRecognition.Geometry.BoundaryRaySeparation

namespace OAI

/-! # Recovering a uniform generator height bound from the boundary traces -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

/-- Positive multiples of the original ray forms can be used as trace
characters. Controlling all traces off one ray controls the whole vector,
uniformly over which ray is omitted and over repeated rays. -/
theorem uniform_height_bound_of_ray_trace_bounds
    {W I Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I]
    (α ell : I → W →ₗ[ℝ] ℝ) (c rate : I → ℝ)
    (hc : ∀ i, 0 < c i) (hrate : ∀ i, 0 < rate i)
    (hrel : ∀ w, ∑ i, c i * α i w = 0)
    (hsep : ∀ w, (∀ i, α i w = 0) → w = 0)
    (hell : ∀ i, ell i = rate i • α i)
    (v : Z → W) (missing : Z → I) (B : I → ℝ) (hB : ∀ i, 0 ≤ B i)
    (htrace : ∀ z i, α i ∉ positiveWeightRay (α (missing z)) → |ell i (v z)| ≤ B i) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z, ‖v z‖ ≤ K := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_bound_outside_positive_ray α c hc hrel hsep
  let total := ∑ i, B i / rate i
  have htotal : 0 ≤ total := Finset.sum_nonneg (fun i _ => div_nonneg (hB i) (hrate i).le)
  refine ⟨C * total, mul_nonneg hC.le htotal, ?_⟩
  intro z
  apply hbound (missing z) (v z) total htotal
  intro i hi
  have hh := htrace z i hi
  rw [hell i, LinearMap.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (hrate i)] at hh
  have hdiv : |α i (v z)| ≤ B i / rate i := by
    apply (le_div_iff₀ (hrate i)).mpr
    simpa only [mul_comm] using hh
  exact hdiv.trans (Finset.single_le_sum
    (fun j _ => div_nonneg (hB j) (hrate j).le) (Finset.mem_univ i))

end PolycyclicRecognition

end

end OAI
