import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportNorm
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Module.Projective

namespace OAI

/-!
# Algebraic consequences of stationary volume comparison

Once the forward volume comparison gives domination of segment supports,
the averaged homomorphism factors through canonical height by an invertible
linear map. The reverse comparison for the coupled inverse then makes this
map a support isometry. Neither conclusion is taken as a new hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

/-- A surjective quotient and a map to the same finite-dimensional target
with a smaller kernel differ by an invertible linear map. -/
theorem exists_linearEquiv_factor_of_kernel_le
    (π l : V →ₗ[ℝ] W) (hπ : Function.Surjective π) (hker : l.ker ≤ π.ker) :
    ∃ A : W ≃ₗ[ℝ] W, ∀ v, l v = A (π v) := by
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  have hsection (w : W) : π (s w) = w := by
    exact congrArg (fun f : W →ₗ[ℝ] W => f w) hs
  let A₀ : W →ₗ[ℝ] W := l.comp s
  have hinj : Function.Injective A₀ := by
    intro x y hxy
    have hl : s (x - y) ∈ l.ker := by
      change l (s (x - y)) = 0
      change l (s x) = l (s y) at hxy
      simpa only [map_sub, sub_eq_zero] using hxy
    have hp := hker hl
    change π (s (x - y)) = 0 at hp
    rw [hsection] at hp
    exact sub_eq_zero.mp hp
  have hsurj : Function.Surjective A₀ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  let A : W ≃ₗ[ℝ] W := LinearEquiv.ofBijective A₀ ⟨hinj, hsurj⟩
  refine ⟨A, ?_⟩
  intro v
  obtain ⟨w, hw⟩ := hsurj (l v)
  have hl : v - s w ∈ l.ker := by
    change l (v - s w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hw.symm
  have hp := hker hl
  change π (v - s w) = 0 at hp
  rw [map_sub, hsection] at hp
  rw [sub_eq_zero] at hp
  change l v = A₀ (π v)
  rw [hp, hw]

/-- The actual support norm turns the forward volume inequality into the
invertible height factor of the stationary slope. -/
theorem exists_linearEquiv_factor_of_support_domination
    {I B : Type*} [Fintype I] [Fintype B] [Nonempty B]
    (D : SupportDatum W I B) (π l : V →ₗ[ℝ] W) (hπ : Function.Surjective π)
    (hvol : ∀ v, D.segmentSupport (π v) ≤ D.segmentSupport (l v)) :
    ∃ A : W ≃ₗ[ℝ] W, ∀ v, l v = A (π v) := by
  apply exists_linearEquiv_factor_of_kernel_le π l hπ
  intro v hv
  have h := hvol v
  rw [LinearMap.mem_ker.mp hv, D.segmentSupport_zero] at h
  exact LinearMap.mem_ker.mpr ((D.segmentSupport_eq_zero_iff _).mp
    (le_antisymm h (D.segmentSupport_nonneg _)))

omit [FiniteDimensional ℝ W] in
/-- Forward comparison and comparison for the *same coupled inverse* force
equality of the support exponents. -/
theorem support_preserved_of_forward_inverse
    {I B : Type*} [Fintype I] [Fintype B] [Nonempty B]
    (D : SupportDatum W I B) (A : W ≃ₗ[ℝ] W)
    (hforward : ∀ w, D.segmentSupport w ≤ D.segmentSupport (A w))
    (hinverse : ∀ w, D.segmentSupport w ≤ D.segmentSupport (A.symm w)) :
    ∀ w, D.segmentSupport (A w) = D.segmentSupport w := by
  intro w
  exact le_antisymm (by simpa only [A.symm_apply_apply] using hinverse (A w)) (hforward w)

end PolycyclicRecognition

end

end OAI
