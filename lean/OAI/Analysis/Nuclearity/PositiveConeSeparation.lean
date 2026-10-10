import Mathlib

namespace OAI

/-! The weak-star separation step used in KR02 Lemma 7.17(ii).
A separating continuous functional on the weak dual is evaluation at an
actual self-adjoint algebra element. -/

noncomputable section
open scoped Topology

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma selfAdjoint_separator_of_closed_cone
    (K : Set (WeakDual ℝ (selfAdjoint A)))
    (hclosed : IsClosed K) (hconvex : Convex ℝ K) (hzero : 0 ∈ K)
    (hscale : ∀ t : ℝ, 0 ≤ t → ∀ φ ∈ K, t • φ ∈ K)
    (φ₀ : WeakDual ℝ (selfAdjoint A)) (hφ₀ : φ₀ ∉ K) :
    ∃ a : selfAdjoint A, φ₀ a < 0 ∧ ∀ φ ∈ K, 0 ≤ φ a := by
  let : LocallyConvexSpace ℝ (WeakDual ℝ (selfAdjoint A)) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℝ (selfAdjoint A))))
  obtain ⟨L, u, hφ, hK⟩ := geometric_hahn_banach_point_closed hconvex hclosed hφ₀
  have hu : u < 0 := by simpa only [map_zero] using hK 0 hzero
  have hpositive (φ : WeakDual ℝ (selfAdjoint A)) (hmem : φ ∈ K) : 0 ≤ L φ := by
    by_contra! hn
    let t : ℝ := (u - 1) / L φ
    have ht : 0 < t := div_pos_of_neg_of_neg (by linarith) hn
    have hlt := hK (t • φ) (hscale t ht.le φ hmem)
    have heq : L (t • φ) = u - 1 := by
      rw [map_smul, smul_eq_mul]
      exact div_mul_cancel₀ (u - 1) (ne_of_lt hn)
    rw [heq] at hlt
    linarith
  obtain ⟨a, ha⟩ := LinearMap.dualEmbedding_surjective
    (topDualPairing ℝ (selfAdjoint A)) L
  have heval (φ : WeakDual ℝ (selfAdjoint A)) : L φ = φ a := by
    have h := DFunLike.congr_fun ha φ
    exact h.symm
  refine ⟨a, ?_, ?_⟩
  · rw [← heval]
    exact hφ.trans hu
  · intro φ hmem
    rw [← heval]
    exact hpositive φ hmem

end WeakPureInfiniteness

end

end OAI
