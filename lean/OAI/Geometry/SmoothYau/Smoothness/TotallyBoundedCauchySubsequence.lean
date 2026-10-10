import Mathlib

namespace OAI

noncomputable section
open Set Filter Function
open scoped Topology ContDiff Manifold SchwartzMap
open Set Filter Manifold Bundle MeasureTheory NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Topology NNReal
namespace YauCounterexamples
open Set Filter
open scoped Topology

lemma totallyBounded_of_cauchy_subsequence {X : Type*} [UniformSpace X] {S : Set X}
    (h : ∀ x : ℕ → X, (∀ n, x n ∈ S) →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ CauchySeq (x ∘ ψ)) : TotallyBounded S := by
  intro V hV
  contrapose! h
  obtain ⟨u, hu, hdist⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ S) ∧
      ∀ n m, m < n → u m ∉ UniformSpace.ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and] using! seq_of_forall_finite_exists h
  refine ⟨u, hu, fun ψ hψ hc => ?_⟩
  obtain ⟨N, hN⟩ := hc.mem_entourage hV
  exact hdist (ψ (N + 1)) (ψ N) (hψ (Nat.lt_add_one N))
    (hN (N + 1) N N.le_succ le_rfl)

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma interpolation_cauchy (I : X →L[ℝ] Y) (L : X →L[ℝ] Z)
    (hint : ∀ ε > (0 : ℝ), ∃ D ≥ (0 : ℝ), ∀ x, ‖I x‖ ≤ ε * ‖x‖ + D * ‖L x‖)
    (u : ℕ → X) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ‖u n‖ ≤ C)
    (hc : CauchySeq (fun n => L (u n))) : CauchySeq (fun n => I (u n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ := ε / (4 * (C + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨D, hD, hDint⟩ := hint δ hδ
  have ht : 0 < ε / (2 * (D + 1)) := div_pos hε (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc _ ht
  refine ⟨N, fun n hn m hm => ?_⟩
  have hh := hDint (u n - u m)
  rw [map_sub, map_sub] at hh
  have hu : ‖u n - u m‖ ≤ 2 * C := (norm_sub_le _ _).trans (by linarith [hb n, hb m])
  have hlow := hN n hn m hm
  have hhigh : δ * ‖u n - u m‖ ≤ ε / 2 := by
    have h0 : δ * (2 * C) ≤ ε / 2 := by
      dsimp only [δ]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < 4 * (C + 1))).mpr
      nlinarith
    exact (mul_le_mul_of_nonneg_left hu hδ.le).trans h0
  have hsmall : D * dist (L (u n)) (L (u m)) < ε / 2 := by
    have hp : 0 < D + 1 := by linarith
    have hlow' := (lt_div_iff₀ (by positivity : 0 < 2 * (D + 1))).mp hlow
    have hz : 0 ≤ dist (L (u n)) (L (u m)) := dist_nonneg
    nlinarith
  rw [dist_eq_norm] at hsmall ⊢
  linarith
end YauCounterexamples

end

end OAI
