import OAI.Probability.InvariantIsing.Cavity.CavityGroupProjectionUniform
import OAI.Probability.InvariantIsing.Arrays.OverlapBounds

namespace OAI

/-! The fresh-frame covariance is the physical projected overlap divided
by the finite spectral-group mass. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

def cavityPhysicalReplicaVectors {N m r : ℕ} (U : Rotation N)
    (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N) :
    (a : Fin m) → Fin r → Fin (d a) → ℝ :=
  fun a i k => U (spinVector (σ i)) (e a k)

lemma cavityPhysicalReplicaVectors_gram {N m r : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N)
    (a : Fin m) (i j : Fin r) :
    cavityGroupReplicaGram (cavityPhysicalReplicaVectors U I d e σ) a i j =
      projectedOverlap U (I a) (σ i) (σ j) / ((d a : ℝ) / N) := by
  have hs : (∑ k, U (spinVector (σ i)) (e a k) * U (spinVector (σ j)) (e a k)) =
      ∑ k ∈ I a, U (spinVector (σ i)) k * U (spinVector (σ j)) k := by
    exact ((e a).sum_comp (fun k : ↥(I a) =>
      U (spinVector (σ i)) k * U (spinVector (σ j)) k)).trans
        ((I a).sum_coe_sort (fun k : Fin N => U (spinVector (σ i)) k * U (spinVector (σ j)) k))
  simp only [cavityGroupReplicaGram, cavityPhysicalReplicaVectors, hs, projectedOverlap]
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  by_cases hd : d a = 0
  · simp [hd]
  · have hd' : (d a : ℝ) ≠ 0 := by exact_mod_cast hd
    field_simp

lemma cavityPhysicalReplicaVectors_gram_bound {N m r : ℕ} (hN : 0 < N)
    (U : Rotation N) (I : Fin m → Finset (Fin N)) (d : Fin m → ℕ)
    (e : (a : Fin m) → Fin (d a) ≃ ↥(I a)) (σ : Fin r → Spin N)
    (c : ℝ) (hc : 0 < c) (hd : ∀ a, c ≤ (d a : ℝ) / N) :
    ∀ a i j, |cavityGroupReplicaGram (cavityPhysicalReplicaVectors U I d e σ) a i j| ≤ 1 / c := by
  intro a i j
  rw [cavityPhysicalReplicaVectors_gram hN, abs_div,
    abs_of_pos (lt_of_lt_of_le hc (hd a))]
  exact div_le_div₀ (by positivity) (projectedOverlap_abs_le_one U (I a) (σ i) (σ j))
    hc (hd a)

end InvariantIsing

end

end OAI
