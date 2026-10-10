import OAI.Probability.SignedSweeps.WeightedNoIsolates

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J] {d : ℕ}

def encounterGraph (state : J → Fin d → SymmetricGroup (2 ^ d)) : SimpleGraph (J × Fin (2 ^ d)) where
  Adj v w := v ≠ w ∧ ∃ i : Fin d,
    state w.1 i w.2 = state v.1 i v.2 ∨
    state w.1 i w.2 = flipPermutation d i (state v.1 i v.2)
  symm := ⟨by
    rintro v w ⟨hvw, i, hi⟩
    refine ⟨hvw.symm, i, ?_⟩
    rcases hi with hi | hi
    · exact Or.inl hi.symm
    · exact Or.inr (by rw [hi, flipPermutation_twice])⟩
  loopless := ⟨by rintro v ⟨hvv, _⟩; exact hvv rfl⟩

def encounterCandidate (state : J → Fin d → SymmetricGroup (2 ^ d))
    (v : J × Fin (2 ^ d)) (a : Fin d × J × Fin 2) : J × Fin (2 ^ d) :=
  (a.2.1, (state a.2.1 a.1).symm
    (if a.2.2 = 0 then state v.1 a.1 v.2 else flipPermutation d a.1 (state v.1 a.1 v.2)))

lemma encounter_neighbor_cover (state : J → Fin d → SymmetricGroup (2 ^ d)) (v : J × Fin (2 ^ d)) :
    Finset.univ.filter ((encounterGraph state).Adj v) ⊆
      Finset.univ.image (encounterCandidate state v) := by
  classical
  intro w hw
  obtain ⟨_, i, hi⟩ := (Finset.mem_filter.mp hw).2
  rcases hi with hi | hi
  · refine Finset.mem_image.mpr ⟨(i, w.1, 0), Finset.mem_univ _, ?_⟩
    simp only [encounterCandidate, ↓reduceIte]
    rw [← hi, Equiv.symm_apply_apply]
  · refine Finset.mem_image.mpr ⟨(i, w.1, 1), Finset.mem_univ _, ?_⟩
    simp only [encounterCandidate, Fin.one_eq_zero_iff, Nat.reduceEqDiff, ↓reduceIte]
    rw [← hi, Equiv.symm_apply_apply]

lemma encounter_weighted_degree (state : J → Fin d → SymmetricGroup (2 ^ d))
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (v : J × Fin (2 ^ d)) :
    (∑ w ∈ Finset.univ.filter ((encounterGraph state).Adj v), p w.1) ≤
      2 * d * ∑ j, p j := by
  classical
  calc
    _ ≤ ∑ w ∈ Finset.univ.image (encounterCandidate state v), p w.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg (encounter_neighbor_cover state v) (fun w _ _ => hp w.1)
    _ ≤ ∑ a : Fin d × J × Fin 2, p (encounterCandidate state v a).1 :=
      Finset.sum_image_le_of_nonneg (fun w _ => hp w.1)
    _ = _ := by
      simp only [Fintype.sum_prod_type, encounterCandidate, Fin.sum_univ_two]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      ring

omit [DecidableEq J] in
lemma network_weights_total [DecidableEq J] (p : J → ℝ) :
    (∑ w : J × Fin (2 ^ d), p w.1) = (2 ^ d : ℕ) * ∑ j, p j := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]

theorem network_noIsolates_probability_bound
    (state : J → Fin d → SymmetricGroup (2 ^ d)) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (k : ℕ)
    (hmass : (2 ^ d : ℕ) * ∑ j, p j = k)
    (μ : Finset (J × Fin (2 ^ d)) → ℝ) (hμ : ∀ S, 0 ≤ μ S)
    (hcard : ∀ S, S.card ≠ k → μ S = 0)
    (hinc : ∀ T, (∑ S : Finset (J × Fin (2 ^ d)), if T ⊆ S then μ S else 0) ≤ ∏ w ∈ T, p w.1)
    (hΔ : 0 < 2 * (d : ℝ) * k / (2 ^ d : ℕ)) (hΔ1 : 2 * (d : ℝ) * k / (2 ^ d : ℕ) ≤ 1) :
    (∑ S : {S : Finset (J × Fin (2 ^ d)) // NoIsolatedVertex (encounterGraph state) S}, μ S.1) ≤
      (Real.sqrt (2 * (d : ℝ) * k / (2 ^ d : ℕ))) ^ k * Real.exp (Real.exp 2 * k) := by
  have hn : (2 ^ d : ℕ) ≠ 0 := ne_of_gt (pow_pos (by omega : 0 < (2 : ℕ)) _)
  have hmass' : (∑ j, p j) = (k : ℝ) / (2 ^ d : ℕ) :=
    (eq_div_iff (by exact_mod_cast hn)).2 (by rwa [mul_comm])
  apply noIsolates_probability_bound (encounterGraph state) (fun w => p w.1) k
    μ hμ hcard (fun w => hp w.1) (by rw [network_weights_total, hmass]) hΔ hΔ1 _ hinc
  intro v
  have h := encounter_weighted_degree state p hp v
  rwa [hmass', ← mul_div_assoc] at h

end SignedSweeps
end

end OAI
