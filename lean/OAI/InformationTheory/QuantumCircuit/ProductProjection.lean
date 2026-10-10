import OAI.InformationTheory.QuantumCircuit.Basic

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

@[simp] lemma tensorMatrix_one {N : ℕ} : tensorMatrix (fun _ : Fin N => (1 : QubitOperator)) = 1 := by
  classical
  ext x y
  simp only [tensorMatrix, Matrix.one_apply]
  by_cases h : x = y
  · subst y
    simp
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma tensorMatrix_mul {N : ℕ} (a b : Fin N → QubitOperator) :
    tensorMatrix a * tensorMatrix b = tensorMatrix (fun i => a i * b i) := by
  classical
  ext x y
  simp only [Matrix.mul_apply, tensorMatrix]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i z => a i (x i) z * b i z (y i))).symm

@[simp] lemma tensorMatrix_star {N : ℕ} (a : Fin N → QubitOperator) :
    star (tensorMatrix a) = tensorMatrix (fun i => star (a i)) := by
  classical
  ext x y
  simp [tensorMatrix, Matrix.star_apply]

lemma tensorMatrix_zero_of_zero {N : ℕ} (a : Fin N → QubitOperator)
    (i : Fin N) (hi : a i = 0) : tensorMatrix a = 0 := by
  classical
  ext x y
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

lemma tensorMatrix_projection {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, IsStarProjection (a i)) : IsStarProjection (tensorMatrix a) := by
  rw [isStarProjection_iff']
  constructor
  · rw [tensorMatrix_mul]
    congr 1
    funext i
    exact (ha i).isIdempotentElem.eq
  · rw [tensorMatrix_star]
    congr 1
    funext i
    exact (ha i).isSelfAdjoint.star_eq

lemma tensorMatrix_unitary {N : ℕ} (a : Fin N → QubitOperator)
    (ha : ∀ i, a i ∈ unitary QubitOperator) : tensorMatrix a ∈ unitary (Operator N) := by
  rw [Unitary.mem_iff]
  simp only [tensorMatrix_star, tensorMatrix_mul]
  constructor <;> convert tensorMatrix_one (N := N) using 1 <;>
    congr 1 <;> funext i
  · exact (Unitary.mem_iff.mp (ha i)).1
  · exact (Unitary.mem_iff.mp (ha i)).2

@[simp] lemma rankOne_star (v : Bit → ℂ) : star (rankOne v) = rankOne v := by
  ext x y
  simp [rankOne, Matrix.star_apply, mul_comm]

lemma normalized_complex {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    ∑ b, star (v b) * v b = 1 := by
  have h := congrArg (fun x : ℝ => (x : ℂ)) hv
  simp only [Complex.ofReal_sum, Complex.ofReal_one] at h
  simpa only [mul_comm, Complex.star_def, Complex.mul_conj] using h

lemma rankOne_projection {v : Bit → ℂ} (hv : ∑ b, Complex.normSq (v b) = 1) :
    IsStarProjection (rankOne v) := by
  rw [isStarProjection_iff']
  refine ⟨?_, rankOne_star v⟩
  ext x y
  simp only [Matrix.mul_apply, rankOne]
  calc
    _ = v x * (∑ z, star (v z) * v z) * star (v y) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      congr 1
      funext z
      ring
    _ = _ := by rw [normalized_complex hv]; ring

lemma Count.zero_projection {N : ℕ} (M : Count N) : IsStarProjection M.zero := by
  apply tensorMatrix_projection
  intro i
  split_ifs with hi
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

lemma Count.pattern_projection {N : ℕ} (M : Count N) (F : Finset (Fin N)) :
    IsStarProjection (M.pattern F) := by
  apply tensorMatrix_projection
  intro i
  split_ifs with hi hF
  · exact (rankOne_projection (M.normalized i hi)).one_sub
  · exact rankOne_projection (M.normalized i hi)
  · exact IsStarProjection.one _

@[simp] lemma Count.pattern_empty {N : ℕ} (M : Count N) : M.pattern ∅ = M.zero := by
  simp [Count.pattern, Count.zero]

lemma Count.pattern_mul {N : ℕ} (M : Count N) {F G : Finset (Fin N)}
    (hF : F ⊆ M.support) (hG : G ⊆ M.support) :
    M.pattern F * M.pattern G = if F = G then M.pattern F else 0 := by
  classical
  by_cases hFG : F = G
  · subst G
    rw [ite_eq_left rfl, (M.pattern_projection F).isIdempotentElem.eq]
  rw [ite_eq_right hFG, Count.pattern, Count.pattern, tensorMatrix_mul]
  obtain ⟨i, hi⟩ : ∃ i, (i ∈ F ∧ i ∉ G) ∨ (i ∈ G ∧ i ∉ F) := by
    by_contra h
    push Not at h
    apply hFG
    ext i
    specialize h i
    aesop
  apply tensorMatrix_zero_of_zero _ i
  rcases hi with ⟨hiF, hiG⟩ | ⟨hiG, hiF⟩
  · simp only [ite_eq_left (hF hiF), ite_eq_left hiF, ite_eq_right hiG]
    exact (rankOne_projection (M.normalized i (hF hiF))).one_sub_mul_self
  · simp only [ite_eq_left (hG hiG), ite_eq_left hiG, ite_eq_right hiF]
    exact (rankOne_projection (M.normalized i (hG hiG))).mul_one_sub_self


lemma sum_powerset_prod_ite {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (S : Finset ι) (a b : ι → R) :
    ∑ F ∈ S.powerset, ∏ i ∈ S, (if i ∈ F then a i else b i) = ∏ i ∈ S, (a i + b i) := by
  classical
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro F hF
  have hFS : F ⊆ S := Finset.mem_powerset.mp hF
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hFS h, h⟩⟩
  · congr 1
    ext i
    simp

lemma prod_ite_mem {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid R]
    (S : Finset ι) (a b : ι → R) :
    ∏ i, (if i ∈ S then a i else b i) = (∏ i ∈ S, a i) * ∏ i ∈ Finset.univ \ S, b i := by
  classical
  rw [Finset.prod_ite]
  congr 1
  · simp
  · congr 1
    ext i
    simp

lemma tensorMatrix_sum_patterns {N : ℕ} (S : Finset (Fin N))
    (a b c : Fin N → QubitOperator) :
    (∑ F ∈ S.powerset, tensorMatrix (fun i =>
      if i ∈ S then (if i ∈ F then a i else b i) else c i)) =
      tensorMatrix (fun i => if i ∈ S then a i + b i else c i) := by
  classical
  ext x y
  simp only [Matrix.sum_apply]
  change (∑ F ∈ S.powerset, ∏ i, (if i ∈ S then (if i ∈ F then a i else b i) else c i) (x i) (y i)) =
    ∏ i, (if i ∈ S then a i + b i else c i) (x i) (y i)
  simp only [Matrix.ite_apply, Matrix.add_apply]
  simp_rw [prod_ite_mem S]
  rw [← Finset.sum_mul, sum_powerset_prod_ite]

@[simp] lemma Count.sum_pattern {N : ℕ} (M : Count N) :
    ∑ F ∈ M.support.powerset, M.pattern F = 1 := by
  classical
  unfold Count.pattern
  rw [tensorMatrix_sum_patterns]
  simp

lemma projection_sum {A ι : Type*} [Ring A] [StarRing A] (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0) :
    IsStarProjection (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    apply (hp i (Finset.mem_insert_self _ _)).add
    · apply ih
      · exact fun j hj => hp j (Finset.mem_insert_of_mem hj)
      · exact fun j hj k hk h => horth j (Finset.mem_insert_of_mem hj)
          k (Finset.mem_insert_of_mem hk) h
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      apply horth i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
      intro h
      exact hi (h ▸ hj)

lemma Count.high_eq_sum_filter {N : ℕ} (M : Count N) (r : ℝ) :
    M.high r = ∑ F ∈ M.support.powerset.filter (fun F => r ≤ (F.card : ℝ)), M.pattern F := by
  classical
  simp only [Count.high, Finset.sum_filter]

lemma Count.high_projection {N : ℕ} (M : Count N) (r : ℝ) : IsStarProjection (M.high r) := by
  classical
  rw [M.high_eq_sum_filter]
  apply projection_sum
  · exact fun F _ => M.pattern_projection F
  · intro F hF G hG hFG
    rw [M.pattern_mul (Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1)
      (Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1), ite_eq_right hFG]

lemma Count.high_mul_zero {N : ℕ} (M : Count N) {r : ℝ} (hr : 0 < r) :
    M.high r * M.zero = 0 := by
  classical
  rw [M.high_eq_sum_filter, Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro F hF
  rw [← M.pattern_empty, M.pattern_mul (Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1)
    (Finset.empty_subset _)]
  split_ifs with h
  · subst F
    have h' := (Finset.mem_filter.mp hF).2
    simp only [Finset.card_empty, Nat.cast_zero] at h'
    exact (not_le_of_gt hr h').elim
  · rfl

lemma Count.high_eq_zero {N : ℕ} (M : Count N) {r : ℝ} (hr : (N : ℝ) < r) : M.high r = 0 := by
  classical
  unfold Count.high
  apply Finset.sum_eq_zero
  intro F hF
  rw [ite_eq_right]
  have hFN : F.card ≤ N := by simpa using Finset.card_le_univ F
  have hFR : (F.card : ℝ) ≤ N := by exact_mod_cast hFN
  linarith


section SpectralAlgebra

variable {A ι : Type*} [CStarAlgebra A]

lemma orthogonal_sum_mul (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0) (c d : ι → ℝ) :
    (∑ i ∈ s, c i • p i) * (∑ i ∈ s, d i • p i) = ∑ i ∈ s, (c i * d i) • p i := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [smul_mul_smul_comm, (hp i hi).isIdempotentElem.eq]
  · intro j hj hji
    rw [smul_mul_smul_comm, horth i hi j hj (Ne.symm hji), smul_zero]
  · intro h
    exact (h hi).elim

lemma orthogonal_sum_star (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i)) (c : ι → ℝ) :
    star (∑ i ∈ s, c i • p i) = ∑ i ∈ s, c i • p i := by
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [star_smul, star_trivial, (hp i hi).isSelfAdjoint.star_eq]

variable [PartialOrder A] [StarOrderedRing A]

lemma orthogonal_sum_norm_le (s : Finset ι) (p : ι → A)
    (hp : ∀ i ∈ s, IsStarProjection (p i))
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → p i * p j = 0)
    (hsum : ∑ i ∈ s, p i = 1) (c : ι → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i ∈ s, |c i| ≤ C) : ‖∑ i ∈ s, c i • p i‖ ≤ C := by
  have hsq : star (∑ i ∈ s, c i • p i) * (∑ i ∈ s, c i • p i) =
      ∑ i ∈ s, (c i)^2 • p i := by
    rw [orthogonal_sum_star s p hp c, orthogonal_sum_mul s p hp horth]
    simp only [pow_two]
  have hle : (∑ i ∈ s, (c i)^2 • p i) ≤ algebraMap ℝ A (C^2) := by
    calc
      _ ≤ ∑ i ∈ s, C^2 • p i := by
        apply Finset.sum_le_sum
        intro i hi
        apply smul_le_smul_of_nonneg_right _ (hp i hi).nonneg
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 (hc i hi)
      _ = _ := by rw [← Finset.smul_sum, hsum, Algebra.algebraMap_eq_smul_one]
  have hnorm := (CStarAlgebra.norm_le_iff_le_algebraMap _ (sq_nonneg C)
    (star_mul_self_nonneg (∑ i ∈ s, c i • p i))).2 (hsq ▸ hle)
  rw [CStarRing.norm_star_mul_self] at hnorm
  nlinarith only [hnorm, norm_nonneg (∑ i ∈ s, c i • p i), hC]

end SpectralAlgebra

open scoped MatrixOrder in
lemma Count.spectral_norm_le {N : ℕ} (M : Count N) (f : ℕ → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hf : ∀ k ≤ N, |f k| ≤ C) :
    ‖∑ F ∈ M.support.powerset, f F.card • M.pattern F‖ ≤ C := by
  refine orthogonal_sum_norm_le M.support.powerset M.pattern
    (fun F _ => M.pattern_projection F) ?_ M.sum_pattern _ hC ?_
  · intro F hF G hG hFG
    rw [M.pattern_mul (Finset.mem_powerset.mp hF) (Finset.mem_powerset.mp hG), ite_eq_right hFG]
  · intro F _
    apply hf
    simpa using Finset.card_le_univ F

end QAC

end

end OAI
