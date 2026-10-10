import OAI.InformationTheory.QuantumCircuit.Count

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator symmDiff
open Matrix

namespace QAC

lemma Count.flip_pattern {N : ℕ} (M : Count N) (F G : Finset (Fin N)) :
    (M.flip F).pattern G = M.pattern (F ∆ G) := by
  classical
  dsimp only [Count.pattern, Count.flip]
  congr 1
  funext i
  by_cases hi : i ∈ M.support
  · have hv := rankOne_orthogonalVector (M.normalized i hi)
    by_cases hF : i ∈ F <;> by_cases hG : i ∈ G <;>
      simp [hi, hF, hG, Finset.mem_symmDiff, hv]
  · simp [hi]

lemma Count.high_mul_pattern {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) (r : ℝ) :
    M.high r * M.pattern F = if r ≤ (F.card : ℝ) then M.pattern F else 0 := by
  classical
  rw [Count.high, Finset.sum_mul, Finset.sum_eq_single F]
  · split_ifs with h
    · exact (M.pattern_projection F).isIdempotentElem.eq
    · exact zero_mul _
  · intro G hG hGF
    split_ifs
    · rw [M.pattern_mul (Finset.mem_powerset.mp hG) hF, ite_eq_right hGF]
    · exact zero_mul _
  · intro h
    exact (h (Finset.mem_powerset.mpr hF)).elim

lemma symmDiff_subset_of_subset {α : Type*} [DecidableEq α] {F G S : Finset α}
    (hF : F ⊆ S) (hG : G ⊆ S) : F ∆ G ⊆ S :=
  Finset.symmDiff_subset_union.trans (Finset.union_subset hF hG)

lemma card_le_add_symmDiff {α : Type*} [DecidableEq α] (F G : Finset α) :
    G.card ≤ F.card + (F ∆ G).card := by
  have h : G ⊆ F ∪ (F ∆ G) := by
    intro i hi
    by_cases hF : i ∈ F
    · exact Finset.mem_union_left _ hF
    · exact Finset.mem_union_right _ (Finset.mem_symmDiff.mpr (Or.inr ⟨hi,hF⟩))
  exact (Finset.card_le_card h).trans (Finset.card_union_le _ _)

lemma Count.high_flip_absorb {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) {r q : ℝ} (hrq : q + F.card ≤ r) :
    (M.flip F).high q * M.high r = M.high r := by
  classical
  rw [M.high_eq_sum_filter r, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G hG
  have hrG : r ≤ (G.card : ℝ) := (Finset.mem_filter.mp hG).2
  have hGs : G ⊆ M.support := Finset.mem_powerset.mp (Finset.mem_filter.mp hG).1
  have hFGs : F ∆ G ⊆ (M.flip F).support := symmDiff_subset_of_subset hF hGs
  have heq : M.pattern G = (M.flip F).pattern (F ∆ G) := by
    rw [M.flip_pattern, symmDiff_symmDiff_cancel_left]
  rw [heq, (M.flip F).high_mul_pattern _ hFGs, ite_eq_left]
  have hc : (G.card : ℝ) ≤ F.card + (F ∆ G).card := by exact_mod_cast card_le_add_symmDiff F G
  linarith

def Count.low {N : ℕ} (M : Count N) (r : ℝ) : Operator N := 1 - M.high r

lemma Count.low_projection {N : ℕ} (M : Count N) (r : ℝ) : IsStarProjection (M.low r) :=
  (M.high_projection r).one_sub

lemma Count.low_eq_sum {N : ℕ} (M : Count N) (r : ℝ) :
    M.low r = ∑ F ∈ M.support.powerset.filter (fun F => (F.card : ℝ) < r), M.pattern F := by
  classical
  rw [Count.low, ← M.sum_pattern]
  unfold Count.high
  rw [← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F _
  by_cases h : r ≤ (F.card : ℝ)
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

lemma norm_mul_le_right {A : Type*} [NormedRing A] (x y : A) (hx : ‖x‖ ≤ 1) :
    ‖x*y‖ ≤ ‖y‖ := (norm_mul_le _ _).trans (by nlinarith only [hx, norm_nonneg y])

lemma norm_mul_le_left {A : Type*} [NormedRing A] (x y : A) (hy : ‖y‖ ≤ 1) :
    ‖x*y‖ ≤ ‖x‖ := (norm_mul_le _ _).trans (by nlinarith only [hy, norm_nonneg x])

lemma Count.high_flip_norm {N : ℕ} (M : Count N) (F : Finset (Fin N))
    (hF : F ⊆ M.support) {r q : ℝ} (hrq : q + F.card ≤ r) (B : Operator N) :
    ‖M.high r * B * M.pattern F‖ ≤ ‖(M.flip F).high q * B * (M.flip F).zero‖ := by
  have habs := congrArg star (M.high_flip_absorb F hF hrq)
  simp only [star_mul, (M.high_projection r).isSelfAdjoint.star_eq,
    ((M.flip F).high_projection q).isSelfAdjoint.star_eq] at habs
  rw [M.flip_zero]
  calc
    _ = ‖M.high r * ((M.flip F).high q * B * M.pattern F)‖ := by rw [← mul_assoc, ← mul_assoc, habs]
    _ ≤ _ := norm_mul_le_right _ _ (IsStarProjection.norm_le _ (M.high_projection r))


lemma Count.generator_mul_pattern {N : ℕ} (M : Count N) (i : Fin N) (hi : i ∈ M.support)
    (F : Finset (Fin N)) :
    tensorMatrix (fun j => if j = i then 1-rankOne (M.vector i) else 1) * M.pattern F =
      if i ∈ F then M.pattern F else 0 := by
  classical
  rw [Count.pattern, tensorMatrix_mul]
  by_cases hiF : i ∈ F
  · rw [ite_eq_left hiF]
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp only [ite_eq_left hi, ite_eq_left hiF]
      exact (rankOne_projection (M.normalized i hi)).one_sub.isIdempotentElem.eq
    · simp only [ite_eq_right hji, one_mul]
  · rw [ite_eq_right hiF]
    apply tensorMatrix_zero_of_zero _ i
    simp only [ite_eq_left hi, ite_eq_right hiF]
    exact (rankOne_projection (M.normalized i hi)).one_sub_mul_self

lemma Count.operator_mul_pattern {N : ℕ} (M : Count N) (F : Finset (Fin N)) (hF : F ⊆ M.support) :
    M.operator * M.pattern F = (F.card : ℝ) • M.pattern F := by
  classical
  rw [Count.operator, Finset.sum_mul]
  calc
    _ = ∑ i ∈ M.support, if i ∈ F then M.pattern F else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact M.generator_mul_pattern i hi F
    _ = _ := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hF, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]

def Count.spectral {N : ℕ} (M : Count N) (f : ℕ → ℝ) : Operator N :=
  ∑ F ∈ M.support.powerset, f F.card • M.pattern F

lemma Count.operator_spectral {N : ℕ} (M : Count N) :
    M.operator = M.spectral (fun k => k) := by
  classical
  calc
    _ = M.operator * (∑ F ∈ M.support.powerset, M.pattern F) := by rw [M.sum_pattern,mul_one]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F hF
      exact M.operator_mul_pattern F (Finset.mem_powerset.mp hF)

lemma Count.spectral_mul {N : ℕ} (M : Count N) (f g : ℕ → ℝ) :
    M.spectral f * M.spectral g = M.spectral (fun k => f k * g k) := by
  classical
  exact orthogonal_sum_mul _ _ (fun F _ => M.pattern_projection F)
    (fun F hF G hG hFG => by
      rw [M.pattern_mul (Finset.mem_powerset.mp hF) (Finset.mem_powerset.mp hG),ite_eq_right hFG]) _ _

lemma Count.operator_pow_spectral {N : ℕ} (M : Count N) (k : ℕ) :
    M.operator^k = M.spectral (fun j => (j:ℝ)^k) := by
  induction k with
  | zero => simp [Count.spectral]
  | succ k ih => rw [pow_succ,ih,M.operator_spectral,M.spectral_mul]; simp only [pow_succ]

lemma Count.operator_norm_le {N : ℕ} (M : Count N) : ‖M.operator‖ ≤ N := by
  rw [M.operator_spectral]
  exact M.spectral_norm_le _ (by positivity) (fun k hk => by simpa using (show (k:ℝ) ≤ N by exact_mod_cast hk))

/-- Evaluate a real polynomial using the explicit integer spectral decomposition. -/
def Count.polynomial {N : ℕ} (M : Count N) (p : Polynomial ℝ) : Operator N :=
  M.spectral (fun k => p.eval (k:ℝ))

lemma Count.polynomial_eq_sum {N : ℕ} (M : Count N) (p : Polynomial ℝ) :
    M.polynomial p = ∑ k ∈ p.support, p.coeff k • M.operator^k := by
  classical
  unfold Count.polynomial Count.spectral
  simp_rw [Polynomial.eval_eq_sum, Polynomial.sum, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.smul_sum]
  change p.coeff k • M.spectral (fun j => (j:ℝ)^k) = _
  rw [← M.operator_pow_spectral]

lemma Count.generator_eq_restrict {N : ℕ} (M : Count N) (i : Fin N) (hi : i ∈ M.support) :
    tensorMatrix (fun j => if j = i then 1-rankOne (M.vector i) else 1) =
      ((M.flip M.support).restrict {i}).zero := by
  classical
  dsimp only [Count.zero, Count.restrict, Count.flip]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Finset.mem_inter, Finset.mem_singleton, hi, true_and, ite_true]
    exact (rankOne_orthogonalVector (M.normalized i hi)).symm
  · simp [hji]

/-- Ordered monomials, retaining multiplicities, with repeated coordinates collapsed. -/
def selectionSets {ι : Type*} [DecidableEq ι] (S : Finset ι) : ℕ → List (Finset ι)
  | 0 => [∅]
  | k+1 => S.toList.flatMap (fun i => (selectionSets S k).map (insert i))

lemma selectionSets_card {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ℕ) :
    ∀ F ∈ selectionSets S k, F.card ≤ k := by
  induction k with
  | zero => intro F hF; simpa [selectionSets] using hF
  | succ k ih =>
    intro F hF
    obtain ⟨i, _, hFi⟩ := List.mem_flatMap.mp hF
    obtain ⟨G, hG, rfl⟩ := List.mem_map.mp hFi
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (ih G hG) 1)

lemma selectionSets_length {ι : Type*} [DecidableEq ι] (S : Finset ι) (k : ℕ) :
    (selectionSets S k).length = S.card^k := by
  induction k with
  | zero => simp [selectionSets]
  | succ k ih => simp [selectionSets, List.length_flatMap, ih, pow_succ, mul_comm]

lemma list_sum_flatMap {ι κ A : Type*} [AddMonoid A] (l : List ι) (f : ι → List κ) (g : κ → A) :
    ((l.flatMap f).map g).sum = (l.map (fun i => ((f i).map g).sum)).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

lemma Count.selectionSets_sum {N : ℕ} (M : Count N) (S : Finset (Fin N)) (k : ℕ) :
    ((selectionSets S k).map (fun F => (M.restrict F).zero)).sum =
      (∑ i ∈ S, (M.restrict {i}).zero)^k := by
  classical
  induction k with
  | zero => simp [selectionSets,Count.zero,Count.restrict]
  | succ k ih =>
    rw [selectionSets, list_sum_flatMap]
    simp only [List.map_map]
    dsimp only [Function.comp_def]
    have hi : ∀ i, ((selectionSets S k).map (fun F => (M.restrict (insert i F)).zero)).sum =
        (M.restrict {i}).zero * ((selectionSets S k).map (fun F => (M.restrict F).zero)).sum := by
      intro i
      simp_rw [← Finset.singleton_union, ← M.restrict_zero_mul]
      exact List.sum_map_mul_left _ _ _
    simp_rw [hi,ih]
    rw [List.sum_map_mul_right, ← List.sum_toFinset _ S.nodup_toList, Finset.toList_toFinset, pow_succ']

lemma Count.operator_monomials {N : ℕ} (M : Count N) (k : ℕ) :
    M.operator^k = ((selectionSets M.support k).map
      (fun F => ((M.flip M.support).restrict F).zero)).sum := by
  rw [(M.flip M.support).selectionSets_sum]
  congr 1
  unfold Count.operator
  apply Finset.sum_congr rfl
  intro i hi
  exact M.generator_eq_restrict i hi

lemma list_norm_sum_le {A : Type*} [SeminormedAddCommGroup A] (l : List A) :
    ‖l.sum‖ ≤ (l.map norm).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.sum_cons,List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma list_norm_sum_le_const {ι A : Type*} [SeminormedAddCommGroup A]
    (l : List ι) (f : ι → A) (C : ℝ) (hf : ∀ i ∈ l, ‖f i‖ ≤ C) :
    ‖(l.map f).sum‖ ≤ l.length * C := by
  apply (list_norm_sum_le _).trans
  rw [List.map_map]
  have h := List.sum_le_length_nsmul (l.map (norm ∘ f)) C (by
    intro c hc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    exact hf i hi)
  simpa only [List.length_map, nsmul_eq_mul] using h


lemma Count.zero_spectral {N : ℕ} (M : Count N) :
    M.zero = M.spectral (fun k => if k = 0 then 1 else 0) := by
  classical
  unfold Count.spectral
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro F _ hF
    simp only [Finset.card_eq_zero, ite_eq_right hF, zero_smul]
  · simp

lemma Count.high_spectral {N : ℕ} (M : Count N) (r : ℝ) :
    M.high r = M.spectral (fun k => if r ≤ (k:ℝ) then 1 else 0) := by
  unfold Count.high Count.spectral
  apply Finset.sum_congr rfl
  intro F _
  split_ifs with h <;> simp only [h, ite_true, ite_false, one_smul, zero_smul]

lemma Count.low_spectral {N : ℕ} (M : Count N) (r : ℝ) :
    M.low r = M.spectral (fun k => if (k:ℝ) < r then 1 else 0) := by
  classical
  rw [M.low_eq_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro F _
  split_ifs with h <;> simp only [h, ite_true, ite_false, one_smul, zero_smul]

lemma Count.spectral_sub {N : ℕ} (M : Count N) (f g : ℕ → ℝ) :
    M.spectral f - M.spectral g = M.spectral (fun k => f k - g k) := by
  simp only [Count.spectral, sub_smul, Finset.sum_sub_distrib]

lemma Count.polynomial_error_low {N : ℕ} (M : Count N) (p : Polynomial ℝ)
    {r δ : ℝ} (hδ : 0 ≤ δ) (hp0 : p.eval 0 = 1)
    (hp : ∀ k : ℕ, 1 ≤ k → (k:ℝ) < r → |p.eval (k:ℝ)| ≤ δ) :
    ‖(M.zero - M.polynomial p) * M.low r‖ ≤ δ := by
  rw [M.zero_spectral, Count.polynomial, M.spectral_sub, M.low_spectral, M.spectral_mul]
  apply M.spectral_norm_le (fun k => ((if k = 0 then 1 else 0) - p.eval (k:ℝ)) *
    (if (k:ℝ) < r then 1 else 0)) hδ
  intro k _
  by_cases hk : k = 0
  · subst k; simpa [hp0] using hδ
  · by_cases hkr : (k:ℝ) < r
    · simpa [hk,hkr] using hp k (by omega) hkr
    · simpa [hkr] using hδ

end QAC

end

end OAI
