import OAI.Probability.SwitchChain.TripleCountEigenvalue
import OAI.Probability.SwitchChain.WeightedConditionalVariance

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.TripleCountLaw

def countKey (m : ℕ) (i : Fin 3) (x : Triple m) : Fin (m + 1) := x.val i

def decodedNat (a : Fin 3 → ℕ) (m : ℕ)
    (z : WeightedConditional.Space (Fin 3) (Fin (m + 1)))
    (i : Fin 3) (t : ℕ) : ℝ :=
  if h : t < m + 1 then WeightedConditional.decode (marginal a m) z i ⟨t, h⟩ else 0

@[simp] theorem decodedNat_fin (a : Fin 3 → ℕ) (m : ℕ)
    (z : WeightedConditional.Space (Fin 3) (Fin (m + 1)))
    (i : Fin 3) (t : Fin (m + 1)) :
    decodedNat a m z i t.val = WeightedConditional.decode (marginal a m) z i t := by
  simp [decodedNat, t.isLt]

theorem count_marginal_eq (a : Fin 3 → ℕ) (m : ℕ) (i : Fin 3) (t : Fin (m + 1)) :
    WeightedConditional.conditionalSum (probability a : Triple m → ℝ) (countKey m)
      i t (fun _ => 1) = marginal a m i t := by
  simp [WeightedConditional.conditionalSum, countKey, marginal]

theorem conditionalSum_ratio (a : Fin 3 → ℕ) (m : ℕ) (f : Triple m → ℝ)
    (i : Fin 3) (t : Fin (m + 1)) :
    WeightedConditional.conditionalSum (probability a) (countKey m) i t f /
      marginal a m i t = conditionalAverage a f (Equiv.swap 0 i) t.val := by
  rw [← normalized_conditionalAverage]
  simp only [WeightedConditional.conditionalSum, countKey, marginal,
    Equiv.swap_apply_left, Fin.val_eq_val]
  rfl

theorem rowSum_decodedNat (a : Fin 3 → ℕ) (m : ℕ)
    (z : WeightedConditional.Space (Fin 3) (Fin (m + 1))) :
    WeightedConditional.rowSum (marginal a m) (countKey m) z =
      rowSum (decodedNat a m z) := by
  funext x
  simp [WeightedConditional.rowSum, rowSum, countKey]

theorem count_gram_eigenvalue_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (z : WeightedConditional.Space (Fin 3) (Fin (m + 1)))
    (hz : z ∈ WeightedConditional.centered (marginal a m)) (hne : z ≠ 0)
    (lam : ℝ)
    (heig : WeightedConditional.gram (probability a : Triple m → ℝ)
      (marginal a m) (countKey m) z = lam • z) : lam ≤ 2 := by
  apply conditional_eigenvalue_le_two a m (decodedNat a m z) lam
  · intro i
    simp only [decodedNat_fin]
    simp_rw [WeightedConditional.marginal_mul_decode (marginal a m)
      (marginal_positive a m)]
    exact hz i
  · by_contra h
    push Not at h
    apply hne
    ext it
    obtain ⟨i, t⟩ := it
    have ht := h i t
    simp only [decodedNat_fin, WeightedConditional.decode] at ht
    exact (div_eq_zero_iff.mp ht).resolve_right
      (Real.sqrt_pos.mpr (marginal_positive a m i t)).ne'
  · intro i t ht
    let t' : Fin (m + 1) := ⟨t, by omega⟩
    have h := WeightedConditional.conditional_eigen_equation
      (probability a : Triple m → ℝ) (marginal a m) (marginal_positive a m)
      (countKey m) z lam heig i t'
    rw [rowSum_decodedNat, conditionalSum_ratio] at h
    simpa [decodedNat, t', show t < m + 1 by omega] using h

theorem count_row_variance_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → Fin (m + 1) → ℝ)
    (hb : ∀ i, ∑ t : Fin (m + 1), marginal a m i t * b i t = 0) :
    (∑ x : Triple m, probability a x * (∑ i : Fin 3, b i (x.val i)) ^ 2) ≤
      2 * ∑ i : Fin 3, ∑ t : Fin (m + 1), marginal a m i t * (b i t) ^ 2 := by
  apply WeightedConditional.centered_variance_le_of_eigenvalue_bound
    (probability a : Triple m → ℝ) (marginal a m) (marginal_positive a m)
    (countKey m) (count_marginal_eq a m) 2 _ b hb
  intro lam c hc hne heig
  let cNat : Fin 3 → ℕ → ℝ := fun i t =>
    if h : t < m + 1 then c i ⟨t, h⟩ else 0
  have hcNat (i : Fin 3) (t : Fin (m + 1)) : cNat i t.val = c i t := by
    dsimp only [cNat]
    rw [dite_eq_left t.isLt]
  apply conditional_eigenvalue_le_two a m cNat lam
  · intro i
    simpa only [hcNat] using hc i
  · obtain ⟨i, t, ht⟩ := hne
    exact ⟨i, t, by simpa only [hcNat] using ht⟩
  · intro i t ht
    let t' : Fin (m + 1) := ⟨t, by omega⟩
    have h := heig i t'
    rw [conditionalSum_ratio] at h
    have hr : (fun x : Triple m => ∑ j : Fin 3, c j (countKey m j x)) =
        rowSum cNat := by
      funext x
      simp only [rowSum, countKey, hcNat]
    rw [hr] at h
    simpa only [← hcNat] using h

def countExpectation (a : Fin 3 → ℕ) {m : ℕ} (f : Triple m → ℝ) : ℝ :=
  ∑ x : Triple m, probability a x * f x

def countVariance (a : Fin 3 → ℕ) {m : ℕ} (f : Triple m → ℝ) : ℝ :=
  countExpectation a (fun x => (f x - countExpectation a f) ^ 2)

theorem countExpectation_row (a : Fin 3 → ℕ) (m : ℕ)
    (i : Fin 3) (b : Fin (m + 1) → ℝ) :
    countExpectation a (fun x : Triple m => b (x.val i)) =
      ∑ t : Fin (m + 1), marginal a m i t * b t := by
  have h := WeightedConditional.sum_mul_conditionalSum
    (probability a : Triple m → ℝ) (countKey m) i b (fun _ => 1)
  simp only [count_marginal_eq, mul_one, countKey] at h
  unfold countExpectation
  rw [← h]
  exact Finset.sum_congr rfl (fun t _ => mul_comm _ _)

theorem countExpectation_sum (a : Fin 3 → ℕ) (m : ℕ)
    (f : Fin 3 → Triple m → ℝ) :
    countExpectation a (fun x => ∑ i, f i x) =
      ∑ i, countExpectation a (f i) := by
  unfold countExpectation
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem count_variance_sum_le_two (a : Fin 3 → ℕ) (m : ℕ)
    (b : Fin 3 → Fin (m + 1) → ℝ) :
    countVariance a (fun x : Triple m => ∑ i, b i (x.val i)) ≤
      2 * ∑ i : Fin 3, countVariance a (fun x : Triple m => b i (x.val i)) := by
  let μ : Fin 3 → ℝ := fun i => countExpectation a (fun x : Triple m => b i (x.val i))
  let c : Fin 3 → Fin (m + 1) → ℝ := fun i t => b i t - μ i
  have hc (i : Fin 3) : ∑ t, marginal a m i t * c i t = 0 := by
    simp only [c, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      marginal_sum, one_mul]
    exact sub_eq_zero.mpr (countExpectation_row a m i (b i)).symm
  have h := count_row_variance_le_two a m c hc
  have hleft : countVariance a (fun x : Triple m => ∑ i, b i (x.val i)) =
      ∑ x : Triple m, probability a x * (∑ i, c i (x.val i)) ^ 2 := by
    unfold countVariance
    rw [countExpectation_sum]
    simp only [countExpectation, c, Finset.sum_sub_distrib, μ]
  have hright (i : Fin 3) : countVariance a (fun x : Triple m => b i (x.val i)) =
      ∑ t, marginal a m i t * (c i t) ^ 2 := by
    exact countExpectation_row a m i (fun t => (c i t) ^ 2)
  rw [hleft]
  simp_rw [hright]
  exact h

end Problem315.TripleCountLaw

end

end OAI
