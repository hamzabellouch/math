import OAI.Probability.SignedSweeps.SignedPairDimension
import OAI.Probability.SignedSweeps.PairDecomposition

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

lemma specht_dimension_entropy_upper {n : ℕ} (a : Partition n) :
    (spechtDimension a : ℝ) ≤ Real.exp (partsEntropy n a.1.rowLens) := by
  by_cases hn : n = 0
  · subst n
    simp only [spechtDimension_empty, Nat.cast_one, partsEntropy_partition_empty, Real.exp_zero, le_refl]
  have hnpos : (0:ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let := specht_irreducible a
  let f : ℂ →ₗ[ℂ] Specht a := LinearMap.toSpanSingleton ℂ (Specht a) (spechtRowVector a)
  have hf : f ≠ 0 := by
    intro hz
    have he := LinearMap.congr_fun hz 1
    exact spechtRowVector_ne_zero a (by simpa [f] using he)
  let p : Fin (a.1.colLen 0) → ℝ := fun i => (a.1.rowLen i : ℝ)/n
  have hp : ∀ i, 0 ≤ p i := by intro i; dsimp [p]; positivity
  have hsum : ∑ i, p i = 1 := by
    simp only [p, ← Finset.sum_div, ← Nat.cast_sum, a.sum_rowLen]
    exact div_self hnpos.ne'
  have hpos : ∀ x, 0 < p (a.rowIndex x) := by
    intro x
    exact div_pos (by exact_mod_cast a.rowLen_pos (a.rowIndex x)) hnpos
  have he := finrank_le_coloring_entropy (spechtRepresentation a) f hf a.rowIndex
    (fun g x => ⟨x, by
      have hg : g.1 ∈ rowSubgroup a := by rw [← fiberSubgroup_rowIndex]; exact g.2
      change spechtRepresentation a g.1 (x • spechtRowVector a) = x • spechtRowVector a
      rw [map_smul, spechtRowVector_invariant a ⟨g.1,hg⟩]⟩) p hp hsum hpos
  have hent : -(∑ x, Real.log (p (a.rowIndex x))) = partsEntropy n a.1.rowLens := by
    change -(∑ x, Real.log ((a.1.rowLen (a.rowOf x) : ℝ)/n)) = _
    rw [a.sum_rowOf (fun i => Real.log ((a.1.rowLen i : ℝ)/n)), partsEntropy_rowLen]
    have hl (x : ℝ) : Real.log (x / n) = -Real.log ((n : ℝ) / x) := by
      rw [← Real.log_inv, inv_div]
    simp only [hl, mul_neg, Finset.sum_neg_distrib, neg_neg]
  simpa only [hent, finrank_self, Nat.cast_one, mul_one, spechtDimension] using he

lemma specht_log_dimension_entropy_upper {n : ℕ} (a : Partition n) :
    Real.log (spechtDimension a : ℝ) ≤ partsEntropy n a.1.rowLens :=
  (Real.log_le_iff_le_exp (by exact_mod_cast spechtDimension_pos a)).mpr
    (specht_dimension_entropy_upper a)

lemma signedEntropy_split_sizes {u v n : ℕ} (h : u+v=n) (a : Partition u) (b : Partition v) :
    signedEntropy a b = partsEntropy u a.1.rowLens + partsEntropy v b.1.rowLens +
      (n : ℝ)*Real.log n - (u : ℝ)*Real.log u - (v : ℝ)*Real.log v := by
  have he : signedEntropy a b = partsEntropy n a.1.rowLens + partsEntropy n b.1.rowLens := by
    have hh : (u:ℝ)+v = n := by exact_mod_cast h
    simp only [signedEntropy, partsEntropy, hh, List.map_append, List.sum_append]
  rw [he,
    partsEntropy_rowLen_log a le_rfl _ (fun hu => Nat.cast_ne_zero.mpr (by omega)),
    partsEntropy_rowLen_log b le_rfl _ (fun hv => Nat.cast_ne_zero.mpr (by omega)),
    partsEntropy_rowLen_log a le_rfl _ (fun hu => Nat.cast_ne_zero.mpr hu),
    partsEntropy_rowLen_log b le_rfl _ (fun hv => Nat.cast_ne_zero.mpr hv)]
  have hh : (u:ℝ)+v = n := by exact_mod_cast h
  rw [← hh]
  ring

lemma log_choose_entropy_upper {u v n : ℕ} (h : u+v=n) :
    Real.log (n.choose u : ℝ) ≤
      (n : ℝ)*Real.log n - (u : ℝ)*Real.log u - (v : ℝ)*Real.log v +
        Real.log (n+1 : ℕ) + 1 := by
  have he : (n.choose u : ℝ) = (n.factorial : ℝ) / ((u.factorial : ℝ)*v.factorial) := by
    subst n
    exact Nat.cast_add_choose ℝ
  rw [he, Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  have hn := log_factorial_upper_uniform n n le_rfl
  have hu := log_factorial_lower u
  have hv := log_factorial_lower v
  have hh : (u:ℝ)+v = n := by exact_mod_cast h
  linarith

lemma induced_pair_dimension_entropy_upper {u v p : ℕ} (h : u+v=p)
    (a : Partition u) (b : Partition v) :
    ((p.choose u * spechtDimension a * spechtDimension b : ℕ) : ℝ) ≤
      Real.exp (signedEntropy a b + Real.log (p+1 : ℕ) + 1) := by
  have hc : (0:ℝ) < p.choose u := by exact_mod_cast Nat.choose_pos (by omega : u ≤ p)
  have hda : (0:ℝ) < spechtDimension a := by exact_mod_cast spechtDimension_pos a
  have hdb : (0:ℝ) < spechtDimension b := by exact_mod_cast spechtDimension_pos b
  apply (Real.log_le_iff_le_exp (show (0:ℝ) < ((p.choose u * spechtDimension a * spechtDimension b : ℕ) : ℝ) by
    simpa only [Nat.cast_mul] using mul_pos (mul_pos hc hda) hdb)).mp
  push_cast
  rw [Real.log_mul (by positivity) hdb.ne', Real.log_mul hc.ne' hda.ne']
  have ha := specht_log_dimension_entropy_upper a
  have hb := specht_log_dimension_entropy_upper b
  have hch := log_choose_entropy_upper h
  rw [signedEntropy_split_sizes h a b]
  push_cast at hch
  linarith

lemma pairTypeProjection_rank_entropy_upper {u v p : ℕ} (h : u+v=p)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    (finrank ℂ (pairTypeProjection h a b C).range : ℝ) ≤
      Real.exp (signedEntropy a b + Real.log (p+1 : ℕ) + 1) *
        (p+1 : ℝ)^(2*(Fintype.card C * Fintype.card C)) := by
  have ht : (finrank ℂ (pairTypeProjection h a b C).range : ℝ) ≤
     ((p.choose u * spechtDimension a * spechtDimension b : ℕ) : ℝ) *
       (p+1 : ℝ)^(2*(Fintype.card C * Fintype.card C)) := by
    exact_mod_cast pairTypeProjection_finrank_le h a b C
  exact ht.trans (mul_le_mul_of_nonneg_right (induced_pair_dimension_entropy_upper h a b) (by positivity))

end SignedSweeps
end

end OAI
