import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarPrefixCoefficient

namespace OAI

section

noncomputable section
open scoped BigOperators
open Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

def scalarTentVector (n : ℕ) (v : Fin n → ℝ) (l r s : Fin (n+1)) (h : ℝ) (i : Fin n) : ℝ :=
  (2*scalarPrefixVector n v r i-scalarPrefixVector n v l i-scalarPrefixVector n v s i)/h

theorem scalarLevelField_prefixVector (n : ℕ) (v : Fin n → ℝ) (j k : Fin (n+1)) :
    scalarLevelField n v j (coordinateVector n (scalarPrefixVector n v k))=
      scalarPrefixVariance n v (min j k) := by
  rw [scalarLevelField_vector]
  unfold scalarPrefixVariance scalarPrefixVector
  apply Finset.sum_congr rfl
  intro i _
  have he : i.val<(min j k).val ↔ i.val<j.val ∧ i.val<k.val := by
    change i.val < min j.val k.val ↔ _
    exact lt_min_iff
  simp only [he]
  by_cases hj : i.val<j.val <;> by_cases hk : i.val<k.val <;> simp [hj,hk,pow_two]

theorem scalarLevelField_tentVector (n : ℕ) (v : Fin n → ℝ) (l r s j : Fin (n+1)) (h : ℝ) :
    scalarLevelField n v j (coordinateVector n (scalarTentVector n v l r s h))=
      (2*scalarPrefixVariance n v (min j r)-scalarPrefixVariance n v (min j l)-
        scalarPrefixVariance n v (min j s))/h := by
  rw [scalarLevelField_vector]
  conv_rhs => rw [← scalarLevelField_prefixVector,← scalarLevelField_prefixVector,← scalarLevelField_prefixVector]
  simp only [scalarLevelField_vector,Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  unfold scalarTentVector
  split_ifs <;> ring

theorem scalarPrefixVariance_monotone_tent (n : ℕ) (v : Fin n → ℝ) :
    Monotone (scalarPrefixVariance n v) := by
  intro j k hjk
  apply Finset.sum_le_sum
  intro i _
  unfold scalarPrefixVector
  by_cases hij : i.val<j.val
  · have hik : i.val<k.val := lt_of_lt_of_le hij (show j.val≤k.val from hjk)
    simp only [hij,hik,ite_true,le_refl]
  · simp only [hij,ite_false,zero_pow (by norm_num : (2:ℕ)≠0)]
    exact sq_nonneg _

theorem scalarTentVector_prefix_bounds (n : ℕ) (v : Fin n → ℝ) (l r s : Fin (n+1))
    (hlr : l ≤ r) (hrs : r ≤ s) {h B : ℝ} (hh : 0<h) (hB : 0≤B)
    (hleft : scalarPrefixVariance n v r-scalarPrefixVariance n v l=B*h)
    (hright : scalarPrefixVariance n v s-scalarPrefixVariance n v r=B*h)
    (j : Fin (n+1)) :
    scalarLevelField n v j (coordinateVector n (scalarTentVector n v l r s h))∈Icc (0:ℝ) B ∧
      (j ≤ l ∨ s ≤ j → scalarLevelField n v j (coordinateVector n (scalarTentVector n v l r s h))=0) := by
  rw [scalarLevelField_tentVector]
  have hm := scalarPrefixVariance_monotone_tent n v
  rcases le_total j l with hj|hj
  · simp only [min_eq_left hj,min_eq_left (hj.trans hlr),min_eq_left (hj.trans (hlr.trans hrs))]
    have he : (2*scalarPrefixVariance n v j-scalarPrefixVariance n v j-scalarPrefixVariance n v j)/h=0 := by ring
    simp only [he]
    exact ⟨⟨le_rfl,hB⟩,fun _ => trivial⟩
  rcases le_total j r with hjr|hjr
  · simp only [min_eq_left hjr,min_eq_right hj,min_eq_left (hjr.trans hrs)]
    have hlow := hm hj
    have hhigh := hm hjr
    constructor
    · constructor
      · apply (le_div_iff₀ hh).mpr; nlinarith
      · apply (div_le_iff₀ hh).mpr; nlinarith
    · rintro (H|H)
      · have he : j=l := le_antisymm H hj
        subst j
        ring
      · have h1 := hm H
        have hn : 2*scalarPrefixVariance n v j-scalarPrefixVariance n v l-scalarPrefixVariance n v j=0 := by nlinarith
        rw [hn,zero_div]
  rcases le_total j s with hjs|hjs
  · simp only [min_eq_right hjr,min_eq_right hj,min_eq_left hjs]
    have hlow := hm hjr
    have hhigh := hm hjs
    constructor
    · constructor
      · apply (le_div_iff₀ hh).mpr
        nlinarith
      · apply (div_le_iff₀ hh).mpr
        nlinarith
    · rintro (H|H)
      · have h1 := hm H
        have hn : 2*scalarPrefixVariance n v r-scalarPrefixVariance n v l-scalarPrefixVariance n v j=0 := by nlinarith
        rw [hn,zero_div]
      · have he : j=s := le_antisymm hjs H
        subst j
        have hn : 2*scalarPrefixVariance n v r-scalarPrefixVariance n v l-scalarPrefixVariance n v s=0 := by linarith
        rw [hn,zero_div]
  · simp only [min_eq_right hjr,min_eq_right hj,min_eq_right hjs]
    have hn : 2*scalarPrefixVariance n v r-scalarPrefixVariance n v l-scalarPrefixVariance n v s=0 := by linarith
    rw [hn,zero_div]
    exact ⟨⟨le_rfl,hB⟩,fun _ => rfl⟩

end SK.Analytic

end
end

end OAI
