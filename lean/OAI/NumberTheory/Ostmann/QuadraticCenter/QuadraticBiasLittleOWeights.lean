import OAI.NumberTheory.Ostmann.QuadraticCenter.QuadraticBiasLittleOBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries Filter
open scoped BigOperators

lemma quadraticBadBandMass_eq_natural (d : Decomposition) (δ T : ℝ)
    (hQ : ⌊Real.exp (2*T)⌋₊ ≤ collisionScale 4 (parameterX T)) :
    quadraticBadBandMass d δ T =
      ∑ p ∈ (closedLogarithmicPrimeBand T).filter (fun p => p ≠ 2 ∧ δ ≤ quadraticBiasValue d p),
        Real.log p/p := by
  classical
  unfold quadraticBadBandMass
  rw [← primeWeight_image_val]
  congr 1
  ext p
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have hh := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨?_,?_⟩
    · rw [← boundedClosedLogarithmicPrimeBand_image _ _ hQ]
      exact Finset.mem_image.mpr ⟨q,hh.1,rfl⟩
    · simpa only [quadraticBiasValue_prime] using hh.2
  · intro hp
    have hh := Finset.mem_filter.mp hp
    rw [← boundedClosedLogarithmicPrimeBand_image _ _ hQ] at hh
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hh.1
    refine Finset.mem_image.mpr ⟨q,Finset.mem_filter.mpr ⟨hq,?_⟩,rfl⟩
    simpa only [quadraticBiasValue_prime] using hh.2

lemma eventually_closed_band_weight_le : ∀ᶠ T : ℝ in atTop,
    (∑ p ∈ closedLogarithmicPrimeBand T, Real.log p/p) ≤ 3*T := by
  filter_upwards [eventually_ge_atTop (Real.log 2),
    eventually_ge_atTop (Real.log 4+4)] with T hT hC
  have ht : Real.log 2 ≤ 2*T := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hf := log_floor_exp_bounds ht
  have hm := (abs_le.mp (mertens_prime_sum _ hf.1)).2
  have hs : (∑ p ∈ closedLogarithmicPrimeBand T, Real.log p/p) ≤
      ∑ p ∈ (⌊Real.exp (2*T)⌋₊).primesLE, Real.log p/p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro p hp hnot
    have hpp := (Nat.mem_primesLE.mp hp).2
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le)) (Nat.cast_nonneg _)
  linarith [hf.2.2]

lemma closed_band_bias_le_threshold (d : Decomposition) {δ T : ℝ}
    (hδ : 0 ≤ δ) (hT : Real.log 2 < T)
    (hQ : ⌊Real.exp (2*T)⌋₊ ≤ collisionScale 4 (parameterX T)) :
    (∑ p ∈ closedLogarithmicPrimeBand T, (Real.log p/p)*quadraticBiasValue d p) ≤
      δ*(∑ p ∈ closedLogarithmicPrimeBand T, Real.log p/p) + quadraticBadBandMass d δ T := by
  classical
  rw [quadraticBadBandMass_eq_natural d δ T hQ, Finset.sum_filter, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hh := mem_closedLogarithmicPrimeBand.mp hp
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    have hhlo := hh.2.1
    norm_num at hhlo
    linarith
  have hw : 0 ≤ Real.log p/(p : ℝ) :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast hh.1.one_le)) (Nat.cast_nonneg _)
  by_cases hb : δ ≤ quadraticBiasValue d p
  · rw [ite_eq_left ⟨hp2,hb⟩]
    have := mul_le_mul_of_nonneg_left (quadraticBiasValue_le_one d p) hw
    nlinarith [mul_nonneg hδ hw]
  · simp only [hb,and_false,ite_false,add_zero]
    exact (mul_le_mul_of_nonneg_left (le_of_not_ge hb) hw).trans_eq (mul_comm _ _)

end Ostmann.QuadraticCenter

end

end OAI
