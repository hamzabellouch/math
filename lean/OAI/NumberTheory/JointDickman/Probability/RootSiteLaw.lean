import OAI.NumberTheory.JointDickman.Amplification.ConsecutiveCRT
import OAI.NumberTheory.JointDickman.Probability.BernoulliComparison

namespace OAI

/-! # Exact categorical law of distinct residue roots at one prime -/

namespace JointDickman
open Finset

noncomputable def rootHitSet {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (root : ι → ZMod p) (r : ZMod p) : Finset ι :=
  I.filter (fun i => root i = r)

theorem rootHitSet_singleton {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (root : ι → ZMod p) (hinj : Set.InjOn root I)
    {i : ι} (hi : i ∈ I) : rootHitSet I root (root i) = {i} := by
  classical
  ext j
  simp only [rootHitSet, mem_filter, mem_singleton]
  constructor
  · rintro ⟨hj,he⟩
    exact hinj hj hi he
  · rintro rfl
    exact ⟨hi,rfl⟩

theorem rootHitSet_test_identity {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (root : ι → ZMod p) (hinj : Set.InjOn root I)
    (F : Finset ι → ℝ) (r : ZMod p) :
    F (rootHitSet I root r) = F ∅+
      ∑ i ∈ I, if root i = r then F {i}-F ∅ else 0 := by
  classical
  by_cases h : ∃ i ∈ I, root i = r
  · obtain ⟨i,hi,rfl⟩ := h
    rw [rootHitSet_singleton I root hinj hi]
    have he (j : ι) (hj : j ∈ I) :
        (if root j = root i then F {j}-F ∅ else 0) =
          if j = i then F {j}-F ∅ else 0 := by
      have hh : root j = root i ↔ j = i := ⟨hinj hj hi, fun h => congrArg root h⟩
      simp only [hh]
    rw [sum_congr rfl he]
    simp [hi]
  · have hh (i : ι) (hi : i ∈ I) : root i ≠ r := fun he => h ⟨i,hi,he⟩
    have hzero : rootHitSet I root r = ∅ := by
      apply filter_eq_empty_iff.mpr
      exact hh
    rw [hzero]
    have hs : (∑ i ∈ I, if root i = r then F {i}-F ∅ else 0) = 0 :=
      sum_eq_zero (fun i hi => ite_eq_right (hh i hi))
    rw [hs,add_zero]

theorem categorical_mass_test {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (q : ι → ℝ) (F : Finset ι → ℝ) :
    (∑ S ∈ I.powerset, categoricalSubsetMass I q S * F S) =
      (1-∑ i ∈ I, q i)*F ∅+∑ i ∈ I, q i*F {i} := by
  classical
  unfold categoricalSubsetMass
  simp only [add_mul, sum_add_distrib, sum_mul, ite_mul, zero_mul]
  congr 1
  · simp
  · rw [sum_comm]
    apply sum_congr rfl
    intro i hi
    simp [mem_powerset, singleton_subset_iff, hi]

theorem root_site_uniform_mean {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} [NeZero p] (root : ι → ZMod p)
    (hinj : Set.InjOn root I) (F : Finset ι → ℝ) :
    (∑ r : ZMod p, F (rootHitSet I root r))/(p : ℝ) =
      ∑ S ∈ I.powerset, categoricalSubsetMass I (fun _ => 1/(p : ℝ)) S * F S := by
  classical
  simp_rw [rootHitSet_test_identity I root hinj F]
  rw [sum_add_distrib, sum_comm, categorical_mass_test]
  have he (i : ι) : (∑ r : ZMod p, if root i = r then F {i}-F ∅ else 0) =
      F {i}-F ∅ := by simp [eq_comm]
  simp_rw [he]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul, sum_sub_distrib,
    ← mul_sum]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
  field_simp
  ring

end JointDickman

end OAI
