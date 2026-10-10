import OAI.NumberTheory.JointDickman.Probability.RootSiteLaw

namespace OAI

/-! # The root law after conditioning a prime to miss all block sites -/

namespace JointDickman
open Finset

theorem root_site_uniform_restricted_mean {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (root : ι → ZMod p) (hinj : Set.InjOn root I)
    (U : Finset (ZMod p)) (hU : 0 < U.card) (hroot : ∀ i ∈ I, root i ∈ U)
    (F : Finset ι → ℝ) :
    (∑ r ∈ U, F (rootHitSet I root r))/(U.card : ℝ) =
      ∑ S ∈ I.powerset, categoricalSubsetMass I (fun _ => 1/(U.card : ℝ)) S * F S := by
  classical
  simp_rw [rootHitSet_test_identity I root hinj F]
  rw [sum_add_distrib, sum_comm, categorical_mass_test]
  have he (i : ι) (hi : i ∈ I) : (∑ r ∈ U, if root i = r then F {i}-F ∅ else 0) =
      F {i}-F ∅ := by simp [eq_comm,hroot i hi]
  rw [sum_congr rfl he]
  simp only [sum_const, nsmul_eq_mul, sum_sub_distrib, ← mul_sum]
  have hc : (U.card : ℝ) ≠ 0 := by exact_mod_cast hU.ne'
  field_simp
  ring

theorem root_site_uniform_outside_mean {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} [NeZero p] (root : ι → ZMod p)
    (hinj : Set.InjOn root I) (forbidden : Finset (ZMod p)) (hsize : forbidden.card < p)
    (havoid : ∀ i ∈ I, root i ∉ forbidden) (F : Finset ι → ℝ) :
    (∑ r ∈ univ \ forbidden, F (rootHitSet I root r))/((p-forbidden.card : ℕ) : ℝ) =
      ∑ S ∈ I.powerset,
        categoricalSubsetMass I (fun _ => 1/((p-forbidden.card : ℕ) : ℝ)) S * F S := by
  classical
  have hc : (univ \ forbidden).card = p-forbidden.card := by
    rw [card_sdiff_of_subset (subset_univ forbidden),card_univ,ZMod.card]
  have hpos : 0 < (univ \ forbidden).card := by rw [hc]; omega
  have h := root_site_uniform_restricted_mean I root hinj (univ \ forbidden) hpos
    (fun i hi => mem_sdiff.mpr ⟨mem_univ _,havoid i hi⟩) F
  simpa only [hc] using h

end JointDickman

end OAI
