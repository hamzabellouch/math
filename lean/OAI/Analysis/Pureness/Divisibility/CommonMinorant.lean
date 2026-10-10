import OAI.Analysis.Pureness.Traces.TraceCyclicCFC
import OAI.Analysis.Pureness.Cuntz.CuntzPolar

namespace OAI
namespace CuntzPureness
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_nonzero_cross (hsimple : TopologicallySimple A) (e f : A)
    (he : e ≠ 0) (hf : 0 ≤ f) (hf0 : f ≠ 0) : ∃ z : A, e * z * f ≠ 0 := by
  obtain ⟨n, s, hs⟩ := fullness hsimple f hf hf0
  by_contra hnone
  have hz (z : A) : e * z * f = 0 := by
    by_contra hne
    exact hnone ⟨z, hne⟩
  apply he
  calc
    e = e * (∑ i : Fin n, star (s i) * f * s i) := by rw [hs, mul_one]
    _ = ∑ i : Fin n, (e * star (s i) * f) * s i := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    _ = 0 := by simp only [hz, zero_mul, Finset.sum_const_zero]

theorem exists_common_minorant (hsimple : TopologicallySimple A) (e f : A)
    (he : 0 ≤ e) (he0 : e ≠ 0) (hf : 0 ≤ f) (hf0 : f ≠ 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧ CuntzSubequiv h e ∧ CuntzSubequiv h f ∧
      ∀ τ : TracialState A,
        normalizedRootRank τ h ≤ normalizedRootRank τ e ∧
        normalizedRootRank τ h ≤ normalizedRootRank τ f := by
  obtain ⟨z, hz⟩ := exists_nonzero_cross hsimple e f he0 hf hf0
  let v := e * z * f
  have hv : v ≠ 0 := hz
  have hvm : v * star v ∈ hereditaryCarrier e := by
    apply subset_closure
    refine ⟨z * f * f * star z, ?_⟩
    simp only [v, star_mul, he.star_eq, hf.star_eq, mul_assoc]
  have hsm : star v * v ∈ hereditaryCarrier f := by
    apply subset_closure
    refine ⟨star z * e * e * z, ?_⟩
    simp only [v, star_mul, he.star_eq, hf.star_eq, mul_assoc]
  have hne : star v * v ≠ 0 := by
    intro heq
    have hn : ‖v‖ * ‖v‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, heq, norm_zero]
    rcases mul_eq_zero.mp hn with hn | hn
    all_goals exact hv (norm_eq_zero.mp hn)
  refine ⟨star v * v, star_mul_self_nonneg v, hne, ?_,
    hereditary_cuntzSubequiv f _ hf (star_mul_self_nonneg v) hsm, ?_⟩
  · exact (star_mul_self_cuntzSubequiv v).trans
      (hereditary_cuntzSubequiv e _ he (mul_star_self_nonneg v) hvm)
  · intro τ
    constructor
    · rw [rank_star_mul_self τ v]
      exact hereditary_rank_domination τ e _ he (mul_star_self_nonneg v) hvm
    · exact hereditary_rank_domination τ f _ hf (star_mul_self_nonneg v) hsm

theorem exists_finite_common_minorant [Nontrivial A] (hsimple : TopologicallySimple A)
    {ι : Type*} (I : Finset ι) (e : ι → A)
    (he : ∀ i ∈ I, 0 ≤ e i) (he0 : ∀ i ∈ I, e i ≠ 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧
      (∀ i ∈ I, CuntzSubequiv h (e i)) ∧
      (∀ τ : TracialState A, ∀ i ∈ I, normalizedRootRank τ h ≤ normalizedRootRank τ (e i)) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, zero_le_one, one_ne_zero, by simp, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨h, hh, hh0, hhC, hhR⟩ := ih
      (fun j hj => he j (Finset.mem_insert_of_mem hj))
      (fun j hj => he0 j (Finset.mem_insert_of_mem hj))
    obtain ⟨k, hk, hk0, hkh, hki, hkr⟩ := exists_common_minorant hsimple h (e i)
      hh hh0 (he i (Finset.mem_insert_self i I)) (he0 i (Finset.mem_insert_self i I))
    refine ⟨k, hk, hk0, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hki
      · exact hkh.trans (hhC j hj)
    · intro τ j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hkr τ).2
      · exact (hkr τ).1.trans (hhR τ j hj)
end CuntzPureness

end OAI
