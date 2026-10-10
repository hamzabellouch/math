import OAI.NumberTheory.TwoPoint.Bounds.CenteredWordMajorant
import OAI.NumberTheory.TwoPoint.Bounds.ForcedSingletonDifference

namespace OAI

/-! Keep the nonnegative weight inside the expectation when it is independent of tuple residues. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem uniform_weighted_centered_word_majorant {ι τ : Type*}
    [Fintype ι] [Fintype τ] [DecidableEq ι]
    (B : ℕ) (p : ι → ℕ) (hp : ∀ i, 0 < p i) (hpB : ∀ i, p i ≤ B)
    (label : τ → ι) (target : τ → Fin B) (base : ι → Fin B)
    (htarget : ∀ t, (target t).val < p (label t))
    (R G : (ι → Fin B) → ℝ) (hR : ∀ x, 0 ≤ R x)
    (hRdep : ∀ x y, (∀ i, i ∉ univ.image label → x i = y i) → R x = R y) :
    |(FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
      (fun x => R x * (∏ t,
        ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x)| ≤
      ∑ U ∈ (nonsingletonSlots label).powerset,
        if LitConsistent (nonsingletonSlots label \ U) label target then
          designatedReciprocal p (singletonLabels label) (nonsingletonSlots label \ U) U label *
            (FiniteLaw.independent (fun i => uniformResidueLaw B (p i) (hp i) (hpB i))).average
              (fun x => R x * |selectedMixedDifference (singletonLabels label)
                (singletonTarget label target base)
                (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
                  (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x|)
        else 0 := by
  have hS : singletonLabels label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, ht⟩ := singleton_occurrence_exists label ⟨i, hi⟩
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  have hforce (U : Finset τ) (x : ι → Fin B) :
      R (forceCoordinates ((nonsingletonSlots label \ U).image label)
        (litForcedTarget (nonsingletonSlots label \ U) label target base) x) = R x := by
    apply hRdep
    intro i hi
    have hiT : i ∉ (nonsingletonSlots label \ U).image label := by
      intro hit
      obtain ⟨t, _, ht⟩ := mem_image.mp hit
      exact hi (mem_image.mpr ⟨t, mem_univ _, ht⟩)
    simp only [forceCoordinates_apply, hiT, ite_false]
  have hdelta (U : Finset τ) (x : ι → Fin B) :
      selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
        (fun y => R (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label target base) y) *
          G (forceCoordinates ((nonsingletonSlots label \ U).image label)
            (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x =
      R x * selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
        (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
          (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x := by
    simp_rw [hforce]
    exact selectedMixedDifference_invariant_factor _ _ hS _ x R _ hRdep
  have he : (fun x => R x * (∏ t,
      ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * G x) =
      (fun x => (1 : ℝ) * (∏ t,
      ((if x (label t) = target t then (1 : ℝ) else 0) - (p (label t) : ℝ)⁻¹)) * (R x * G x)) := by
    funext x
    ring
  rw [he]
  apply (uniform_centered_word_majorant B p hp hpB label target base htarget
    1 (by norm_num) (fun x => R x * G x)).trans_eq
  apply sum_congr rfl
  intro U _
  split_ifs
  · simp only [one_mul, hdelta, abs_mul, abs_of_nonneg (hR _)]
  · rfl

end TwoPointCorrelations

end OAI
