import OAI.NumberTheory.TwoPoint.Bounds.ForcedSingletonDifference
import OAI.NumberTheory.TwoPoint.Bounds.CenteredWordExpansion

namespace OAI

/-! A nonzero selected difference has one surviving hybrid, preserving all exterior weights. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma selected_difference_nonzero_hybrid {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (S : Finset ι) (a x : ι → A) (G : (ι → A) → ℝ)
    (hG : selectedMixedDifference S a G x ≠ 0) :
    ∃ y : ι → A, (∀ i, i ∉ S → y i = x i) ∧ G y ≠ 0 := by
  obtain ⟨T, hT⟩ := exists_forced_value_ne_zero (fun i : S => a i)
    (fun z : S → A => G (joinCoordinates S z (fun i : {i // i ∉ S} => x i)))
    (fun i : S => x i) hG
  refine ⟨joinCoordinates S (forceCoordinates T (fun i : S => a i) (fun i : S => x i))
    (fun i : {i // i ∉ S} => x i), ?_, hT⟩
  intro i hi
  simp only [joinCoordinates, hi, dite_false]

theorem selected_forced_nonzero_hybrid {ι A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]
    (S T M : Finset ι) (hS : S ⊆ M) (hT : T ⊆ M)
    (a b x : ι → A) (G weight : (ι → A) → ℝ)
    (hweight : ∀ y z, (∀ i, i ∉ M → y i = z i) → weight y = weight z)
    (hG : selectedMixedDifference S a (fun y => G (forceCoordinates T b y)) x ≠ 0) :
    ∃ y : ι → A, (∀ i, i ∉ M → y i = x i) ∧
      (∀ i ∈ T, y i = b i) ∧ weight y = weight x ∧ G y ≠ 0 := by
  obtain ⟨z, hz, hGz⟩ := selected_difference_nonzero_hybrid S a x
    (fun y => G (forceCoordinates T b y)) hG
  have he : ∀ i, i ∉ M → forceCoordinates T b z i = x i := by
    intro i hi
    have hiT : i ∉ T := fun hit => hi (hT hit)
    have hiS : i ∉ S := fun his => hi (hS his)
    simpa only [forceCoordinates_apply, hiT, ite_false] using hz i hiS
  exact ⟨forceCoordinates T b z, he, (fun i hi => by simp only [forceCoordinates_apply, hi, ite_true]),
    hweight _ _ he, hGz⟩

theorem centered_word_nonzero_hybrid {ι τ A : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype τ] [DecidableEq τ] [Fintype A] [DecidableEq A]
    (label : τ → ι) (target : τ → A) (base x : ι → A) (U : Finset τ)
    (G weight : (ι → A) → ℝ)
    (hweight : ∀ y z, (∀ i, i ∉ univ.image label → y i = z i) → weight y = weight z)
    (hL : LitConsistent (nonsingletonSlots label \ U) label target)
    (hG : selectedMixedDifference (singletonLabels label) (singletonTarget label target base)
      (fun y => G (forceCoordinates ((nonsingletonSlots label \ U).image label)
        (litForcedTarget (nonsingletonSlots label \ U) label target base) y)) x ≠ 0) :
    ∃ y : ι → A, (∀ i, i ∉ univ.image label → y i = x i) ∧
      (∀ t ∈ nonsingletonSlots label \ U, y (label t) = target t) ∧
      weight y = weight x ∧ G y ≠ 0 := by
  have hS : singletonLabels label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, ht⟩ := singleton_occurrence_exists label ⟨i, hi⟩
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  have hT : (nonsingletonSlots label \ U).image label ⊆ univ.image label := by
    intro i hi
    obtain ⟨t, _, ht⟩ := mem_image.mp hi
    exact mem_image.mpr ⟨t, mem_univ _, ht⟩
  obtain ⟨y, hy, hylit, hyw, hyG⟩ := selected_forced_nonzero_hybrid (singletonLabels label)
    ((nonsingletonSlots label \ U).image label) (univ.image label) hS hT
    (singletonTarget label target base) (litForcedTarget (nonsingletonSlots label \ U) label target base)
    x G weight hweight hG
  refine ⟨y, hy, ?_, hyw, hyG⟩
  intro t ht
  rw [hylit _ (mem_image.mpr ⟨t, ht, rfl⟩), litForcedTarget_at _ _ _ _ hL t ht]

end TwoPointCorrelations

end OAI
