import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalCardinality
import OAI.Combinatorics.BalancedRyser.Local.AlignedGlobalProduct

namespace OAI

namespace Balanced.Local.AlignedGlobal

open TupleAlignment AlignedUnused UniformConditionalProduct
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_rectangle_probability {A U : Type*}
    [Fintype A] [Fintype U] [Nonempty A] [Nonempty U]
    (E : A → Prop) (H : U → Prop) :
    ((PMF.uniformOfFintype (A × U)).toOuterMeasure {z | E z.1 ∧ H z.2}).toReal =
      ((PMF.uniformOfFintype A).toOuterMeasure {x | E x}).toReal *
      ((PMF.uniformOfFintype U).toOuterMeasure {u | H u}).toReal := by
  let e : {z : A × U // E z.1 ∧ H z.2} ≃ {x : A // E x} × {u : U // H u} :=
    { toFun := fun z => (⟨z.1.1,z.2.1⟩, ⟨z.1.2,z.2.2⟩)
      invFun := fun z => ⟨(z.1.1,z.2.1),z.1.2,z.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Fintype.card_congr e
  rw [PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  change (Fintype.card {z : A × U // E z.1 ∧ H z.2} : ℝ) /
      Fintype.card (A × U) =
    (Fintype.card {x : A // E x} : ℝ) / Fintype.card A *
      ((Fintype.card {u : U // H u} : ℝ) / Fintype.card U)
  rw [hc, Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul,
    div_mul_div_comm]

theorem uniform_coordinate_cylinder {I V : Type*}
    [Fintype I] [Fintype V] [DecidableEq I] [Nonempty V]
    (J : Finset I) (x : I → V) :
    ((PMF.uniformOfFintype (I → V)).toOuterMeasure
      {f | ∀ j ∈ J, f j = x j}).toReal = (Fintype.card V : ℝ)⁻¹ ^ J.card := by
  let e : J ↪ I := ⟨Subtype.val, Subtype.val_injective⟩
  have h := congrArg (fun law => (law.toOuterMeasure {fun j : J => x j}).toReal)
    (uniform_map_restrict (A := V) e)
  rw [PMF.toOuterMeasure_map_apply] at h
  have he : (fun f : I → V => fun j : J => f (e j)) ⁻¹' {fun j : J => x j} =
      {f | ∀ j ∈ J, f j = x j} := by
    ext f
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · intro hf j hj
      exact congrFun hf ⟨j,hj⟩
    · intro hf
      funext j
      exact hf j j.2
  rw [he, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply] at h
  simpa only [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast, Fintype.card_fun,
    Fintype.card_coe, Nat.cast_pow, inv_pow] using h

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def FreePointCylinder {b κ : ℕ} (P : EqualityPattern b κ) (R : Finset (Fin b))
    (a : DirectionAssignment F b κ) (bits : Bits b) (p : Point F)
    (J : Finset (FreeIndex P R)) (x : FreeIndex P R → F) (M : MergedPairs F) : Prop :=
  ∀ ij ∈ J, prescribedPoint P a bits M ij.1 =
    ((linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm (x ij)).1

theorem generated_freePointCylinder_iff {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (R : Finset (Fin b))
    (hD : (RootChildPartition.dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (J : Finset (FreeIndex P R)) (x : FreeIndex P R → F)
    (z : (FreeIndex P R → F) × UnusedArray P a) :
    FreePointCylinder P R a bits p J x
      ((coordinateEquiv P hκ R hD a ha bits p).symm z).1 ↔
        ∀ ij ∈ J, z.1 ij = x ij := by
  constructor
  · intro h ij hij
    have hp := h ij hij
    rw [generated_free P hκ R hD a ha bits p z ij] at hp
    exact (linePointEquiv (a.1 ij.1.1) (lineEval (a.1 ij.1.1) p)).symm.injective
      (Subtype.ext hp)
  · intro h ij hij
    rw [generated_free P hκ R hD a ha bits p z ij, h ij hij]

theorem aligned_freePointCylinder_unused {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (R : Finset (Fin b))
    (hD : (RootChildPartition.dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (J : Finset (FreeIndex P R)) (x : FreeIndex P R → F)
    (H : UnusedArray P a → Prop) :
    conditionedOffsetProbability (Aligned P a bits p)
      (fun M => FreePointCylinder P R a bits p J x M ∧ H ((split P a M).2)) =
      (Fintype.card F : ℝ)⁻¹ ^ J.card *
        ((PMF.uniformOfFintype (UnusedArray P a)).toOuterMeasure {u | H u}).toReal := by
  rw [conditioned_probability_eq_uniform_coordinates P hκ R hD a ha bits p]
  have hevent :
      {z : (FreeIndex P R → F) × UnusedArray P a |
        FreePointCylinder P R a bits p J x
          ((coordinateEquiv P hκ R hD a ha bits p).symm z).1 ∧
        H ((split P a ((coordinateEquiv P hκ R hD a ha bits p).symm z).1).2)} =
      {z | (∀ ij ∈ J, z.1 ij = x ij) ∧ H z.2} := by
    ext z
    have hu : (split P a ((coordinateEquiv P hκ R hD a ha bits p).symm z).1).2 =
        z.2 := by
      funext d
      exact generated_unused P hκ R hD a ha bits p z d
    simp only [Set.mem_ofPred_eq, generated_freePointCylinder_iff, hu]
  rw [hevent]
  have hr := uniform_rectangle_probability
    (fun f : FreeIndex P R → F => ∀ ij ∈ J, f ij = x ij) H
  rw [uniform_coordinate_cylinder J x] at hr
  exact hr

theorem aligned_freePointCylinder {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (R : Finset (Fin b))
    (hD : (RootChildPartition.dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (J : Finset (FreeIndex P R)) (x : FreeIndex P R → F) :
    conditionedOffsetProbability (Aligned P a bits p)
      (FreePointCylinder P R a bits p J x) = (Fintype.card F : ℝ)⁻¹ ^ J.card := by
  simpa using
    aligned_freePointCylinder_unused P hκ R hD a ha bits p J x (fun _ => True)

theorem original_aligned_freePointCylinder_unused {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (R : Finset (Fin b))
    (hD : (RootChildPartition.dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (J : Finset (FreeIndex P R)) (x : FreeIndex P R → F)
    (H : UnusedArray P a → Prop) :
    offsetProbability (fun M => Aligned P a bits p M ∧
      FreePointCylinder P R a bits p J x M ∧ H ((split P a M).2)) =
      (1 / (Fintype.card F : ℝ) ^ (4*b)) *
        (Fintype.card F : ℝ)⁻¹ ^ J.card *
        ((PMF.uniformOfFintype (UnusedArray P a)).toOuterMeasure {u | H u}).toReal := by
  have h := aligned_freePointCylinder_unused P hκ R hD a ha bits p J x H
  unfold conditionedOffsetProbability at h
  have hm := (div_eq_iff (ne_of_gt (alignment_probability_pos P hκ a ha bits p))).mp h
  rw [alignment_probability P hκ a ha bits p] at hm
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hm

theorem aligned_unused_conditioned_freePointCylinder {b κ : ℕ}
    (P : EqualityPattern b κ) (hκ : κ ≤ 2) (R : Finset (Fin b))
    (hD : (RootChildPartition.dependentOccurrences P R).card = 2*κ)
    (a : DirectionAssignment F b κ) (ha : Eligible P a) (bits : Bits b) (p : Point F)
    (J : Finset (FreeIndex P R)) (x : FreeIndex P R → F)
    (H : UnusedArray P a → Prop)
    (hH : 0 < ((PMF.uniformOfFintype (UnusedArray P a)).toOuterMeasure {u | H u}).toReal) :
    conditionedOffsetProbability
      (fun M => Aligned P a bits p M ∧ H ((split P a M).2))
      (FreePointCylinder P R a bits p J x) = (Fintype.card F : ℝ)⁻¹ ^ J.card := by
  have hn := original_aligned_freePointCylinder_unused P hκ R hD a ha bits p J x H
  have hd := original_aligned_freePointCylinder_unused P hκ R hD a ha bits p
    (∅ : Finset (FreeIndex P R)) x H
  simp only [FreePointCylinder, Finset.forall_mem_empty_iff, true_and,
    Finset.card_empty, pow_zero, mul_one] at hd
  unfold conditionedOffsetProbability
  have he : (fun M => (Aligned P a bits p M ∧ H ((split P a M).2)) ∧
      FreePointCylinder P R a bits p J x M) =
      (fun M => Aligned P a bits p M ∧
        FreePointCylinder P R a bits p J x M ∧ H ((split P a M).2)) := by
    funext M
    exact propext (by tauto)
  rw [he, hn, hd]
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hp : (1 / (Fintype.card F : ℝ) ^ (4*b)) ≠ 0 := by positivity
  have hHne := ne_of_gt hH
  field_simp [hHne]

end
end Balanced.Local.AlignedGlobal

end OAI
