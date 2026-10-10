import OAI.Analysis.CircleDomains.Selection.TorusProjection
import OAI.Analysis.CircleDomains.Modulus.LevelIncidence

namespace OAI

/-! The ordered compatibility null sets survive arbitrary finite selections
of a prior tuple, including tuples with repeated labels. -/

open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

variable {X : Type*} [TopologicalSpace X]

def levelRelation (H : ℕ → Set (UnitAddCircle × X)) (i : ℕ) : Set (X × UnitAddCircle) :=
  Prod.swap ⁻¹' H i

def OrderedLevelNullCompatibility (H : ℕ → Set (UnitAddCircle × X)) (F : Set X) : Prop :=
  ∀ (j n : ℕ) (l : Fin n → ℕ), (∀ k, l k < j) →
    ((volume : Measure UnitAddCircle).prod
      (volume : Measure (Fin n → UnitAddCircle)))
      (freeComponentFailure F (levelRelation H j) (levelRelation H) l) = 0

theorem ae_finite_tuple_ordered_compatibility
    (H : ℕ → Set (UnitAddCircle × X)) (F : Set X)
    (hP : OrderedLevelNullCompatibility H F) {n m : ℕ}
    (l : Fin n → ℕ) (r : Fin m → ℕ) :
    ∀ᵐ p ∂((volume : Measure (Fin n → UnitAddCircle)).prod
      (volume : Measure (Fin m → UnitAddCircle))),
      ∀ j : Fin m, ∀ A : Finset (Fin n), (∀ k ∈ A, l k < r j) →
        ∀ x ∈ F, (p.2 j, x) ∈ H (r j) →
          ¬ (connectedComponentIn (⋃ k ∈ A, {y | (p.1 k, y) ∈ H (l k)}) x).Nontrivial := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro A
  by_cases horder : ∀ k ∈ A, l k < r j
  · let e : Fin (Fintype.card A) → Fin n := fun k => ((Fintype.equivFin A).symm k).val
    have he : Injective e := Subtype.val_injective.comp (Fintype.equivFin A).symm.injective
    have hp := hP (r j) (Fintype.card A) (l ∘ e) (fun k =>
      horder (e k) ((Fintype.equivFin A).symm k).property)
    have hproj : MeasurePreserving
        (fun p : (Fin n → UnitAddCircle) × (Fin m → UnitAddCircle) => (p.2 j, p.1 ∘ e))
        (volume.prod volume) (volume.prod volume) := by
      exact Measure.measurePreserving_swap.comp
        ((torus_projection_measurePreserving e he).prod
          (measurePreserving_eval (fun _ : Fin m => (volume : Measure UnitAddCircle)) j))
    have hzero := hproj.quasiMeasurePreserving.preimage_null hp
    have hgood : ∀ᵐ p ∂((volume : Measure (Fin n → UnitAddCircle)).prod
        (volume : Measure (Fin m → UnitAddCircle))),
        (p.2 j, p.1 ∘ e) ∉ freeComponentFailure F (levelRelation H (r j))
          (levelRelation H) (l ∘ e) := by
      rw [ae_iff]
      simpa only [Set.preimage, not_not, ofPred_mem_eq] using hzero
    filter_upwards [hgood] with p hp
    intro _ x hx hj hnt
    apply hp
    have hset : {y | (y, p.1 ∘ e) ∈ finiteLevelUnionGraph (levelRelation H) (l ∘ e)} =
        ⋃ k ∈ A, {y | (p.1 k, y) ∈ H (l k)} := by
      ext y
      constructor
      · intro hy
        obtain ⟨k, hk⟩ := mem_iUnion.mp hy
        exact mem_iUnion₂.mpr ⟨e k, ((Fintype.equivFin A).symm k).property, hk⟩
      · intro hy
        obtain ⟨k, hk, hyk⟩ := mem_iUnion₂.mp hy
        refine mem_iUnion.mpr ⟨(Fintype.equivFin A) ⟨k, hk⟩, ?_⟩
        change (p.1 (e ((Fintype.equivFin A) ⟨k, hk⟩)), y) ∈
          H (l (e ((Fintype.equivFin A) ⟨k, hk⟩)))
        simpa only [e, Equiv.symm_apply_apply, mem_ofPred_eq] using hyk
    refine ⟨(x, p.2 j, p.1 ∘ e), ⟨hx, hj, ?_⟩, rfl⟩
    change (connectedComponentIn {y | (y, p.1 ∘ e) ∈
      finiteLevelUnionGraph (levelRelation H) (l ∘ e)} x).Nontrivial
    rwa [hset]
  · exact Eventually.of_forall fun _ h => (horder h).elim

end CircleDomainRigidity

end

end OAI
