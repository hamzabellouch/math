import OAI.Combinatorics.BalancedRyser.Probability.TailPrescriptions2
import OAI.Combinatorics.BalancedRyser.Selection.SelectionTailCompletion

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.Tail
variable {I V : Type*} [Fintype I] [Fintype V]

def residualIndices (S : State I V) (J : Finset I) : Finset (Slot S) :=
  Finset.univ.filter (fun i => i.1 ∈ J)

omit [Fintype I] [Fintype V] in
@[simp] theorem mem_residualIndices (S : State I V) (J : Finset I) (i : Slot S) :
    i ∈ residualIndices S J ↔ i.1 ∈ J := by
  simp [residualIndices]

omit [Fintype I] [Fintype V] in

theorem complete_cylinder_iff (G : Input I V) (S : State I V)
    (fixed prescribed : I → V) (J : Finset I)
    (a : Slots.Assignment (Domain G S)) :
    (∀ i ∈ J, complete G S fixed a i = prescribed i) ↔
      (∀ i ∈ J, i ∉ S.remaining → fixed i = prescribed i) ∧
      a ∈ TailConditioning.ambientCylinder (Domain G S) (fun _ => Subtype.val)
        (residualIndices S J) (fun i => prescribed i.1) := by
  constructor
  · intro h
    constructor
    · intro i hi hr
      simpa only [complete_recorded G S fixed a i hr] using h i hi
    · intro i hi
      simpa only [complete_remaining] using h i.1 ((mem_residualIndices S J i).mp hi)
  · rintro ⟨hfixed, hremaining⟩ i hi
    by_cases hr : i ∈ S.remaining
    · simpa only [complete, dite_eq_left hr] using
        hremaining ⟨i, hr⟩ ((mem_residualIndices S J ⟨i, hr⟩).mpr hi)
    · rw [complete_recorded G S fixed a i hr]
      exact hfixed i hi hr

omit [Fintype I] [Fintype V] in

theorem image_residualIndices (S : State I V) (J : Finset I) :
    (residualIndices S J).image Subtype.val = J ∩ S.remaining := by
  ext i
  simp only [Finset.mem_image, mem_residualIndices, Finset.mem_inter]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨hj, j.property⟩
  · rintro ⟨hj, hr⟩
    exact ⟨⟨i, hr⟩, hj, rfl⟩

omit [Fintype I] [Fintype V] in

theorem card_residualIndices (S : State I V) (J : Finset I) :
    (residualIndices S J).card = (J ∩ S.remaining).card := by
  rw [← image_residualIndices S J, Finset.card_image_of_injective _ Subtype.val_injective]

omit [Fintype I] [Fintype V] in

theorem prod_residualIndices {M : Type*} [CommMonoid M]
    (S : State I V) (J : Finset I) (f : I → M) :
    (∏ i ∈ residualIndices S J, f i.1) = ∏ i ∈ J ∩ S.remaining, f i := by
  rw [← image_residualIndices S J, Finset.prod_image]
  exact fun _ _ _ _ h => Subtype.val_injective h

variable [MeasurableSpace V] [MeasurableSingletonClass V]

theorem cylinderMass_completion_eq_conditional (G : Input I V) (S : State I V)
    (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty)
    (J : Finset I) (prescribed : I → V) :
    cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed =
      (cond (Slots.law (Domain G S))
        (TailConditioning.independentTransversals (Domain G S) (graph G S))).real
        {a | ∀ i ∈ J, complete G S fixed a i = prescribed i} := by
  classical
  let E : Finset (I → V) := Finset.univ.filter (fun a => ∀ i ∈ J, a i = prescribed i)
  have hmass : cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed =
      (completionPMF G S fixed hG).toMeasure.real (E : Set (I → V)) := by
    unfold Measure.real
    rw [PMF.toMeasure_apply_finset, ENNReal.toReal_sum (fun a _ =>
      (completionPMF G S fixed hG).apply_ne_top a)]
    rfl
  rw [hmass]
  have he : (successfulAssignments G S : Set (Slots.Assignment (Domain G S))) =
      TailConditioning.independentTransversals (Domain G S) (graph G S) := by
    ext a
    exact mem_successfulAssignments G S a
  rw [← he, Slots.conditional_law_eq_uniformOfFinset _ hG]
  unfold completionPMF Measure.real
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _) (E.finite_toSet.measurableSet)]
  congr 2
  ext a
  simp [E]

theorem cylinderMass_completion_eq_ambient (G : Input I V) (S : State I V)
    (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty)
    (J : Finset I) (prescribed : I → V)
    (hfixed : ∀ i ∈ J, i ∉ S.remaining → fixed i = prescribed i) :
    cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed =
      TailConditioning.conditionalAmbientCylinder (Domain G S) (graph G S)
        (fun _ => Subtype.val) (residualIndices S J) (fun i => prescribed i.1) := by
  rw [cylinderMass_completion_eq_conditional]
  have he : {a | ∀ i ∈ J, complete G S fixed a i = prescribed i} =
      TailConditioning.ambientCylinder (Domain G S) (fun _ => Subtype.val)
        (residualIndices S J) (fun i => prescribed i.1) := by
    ext a
    exact (complete_cylinder_iff G S fixed prescribed J a).trans (and_iff_right hfixed)
  rw [he]
  simp [TailConditioning.conditionalAmbientCylinder, Measure.real,
    ProbabilityTheory.cond_apply
      (Set.toFinite (TailConditioning.independentTransversals (Domain G S) (graph G S))).measurableSet,
    ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm, Set.inter_comm]

theorem cylinderMass_completion_eq_zero_of_prefix_mismatch
    (G : Input I V) (S : State I V) (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty)
    (J : Finset I) (prescribed : I → V)
    (hbad : ¬ ∀ i ∈ J, i ∉ S.remaining → fixed i = prescribed i) :
    cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed = 0 := by
  rw [cylinderMass_completion_eq_conditional]
  have he : {a | ∀ i ∈ J, complete G S fixed a i = prescribed i} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    exact hbad ((complete_cylinder_iff G S fixed prescribed J a).mp ha).1
  rw [he, measureReal_empty]

theorem cylinderMass_completion_le_ambient (G : Input I V) (S : State I V)
    (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty)
    (J : Finset I) (prescribed : I → V) :
    cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed ≤
      TailConditioning.conditionalAmbientCylinder (Domain G S) (graph G S)
        (fun _ => Subtype.val) (residualIndices S J) (fun i => prescribed i.1) := by
  by_cases hfixed : ∀ i ∈ J, i ∉ S.remaining → fixed i = prescribed i
  · exact (cylinderMass_completion_eq_ambient G S fixed hslot hind hcross hG J prescribed hfixed).le
  · rw [cylinderMass_completion_eq_zero_of_prefix_mismatch G S fixed hslot hind hcross hG J prescribed hfixed]
    exact div_nonneg (measureReal_nonneg) (measureReal_nonneg)

theorem cylinderMass_completion_eq_zero_of_unavailable (G : Input I V) (S : State I V)
    (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty)
    (J : Finset I) (prescribed : I → V)
    (hbad : ∃ i ∈ J, i ∈ S.remaining ∧ prescribed i ∉ domain G S i) :
    cylinderMass (completionOutputLaw G S fixed hslot hind hcross hG) J prescribed = 0 := by
  have hb : TailConditioning.conditionalAmbientCylinder (Domain G S) (graph G S)
      (fun _ => Subtype.val) (residualIndices S J) (fun i => prescribed i.1) = 0 := by
    apply TailConditioning.conditionalAmbientCylinder_eq_zero_of_unavailable
    obtain ⟨i, hi, hr, hbad⟩ := hbad
    refine ⟨⟨i, hr⟩, (mem_residualIndices S J ⟨i, hr⟩).mpr hi, ?_⟩
    rintro ⟨v, hv⟩
    exact hbad (hv ▸ v.property)
  apply le_antisymm
  · exact hb ▸ cylinderMass_completion_le_ambient G S fixed hslot hind hcross hG J prescribed
  · exact Finset.sum_nonneg (fun a _ => ENNReal.toReal_nonneg)

end Balanced.Selection.Process.Tail

end

end OAI
