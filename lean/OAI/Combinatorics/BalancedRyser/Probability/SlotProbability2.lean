import Mathlib.Probability.Independence.Basic
import OAI.Combinatorics.BalancedRyser.Probability.SlotProbability

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Balanced.Slots

universe u v
variable {ι : Type u} {V : ι → Type v}
variable [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
variable [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)]

instance law_isProbabilityMeasure : IsProbabilityMeasure (law V) := by
  unfold law
  infer_instance

omit [∀ i, MeasurableSingletonClass (V i)] in

theorem independent_coordinates :
    iIndepFun (fun i (ω : Assignment V) => ω i) (law V) := by
  exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)

theorem law_cylinder (J : Finset ι) (a : Assignment V) :
    law V (cylinder V J a) = ∏ i ∈ J, (Fintype.card (V i) : ℝ≥0∞)⁻¹ := by
  have hc : cylinder V J a = (J : Set ι).pi (fun i => {a i}) := by
    ext ω
    simp [cylinder, Set.mem_pi]
  rw [hc, law, Measure.pi_pi_finset]
  apply Finset.prod_congr rfl
  intro i hi
  simp [uniformOn_univ]

theorem law_real_cylinder (J : Finset ι) (a : Assignment V) :
    (law V).real (cylinder V J a) = ∏ i ∈ J, (Fintype.card (V i) : ℝ)⁻¹ := by
  simp [Measure.real, law_cylinder, ENNReal.toReal_prod]

theorem law_real_cylinder_pos (J : Finset ι) (a : Assignment V) :
    0 < (law V).real (cylinder V J a) := by
  rw [law_real_cylinder]
  apply Finset.prod_pos
  intro i hi
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

omit [∀ i, MeasurableSingletonClass (V i)] in

theorem independent_restrictions (S T : Finset ι) (hST : Disjoint S T) :
    IndepFun (fun (ω : Assignment V) (i : S) => ω i)
      (fun (ω : Assignment V) (i : T) => ω i) (law V) := by
  exact independent_coordinates.indepFun_finset S T hST (fun i => measurable_pi_apply i)

omit [∀ i, MeasurableSpace (V i)] [Fintype ι] [∀ i, Fintype (V i)] [∀ i, MeasurableSingletonClass (V i)] in

theorem dependsOn_representation (S : Finset ι) (A : Set (Assignment V))
    (hA : DependsOn V S A) :
    ∃ B : Set ((i : S) → V i),
      A = (fun (ω : Assignment V) (i : S) => ω i) ⁻¹' B := by
  classical
  let base : Assignment V := fun i => Classical.choice (inferInstance : Nonempty (V i))
  let extend : ((i : S) → V i) → Assignment V :=
    fun f i => if h : i ∈ S then f ⟨i, h⟩ else base i
  refine ⟨{f | extend f ∈ A}, ?_⟩
  ext ω
  apply hA ω (extend (fun i : S => ω i))
  intro i hi
  simp [extend, hi]

theorem independent_events_of_disjoint (S T : Finset ι) (hST : Disjoint S T)
    (A B : Set (Assignment V)) (hA : DependsOn V S A) (hB : DependsOn V T B) :
    IndepSet A B (law V) := by
  classical
  obtain ⟨A', rfl⟩ := dependsOn_representation S A hA
  obtain ⟨B', rfl⟩ := dependsOn_representation T B hB
  have hS : Measurable (fun (ω : Assignment V) (i : S) => ω i) :=
    Measurable.of_eval (fun index => measurable_pi_apply (index : ι))
  have hT : Measurable (fun (ω : Assignment V) (i : T) => ω i) :=
    Measurable.of_eval (fun index => measurable_pi_apply (index : ι))
  exact (indepFun_iff_indepSet_preimage hS hT).mp
    (independent_restrictions S T hST) A' B'
    (Set.toFinite A').measurableSet (Set.toFinite B').measurableSet

theorem law_real_inter_of_disjoint (S T : Finset ι) (hST : Disjoint S T)
    (A B : Set (Assignment V)) (hA : DependsOn V S A) (hB : DependsOn V T B) :
    (law V).real (A ∩ B) = (law V).real A * (law V).real B := by
  have h := (independent_events_of_disjoint S T hST A B hA hB).measure_inter_eq_mul
  simpa [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal h

omit [∀ i, MeasurableSpace (V i)] [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
  [∀ i, MeasurableSingletonClass (V i)] in

theorem cylinder_dependsOn (J : Finset ι) (a : Assignment V) :
    DependsOn V J (cylinder V J a) := by
  intro ω ω' h
  constructor <;> intro hc i hi
  · rw [← h i hi]
    exact hc i hi
  · rw [h i hi]
    exact hc i hi

omit [∀ i, MeasurableSpace (V i)] [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
  [∀ i, MeasurableSingletonClass (V i)] in

theorem DependsOn.compl {J : Finset ι} {A : Set (Assignment V)}
    (h : DependsOn V J A) : DependsOn V J Aᶜ := by
  intro ω ω' heq
  exact not_congr (h ω ω' heq)

omit [∀ i, MeasurableSpace (V i)] [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
  [∀ i, MeasurableSingletonClass (V i)] in

theorem dependsOn_biInter [DecidableEq ι] {κ : Type*} (E : Finset κ)
    (support : κ → Finset ι) (A : κ → Set (Assignment V))
    (hA : ∀ e ∈ E, DependsOn V (support e) (A e)) :
    DependsOn V (E.biUnion support) (⋂ e ∈ E, A e) := by
  classical
  intro ω ω' heq
  simp only [Set.mem_iInter]
  constructor <;> intro h e he
  · exact (hA e he ω ω' (fun i hi => heq i (Finset.mem_biUnion.mpr ⟨e, he, hi⟩))).mp (h e he)
  · exact (hA e he ω ω' (fun i hi => heq i (Finset.mem_biUnion.mpr ⟨e, he, hi⟩))).mpr (h e he)

omit [∀ i, MeasurableSpace (V i)] [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
  [∀ i, MeasurableSingletonClass (V i)] in

theorem pairEvent_dependsOn [DecidableEq ι] (i j : ι) (a : V i) (b : V j) :
    DependsOn V {i, j} (pairEvent V i j a b) := by
  intro ω ω' heq
  simp only [pairEvent, Set.mem_ofPred_eq]
  rw [heq i (by simp), heq j (by simp)]

omit [∀ i, Nonempty (V i)] in

theorem law_eq_uniformOn : law V = uniformOn (Set.univ : Set (Assignment V)) := by
  classical
  apply Measure.ext_of_singleton
  intro a
  simp only [law, Measure.pi_singleton, uniformOn_univ, Measure.count_singleton,
    one_div, Assignment, Fintype.card_pi, Nat.cast_prod]
  symm
  apply ENNReal.prod_inv_distrib
  intro i hi j hj hij
  exact Or.inr (ENNReal.natCast_ne_top _)

theorem law_coordinate (i : ι) (a : V i) :
    law V {ω | ω i = a} = (Fintype.card (V i) : ℝ≥0∞)⁻¹ := by
  have hm := (measurePreserving_eval
    (fun j => uniformOn (Set.univ : Set (V j))) i).map_eq
  have h := congrArg (fun μ => μ {a}) hm
  simpa [Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton a),
    uniformOn_univ, law, Set.preimage, Set.mem_singleton_iff] using h

theorem law_pairEvent (i j : ι) (hij : i ≠ j) (a : V i) (b : V j) :
    law V (pairEvent V i j a b) =
      (Fintype.card (V i) : ℝ≥0∞)⁻¹ * (Fintype.card (V j) : ℝ≥0∞)⁻¹ := by
  have h := (independent_coordinates (V := V)).indepFun hij
  have heq := h.measure_inter_preimage_eq_mul {a} {b}
    (measurableSet_singleton a) (measurableSet_singleton b)
  change law V (pairEvent V i j a b) =
    law V {ω | ω i = a} * law V {ω | ω j = b} at heq
  rw [heq, law_coordinate, law_coordinate]

theorem law_real_pairEvent (i j : ι) (hij : i ≠ j) (a : V i) (b : V j) :
    (law V).real (pairEvent V i j a b) =
      (Fintype.card (V i) : ℝ)⁻¹ * (Fintype.card (V j) : ℝ)⁻¹ := by
  simp [Measure.real, law_pairEvent i j hij a b, ENNReal.toReal_mul]

theorem law_real_inter_avoidance [DecidableEq ι] {κ : Type*}
    (J : Finset ι) (A : Set (Assignment V)) (hA : DependsOn V J A)
    (E : Finset κ) (support : κ → Finset ι) (bad : κ → Set (Assignment V))
    (hbad : ∀ e ∈ E, DependsOn V (support e) (bad e))
    (hdisjoint : ∀ e ∈ E, Disjoint J (support e)) :
    (law V).real (A ∩ ⋂ e ∈ E, (bad e)ᶜ) =
      (law V).real A * (law V).real (⋂ e ∈ E, (bad e)ᶜ) := by
  classical
  apply law_real_inter_of_disjoint J (E.biUnion support) _ A _ hA
  · exact dependsOn_biInter E support (fun e => (bad e)ᶜ)
      (fun e he => (hbad e he).compl)
  · apply Finset.disjoint_left.mpr
    intro i hiJ hiUnion
    obtain ⟨e, he, hi⟩ := Finset.mem_biUnion.mp hiUnion
    exact Finset.disjoint_left.mp (hdisjoint e he) hiJ hi

omit [∀ i, Nonempty (V i)] in

theorem law_real_finset [DecidableEq ι] (A : Finset (Assignment V)) :
    (law V).real (A : Set (Assignment V)) =
      ∑ _ω ∈ A, (Fintype.card (Assignment V) : ℝ)⁻¹ := by
  classical
  rw [law_eq_uniformOn]
  simp [Measure.real, uniformOn_univ, Measure.count_apply_finset,
    div_eq_mul_inv]

end Balanced.Slots

end

end OAI
