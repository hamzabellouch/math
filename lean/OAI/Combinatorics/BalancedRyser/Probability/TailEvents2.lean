import OAI.Combinatorics.BalancedRyser.Probability.CylinderConditioning
import OAI.Combinatorics.BalancedRyser.Probability.SlotProbability2
import OAI.Combinatorics.BalancedRyser.Probability.TailEvents
import OAI.Combinatorics.BalancedRyser.Probability.TailGraphWeights

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced.TailGraph

variable {I : Type*} {Q : I → Type*}
variable [Fintype I] [DecidableEq I]
variable [∀ i, Fintype (Q i)] [∀ i, DecidableEq (Q i)] [∀ i, Nonempty (Q i)]
variable [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Q index)]
  [∀ index, DecidableEq (Q index)] [∀ index, Nonempty (Q index)]
  [∀ index, MeasurableSpace (Q index)] [∀ index, MeasurableSingletonClass (Q index)] in
@[simp] theorem edgeEvent_mk (u v : Sigma Q) :
    edgeEvent Q s(u, v) = Slots.pairEvent Q u.1 v.1 u.2 v.2 := by
  ext ω
  simp only [edgeEvent, Slots.pairEvent, Set.mem_ofPred_eq, Sym2.mem_iff]
  constructor
  · intro h
    exact ⟨h u (Or.inl rfl), h v (Or.inr rfl)⟩
  · rintro ⟨hu, hv⟩ w (rfl | rfl)
    · exact hu
    · exact hv

omit [∀ index, Nonempty (Q index)] [∀ index, MeasurableSpace (Q index)]
  [∀ index, MeasurableSingletonClass (Q index)] in
@[simp] theorem slotSize_sigma (i : I) :
    slotSize (Sigma.fst : Sigma Q → I) i = Fintype.card (Q i) := by
  have heq : slotVertices (Sigma.fst : Sigma Q → I) i =
      Finset.univ.image (Sigma.mk i : Q i → Sigma Q) := by
    ext ⟨j, v⟩
    constructor
    · intro h
      have hji : j = i := (mem_slotVertices _ _ _).mp h
      subst j
      simp
    · intro h
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h
      apply (mem_slotVertices _ _ _).mpr
      exact (congrArg Sigma.fst ha).symm
  unfold slotSize
  rw [heq, Finset.card_image_of_injective _ (by intro a b h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)]
  exact Finset.card_univ

omit [Fintype I] [∀ index, Fintype (Q index)] [∀ index, Nonempty (Q index)]
  [∀ index, MeasurableSpace (Q index)] [∀ index, MeasurableSingletonClass (Q index)] in
theorem edgeEvent_dependsOn (e : Sym2 (Sigma Q)) :
    Slots.DependsOn Q (edgeSlots Sigma.fst e) (edgeEvent Q e) := by
  intro ω ω' heq
  constructor <;> intro h v hv
  · rw [← heq v.1 (Finset.mem_image.mpr ⟨v, by simpa using hv, rfl⟩)]
    exact h v hv
  · rw [heq v.1 (Finset.mem_image.mpr ⟨v, by simpa using hv, rfl⟩)]
    exact h v hv

theorem law_real_edgeEvent (G : SimpleGraph (Sigma Q))
    (hno : NoWithinSlotEdges G Sigma.fst) (e : Sym2 (Sigma Q)) (he : e ∈ G.edgeSet) :
    (Slots.law Q).real (edgeEvent Q e) = edgeWeight Sigma.fst e / 2 := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    rw [edgeEvent_mk, Slots.law_real_pairEvent _ _ (hno (G.mem_edgeSet.mp he)),
      edgeWeight_mk, slotSize_sigma, slotSize_sigma]
    ring

omit [Fintype I] [DecidableEq I] [∀ index, Fintype (Q index)]
  [∀ index, DecidableEq (Q index)] [∀ index, Nonempty (Q index)]
  [∀ index, MeasurableSpace (Q index)] [∀ index, MeasurableSingletonClass (Q index)] in
theorem avoid_eq_biInter {E : Type*} (B : E → Set (Slots.Assignment Q)) (T : Finset E) :
    CylinderConditioning.avoid B T = ⋂ e ∈ T, (B e)ᶜ := by
  ext ω
  simp [CylinderConditioning.avoid]

theorem edgeEvent_avoidance_independent {E : Type*} (edge : E → Sym2 (Sigma Q))
    (e : E) (T : Finset E)
    (hd : ∀ f ∈ T, Disjoint (edgeSlots Sigma.fst (edge e))
      (edgeSlots Sigma.fst (edge f))) :
    (Slots.law Q).real (edgeEvent Q (edge e) ∩
      CylinderConditioning.avoid (fun f => edgeEvent Q (edge f)) T) =
    (Slots.law Q).real (edgeEvent Q (edge e)) *
      (Slots.law Q).real (CylinderConditioning.avoid (fun f => edgeEvent Q (edge f)) T) := by
  rw [avoid_eq_biInter]
  exact Slots.law_real_inter_avoidance (edgeSlots Sigma.fst (edge e))
    (edgeEvent Q (edge e)) (edgeEvent_dependsOn _) T
    (fun f => edgeSlots Sigma.fst (edge f)) (fun f => edgeEvent Q (edge f))
    (fun f _ => edgeEvent_dependsOn _) hd

theorem cylinder_avoidance_independent {E : Type*} (edge : E → Sym2 (Sigma Q))
    (J : Finset I) (a : Slots.Assignment Q) (T : Finset E)
    (hd : ∀ f ∈ T, Disjoint J (edgeSlots Sigma.fst (edge f))) :
    (Slots.law Q).real (Slots.cylinder Q J a ∩
      CylinderConditioning.avoid (fun f => edgeEvent Q (edge f)) T) =
    (Slots.law Q).real (Slots.cylinder Q J a) *
      (Slots.law Q).real (CylinderConditioning.avoid (fun f => edgeEvent Q (edge f)) T) := by
  rw [avoid_eq_biInter]
  exact Slots.law_real_inter_avoidance J (Slots.cylinder Q J a)
    (Slots.cylinder_dependsOn J a) T (fun f => edgeSlots Sigma.fst (edge f))
    (fun f => edgeEvent Q (edge f)) (fun f _ => edgeEvent_dependsOn _) hd

end Balanced.TailGraph

end OAI
