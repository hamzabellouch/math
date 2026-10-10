import OAI.Combinatorics.BalancedRyser.Local.MeasureLocalLemma
import OAI.Combinatorics.BalancedRyser.Probability.SlotEdges
import OAI.Combinatorics.BalancedRyser.Probability.SlotProbability2

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Balanced.Slots

universe u v w
variable {ι : Type u} {V : ι → Type v}

@[simp] theorem edgeEvent_mk (a b : Sigma V) :
    edgeEvent V s(a, b) = pairEvent V a.1 b.1 a.2 b.2 := by
  ext ω
  simp [edgeEvent, pairEvent]

@[simp] theorem edgeSupport_mk [DecidableEq ι] (a b : Sigma V) :
    edgeSupport V s(a, b) = {a.1, b.1} := by
  classical
  ext i
  simp [edgeSupport, Sym2.mem_toFinset, eq_comm]

@[simp] theorem edgeSlotsDistinct_mk (a b : Sigma V) :
    edgeSlotsDistinct V s(a, b) ↔ a.1 ≠ b.1 := Iff.rfl

@[simp] theorem edgeMass_mk [∀ i, Fintype (V i)] (a b : Sigma V) :
    edgeMass V s(a, b) =
      (Fintype.card (V a.1) : ℝ)⁻¹ * (Fintype.card (V b.1) : ℝ)⁻¹ := rfl

theorem edgeEvent_dependsOn (e : Sym2 (Sigma V)) :
    DependsOn V (edgeSupport V e) (edgeEvent V e) := by
  classical
  induction e using Sym2.inductionOn with
  | _ a b =>
    simpa using pairEvent_dependsOn (V := V) a.1 b.1 a.2 b.2

variable [Fintype ι] [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
variable [∀ i, MeasurableSpace (V i)] [∀ i, MeasurableSingletonClass (V i)]

theorem law_real_edgeEvent (e : Sym2 (Sigma V)) (h : edgeSlotsDistinct V e) :
    (law V).real (edgeEvent V e) = edgeMass V e := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    simpa using law_real_pairEvent a.1 b.1 h a.2 b.2

variable {κ : Type w} [Fintype κ] [DecidableEq κ]

omit [Fintype ι] in
@[simp] theorem mem_supportNeighbors (support : κ → Finset ι) (e f : κ) :
    f ∈ supportNeighbors support e ↔ f ≠ e ∧ ¬ Disjoint (support e) (support f) := by
  classical
  simp [supportNeighbors]

omit [Fintype ι] [DecidableEq κ] in
@[simp] theorem mem_touching (support : κ → Finset ι) (J : Finset ι) (e : κ) :
    e ∈ touching support J ↔ ¬ Disjoint J (support e) := by
  classical
  simp [touching]

theorem support_neighbor_independence [DecidableEq ι]
    (support : κ → Finset ι) (events : κ → Set (Assignment V))
    (hdep : ∀ e, DependsOn V (support e) (events e))
    (e : κ) (T : Finset κ) (he : e ∉ T)
    (hT : Disjoint T (supportNeighbors support e)) :
    (law V).real (events e ∩ CylinderConditioning.avoid events T) =
      (law V).real (events e) * (law V).real (CylinderConditioning.avoid events T) := by
  have ha : CylinderConditioning.avoid events T = ⋂ f ∈ T, (events f)ᶜ := by
    ext ω
    simp [CylinderConditioning.avoid]
  rw [ha]
  apply law_real_inter_avoidance (support e) (events e) (hdep e) T support events
    (fun f _ => hdep f)
  intro f hf
  by_contra hdis
  have hfe : f ≠ e := by intro h; exact he (h ▸ hf)
  exact Finset.disjoint_left.mp hT hf (mem_supportNeighbors support e f |>.mpr ⟨hfe, hdis⟩)

theorem cylinder_avoidance_independence [DecidableEq ι]
    (support : κ → Finset ι) (events : κ → Set (Assignment V))
    (hdep : ∀ e, DependsOn V (support e) (events e))
    (J : Finset ι) (a : Assignment V) :
    (law V).real (cylinder V J a ∩
      CylinderConditioning.avoid events (Finset.univ \ touching support J)) =
    (law V).real (cylinder V J a) *
      (law V).real (CylinderConditioning.avoid events (Finset.univ \ touching support J)) := by
  have ha : CylinderConditioning.avoid events (Finset.univ \ touching support J) =
      ⋂ f ∈ Finset.univ \ touching support J, (events f)ᶜ := by
    ext ω
    simp [CylinderConditioning.avoid]
  rw [ha]
  apply law_real_inter_avoidance J _ (cylinder_dependsOn J a) _ support events
    (fun f _ => hdep f)
  intro f hf
  have hn := (Finset.mem_sdiff.mp hf).2
  simpa using hn

theorem local_lemma_of_supports [DecidableEq ι]
    (support : κ → Finset ι) (events : κ → Set (Assignment V))
    (hdep : ∀ e, DependsOn V (support e) (events e)) (x : κ → ℝ)
    (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e < 1)
    (hp : ∀ e, (law V).real (events e) ≤
      x e * ∏ f ∈ supportNeighbors support e, (1 - x f)) :
    ∀ S, 0 < (law V).real (CylinderConditioning.avoid events S) ∧
      ∀ e, e ∉ S →
      (law V).real (CylinderConditioning.avoid events S ∩ events e) ≤
        x e * (law V).real (CylinderConditioning.avoid events S) := by
  classical
  exact CylinderConditioning.local_lemma (law V) events
    (fun e => (Set.toFinite (events e)).measurableSet)
    (supportNeighbors support) x hx0 hx1 hp
    (support_neighbor_independence support events hdep)

theorem local_lemma_cylinder_of_supports [DecidableEq ι]
    (support : κ → Finset ι) (events : κ → Set (Assignment V))
    (hdep : ∀ e, DependsOn V (support e) (events e)) (x : κ → ℝ)
    (hx0 : ∀ e, 0 ≤ x e) (hx1 : ∀ e, x e < 1)
    (hp : ∀ e, (law V).real (events e) ≤
      x e * ∏ f ∈ supportNeighbors support e, (1 - x f))
    (J : Finset ι) (a : Assignment V) :
    0 < (law V).real (CylinderConditioning.avoid events Finset.univ) ∧
      (law V).real (cylinder V J a ∩ CylinderConditioning.avoid events Finset.univ) /
        (law V).real (CylinderConditioning.avoid events Finset.univ) ≤
      (∏ i ∈ J, (Fintype.card (V i) : ℝ)⁻¹) *
        ∏ e ∈ touching support J, (1 - x e)⁻¹ := by
  classical
  have h := CylinderConditioning.local_lemma_cylinder (law V) events
    (fun e => (Set.toFinite (events e)).measurableSet)
    (supportNeighbors support) x hx0 hx1 hp
    (support_neighbor_independence support events hdep)
    (cylinder V J a) (Finset.univ \ touching support J) (touching support J)
    (by simp [Finset.disjoint_left])
    (cylinder_avoidance_independence support events hdep J a)
  have hu : (Finset.univ \ touching support J) ∪ touching support J = Finset.univ := by
    ext e
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  rw [hu, law_real_cylinder] at h
  exact h

omit [∀ i, Nonempty (V i)] in

theorem conditional_law_real (G C : Set (Assignment V)) :
    (ProbabilityTheory.cond (law V) G).real C =
      (law V).real (C ∩ G) / (law V).real G := by
  classical
  simp [Measure.real, ProbabilityTheory.cond_apply (Set.toFinite G).measurableSet,
    ENNReal.toReal_mul, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm, Set.inter_comm]

omit [∀ i, Nonempty (V i)] in

theorem conditional_law_zero_of_disjoint (G C : Set (Assignment V))
    (h : Disjoint C G) : (ProbabilityTheory.cond (law V) G).real C = 0 := by
  rw [conditional_law_real, Set.disjoint_iff_inter_eq_empty.mp h]
  simp

end Balanced.Slots

end

end OAI
