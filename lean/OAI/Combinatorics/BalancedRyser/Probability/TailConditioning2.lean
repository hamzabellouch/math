import Mathlib.Probability.ConditionalProbability
import OAI.Combinatorics.BalancedRyser.Local.HalfWeightLocalLemma
import OAI.Combinatorics.BalancedRyser.Local.MeasureLocalLemma
import OAI.Combinatorics.BalancedRyser.Probability.SlotProbability2
import OAI.Combinatorics.BalancedRyser.Probability.TailConditioning
import OAI.Combinatorics.BalancedRyser.Probability.TailEvents2
import OAI.Combinatorics.BalancedRyser.Probability.TailGraphWeights

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Balanced
open scoped _root_.Balanced
namespace TailConditioning

universe u v
variable {I : Type u} {Q : I → Type v}

theorem minSlotSize_le [Fintype I] [∀ i, Fintype (Q i)] (i : I) :
    minSlotSize Q ≤ Fintype.card (Q i) := by
  classical
  apply WithTop.untopD_le
  exact Finset.min_le (Finset.mem_image_of_mem (fun i => Fintype.card (Q i))
    (Finset.mem_univ i))

theorem slotSize_sigma [Fintype I] [DecidableEq I] [∀ i, Fintype (Q i)]
    [∀ i, DecidableEq (Q i)] (i : I) :
    TailGraph.slotSize (Sigma.fst : Sigma Q → I) i = Fintype.card (Q i) := by
  let e : {v : Sigma Q // v.1 = i} ≃ Q i :=
    { toFun := fun v => v.2 ▸ v.1.2
      invFun := fun a => ⟨⟨i, a⟩, rfl⟩
      left_inv := by
        rintro ⟨⟨j, a⟩, h⟩
        dsimp at h
        subst j
        rfl
      right_inv := by intro a; rfl }
  simpa [TailGraph.slotSize, TailGraph.slotVertices, Fintype.card_subtype] using Fintype.card_congr e

theorem eight_mul_degree_le_min [Fintype I] [∀ i, Fintype (Q i)]
    (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (hmin : 3 ≤ minSlotSize Q)
    (hsparse : (G.maxDegree : ℝ) / minSlotSize Q ≤ 1 / 8) :
    8 * G.maxDegree ≤ minSlotSize Q := by
  have hpos : (0 : ℝ) < minSlotSize Q := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < 3) hmin
  have h := (div_le_iff₀ hpos).mp hsparse
  have he : (8 : ℝ) * G.maxDegree ≤ minSlotSize Q := by linarith
  exact_mod_cast he

theorem conditionalCylinder_eq_zero [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)]
    (G : SimpleGraph (Sigma Q)) (J : Finset I) (a : Slots.Assignment Q)
    (himpossible : Disjoint (Slots.cylinder Q J a) (independentTransversals Q G)) :
    conditionalCylinder Q G J a = 0 := by
  simp [conditionalCylinder, Set.disjoint_iff_inter_eq_empty.mp himpossible]

section Graph

variable [Fintype I] [DecidableEq I] [∀ i, Fintype (Q i)]
variable [∀ i, DecidableEq (Q i)] [∀ i, Nonempty (Q i)]
variable [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]

omit [DecidableEq I] [∀ i, DecidableEq (Q i)] [∀ i, Nonempty (Q i)]
    [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)] in
theorem independentTransversals_eq_avoid (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj] :
    independentTransversals Q G =
      CylinderConditioning.avoid (fun e : G.edgeSet => TailGraph.edgeEvent Q e.val) Finset.univ := by
  ext ω
  constructor
  · intro hω e he hbad
    obtain ⟨e, heG⟩ := e
    induction e using Sym2.inductionOn with
    | _ u v =>
      have hu : ω u.1 = u.2 := hbad u (Sym2.mem_mk_left _ _)
      have hv : ω v.1 = v.2 := hbad v (Sym2.mem_mk_right _ _)
      have ha := G.mem_edgeSet.mp heG
      have hn := hω u.1 v.1
      apply hn
      simpa only [hu, hv, Sigma.eta] using ha
  · intro hω i j hij
    let e : G.edgeSet := ⟨s(⟨i, ω i⟩, ⟨j, ω j⟩), G.mem_edgeSet.mpr hij⟩
    apply hω e (Finset.mem_univ e)
    intro v hv
    change v ∈ s(⟨i, ω i⟩, ⟨j, ω j⟩) at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl <;> rfl

theorem graph_nonneighbor_independence (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (e : G.edgeSet) (T : Finset G.edgeSet) (heT : e ∉ T)
    (hTN : Disjoint T (TailGraph.liftEdges G (TailGraph.dependencyEdges G Sigma.fst e.val))) :
    (Slots.law Q).real (TailGraph.edgeEvent Q e.val ∩
      CylinderConditioning.avoid (fun f : G.edgeSet => TailGraph.edgeEvent Q f.val) T) =
      (Slots.law Q).real (TailGraph.edgeEvent Q e.val) *
        (Slots.law Q).real
          (CylinderConditioning.avoid (fun f : G.edgeSet => TailGraph.edgeEvent Q f.val) T) := by
  apply TailGraph.edgeEvent_avoidance_independent (fun f : G.edgeSet => f.val) e T
  intro f hf
  by_contra hdisj
  have hfe : f.val ≠ e.val := by
    intro heq
    have hfe' : f = e := Subtype.ext heq
    exact heT (hfe' ▸ hf)
  have hfN : f ∈ TailGraph.liftEdges G (TailGraph.dependencyEdges G Sigma.fst e.val) := by
    rw [TailGraph.mem_liftEdges, TailGraph.mem_dependencyEdges_iff]
    exact ⟨G.mem_edgeFinset.mpr f.property, hfe, hdisj⟩
  exact Finset.disjoint_left.mp hTN hf hfN

theorem graph_cylinder_independence (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (J : Finset I) (a : Slots.Assignment Q) :
    (Slots.law Q).real (Slots.cylinder Q J a ∩
      CylinderConditioning.avoid (fun f : G.edgeSet => TailGraph.edgeEvent Q f.val)
        (Finset.univ \ TailGraph.liftEdges G (TailGraph.touchingEdges G Sigma.fst J))) =
    (Slots.law Q).real (Slots.cylinder Q J a) *
      (Slots.law Q).real (CylinderConditioning.avoid
        (fun f : G.edgeSet => TailGraph.edgeEvent Q f.val)
        (Finset.univ \ TailGraph.liftEdges G (TailGraph.touchingEdges G Sigma.fst J))) := by
  apply TailGraph.cylinder_avoidance_independent (fun f : G.edgeSet => f.val) J a
  intro f hf
  have hfnot := (Finset.mem_sdiff.mp hf).2
  apply Finset.disjoint_left.mpr
  intro i hiJ hie
  apply hfnot
  rw [TailGraph.mem_liftEdges]
  exact Finset.mem_filter.mpr ⟨G.mem_edgeFinset.mpr f.property, ⟨i, hiJ, hie⟩⟩

theorem tail_conditioning_of_bounds (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (hno : TailGraph.NoWithinSlotEdges G Sigma.fst)
    (L Δ : ℕ) (hL : 3 ≤ L) (hsize : ∀ i, L ≤ Fintype.card (Q i))
    (hdegree : ∀ u, G.degree u ≤ Δ) (hsparse : 8 * Δ ≤ L) :
    0 < (Slots.law Q).real (independentTransversals Q G) ∧
      ∀ (J : Finset I) (a : Slots.Assignment Q),
        conditionalCylinder Q G J a ≤
          Real.exp ((J.card : ℝ) / 2) * ∏ i ∈ J, (Fintype.card (Q i) : ℝ)⁻¹ := by
  classical
  let B : G.edgeSet → Set (Slots.Assignment Q) := fun e => TailGraph.edgeEvent Q e.val
  let N : G.edgeSet → Finset G.edgeSet :=
    fun e => TailGraph.liftEdges G (TailGraph.dependencyEdges G Sigma.fst e.val)
  let x : G.edgeSet → ℝ := fun e => TailGraph.edgeWeight Sigma.fst e.val
  have hslot : ∀ i, L ≤ TailGraph.slotSize (Sigma.fst : Sigma Q → I) i := by
    intro i
    rw [slotSize_sigma]
    exact hsize i
  have hx0 : ∀ e, 0 ≤ x e := fun e => TailGraph.edgeWeight_nonneg Sigma.fst e.val
  have hxhalf : ∀ e, x e ≤ 1 / 2 := fun e =>
    TailGraph.edgeWeight_le_half Sigma.fst (fun i => hL.trans (hslot i)) e.val
  have hB : ∀ e, MeasurableSet (B e) := fun e => (Set.toFinite (B e)).measurableSet
  have hp : ∀ e, (Slots.law Q).real (B e) ≤ x e / 2 := by
    intro e
    exact (TailGraph.law_real_edgeEvent G hno e.val e.property).le
  have hweight : ∀ e, ∑ f ∈ N e, x f ≤ 1 / 2 := by
    intro e
    dsimp [N, x]
    rw [TailGraph.sum_liftEdges G _ (TailGraph.dependencyEdges_subset G Sigma.fst e.val)]
    exact TailGraph.dependency_weight_le_half G Sigma.fst L Δ (by omega)
      hslot hdegree hsparse e.val
  have hind : ∀ e T, e ∉ T → Disjoint T (N e) →
      (Slots.law Q).real (B e ∩ CylinderConditioning.avoid B T) =
        (Slots.law Q).real (B e) * (Slots.law Q).real (CylinderConditioning.avoid B T) := by
    intro e T heT hTN
    exact graph_nonneighbor_independence G e T heT hTN
  have hlocal := CylinderConditioning.local_lemma_of_half_weight
    (Slots.law Q) B hB N x hx0 hxhalf hp hweight hind
  constructor
  · rw [independentTransversals_eq_avoid]
    exact (hlocal Finset.univ).1
  · intro J a
    let U := TailGraph.liftEdges G (TailGraph.touchingEdges G Sigma.fst J)
    let T : Finset G.edgeSet := Finset.univ \ U
    have hTU : T ∪ U = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ U)
    have hd : Disjoint T U := by
      exact Finset.disjoint_left.mpr (fun e heT heU => (Finset.mem_sdiff.mp heT).2 heU)
    have hC : (Slots.law Q).real (Slots.cylinder Q J a ∩ CylinderConditioning.avoid B T) =
        (Slots.law Q).real (Slots.cylinder Q J a) *
          (Slots.law Q).real (CylinderConditioning.avoid B T) :=
      graph_cylinder_independence G J a
    have hsum : ∑ e ∈ U, x e ≤ (J.card : ℝ) / 4 := by
      dsimp [U, x]
      rw [TailGraph.sum_liftEdges G _ (TailGraph.touchingEdges_subset G Sigma.fst J)]
      exact TailGraph.touching_weight_le_quarter G Sigma.fst L Δ (by omega)
        hslot hdegree hsparse J
    have hc := (CylinderConditioning.local_lemma_cylinder_exp (Slots.law Q)
      B hB N x hx0 hxhalf hp hweight hind (Slots.cylinder Q J a) T U hd hC
      (J.card : ℝ) hsum).2
    rw [hTU] at hc
    change (Slots.law Q).real (Slots.cylinder Q J a ∩
      CylinderConditioning.avoid (fun e : G.edgeSet => TailGraph.edgeEvent Q e.val) Finset.univ) /
      (Slots.law Q).real (CylinderConditioning.avoid
        (fun e : G.edgeSet => TailGraph.edgeEvent Q e.val) Finset.univ) ≤ _ at hc
    rw [← independentTransversals_eq_avoid G, Slots.law_real_cylinder] at hc
    exact hc

end Graph

theorem tail_conditioning [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]
    (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (hno : TailGraph.NoWithinSlotEdges G Sigma.fst)
    (hmin : 3 ≤ minSlotSize Q)
    (hsparse : (G.maxDegree : ℝ) / minSlotSize Q ≤ 1 / 8) :
    0 < (Slots.law Q).real (independentTransversals Q G) ∧
      ∀ (J : Finset I) (a : Slots.Assignment Q),
        conditionalCylinder Q G J a ≤
          Real.exp ((J.card : ℝ) / 2) * ∏ i ∈ J, (Fintype.card (Q i) : ℝ)⁻¹ := by
  classical
  let : ∀ i, Nonempty (Q i) := fun i => Fintype.card_pos_iff.mp
    (lt_of_lt_of_le (show 0 < 3 by decide) (hmin.trans (minSlotSize_le i)))
  exact tail_conditioning_of_bounds G hno (minSlotSize Q) G.maxDegree hmin
    (fun i => minSlotSize_le i) G.degree_le_maxDegree
    (eight_mul_degree_le_min G hmin hsparse)

theorem tail_conditioning_of_pointwise_bounds
    [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]
    (G : SimpleGraph (Sigma Q)) [DecidableRel G.Adj]
    (hno : TailGraph.NoWithinSlotEdges G Sigma.fst)
    (hsize : ∀ i, 3 ≤ Fintype.card (Q i))
    (hdegree : ∀ v i, 8 * G.degree v ≤ Fintype.card (Q i)) :
    0 < (Slots.law Q).real (independentTransversals Q G) ∧
      ∀ (J : Finset I) (a : Slots.Assignment Q),
        conditionalCylinder Q G J a ≤
          Real.exp ((J.card : ℝ) / 2) * ∏ i ∈ J, (Fintype.card (Q i) : ℝ)⁻¹ := by
  classical
  let : ∀ i, Nonempty (Q i) := fun i => Fintype.card_pos_iff.mp
    (lt_of_lt_of_le (show 0 < 3 by decide) (hsize i))
  cases isEmpty_or_nonempty I with
  | inl hI =>
    let := hI
    exact tail_conditioning_of_bounds G hno 3 0 (by decide)
      (fun i => isEmptyElim i) (fun v => isEmptyElim v.1) (by decide)
  | inr hI =>
    let := hI
    obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
      (fun i => Fintype.card (Q i)) Finset.univ_nonempty
    refine tail_conditioning_of_bounds G hno (Fintype.card (Q i))
      (Fintype.card (Q i) / 8) (hsize i)
      (fun j => hi j (Finset.mem_univ j)) ?_ (Nat.mul_div_le _ _)
    intro v
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr
    simpa only [Nat.mul_comm] using hdegree v i

theorem conditionalCylinder_eq_cond_real [Fintype I] [∀ i, Fintype (Q i)]
    [∀ i, MeasurableSpace (Q i)] [∀ i, MeasurableSingletonClass (Q i)]
    (G : SimpleGraph (Sigma Q)) (J : Finset I) (a : Slots.Assignment Q) :
    conditionalCylinder Q G J a =
      (ProbabilityTheory.cond (Slots.law Q) (independentTransversals Q G)).real
        (Slots.cylinder Q J a) := by
  unfold conditionalCylinder Measure.real
  rw [ProbabilityTheory.cond_apply (Set.toFinite (independentTransversals Q G)).measurableSet]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [Set.inter_comm, div_eq_mul_inv, mul_comm]

theorem conditionalCylinder_eq_zero_of_no_realization
    [Fintype I] [∀ i, Fintype (Q i)] [∀ i, MeasurableSpace (Q i)]
    (G : SimpleGraph (Sigma Q)) (J : Finset I) (a : Slots.Assignment Q)
    (h : ¬ ∃ ω, ω ∈ independentTransversals Q G ∧ ∀ i ∈ J, ω i = a i) :
    conditionalCylinder Q G J a = 0 := by
  apply conditionalCylinder_eq_zero G J a
  apply Set.disjoint_left.mpr
  intro ω hc hg
  exact h ⟨ω, hg, hc⟩

end TailConditioning
end Balanced

end OAI
