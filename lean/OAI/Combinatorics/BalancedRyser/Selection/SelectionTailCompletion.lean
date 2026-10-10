import OAI.Combinatorics.BalancedRyser.Probability.SlotConditionedLaw
import OAI.Combinatorics.BalancedRyser.Probability.TailConditioning2
import OAI.Combinatorics.BalancedRyser.Selection.SelectionLaw
import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcess

namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

namespace Balanced.Selection.Process.Tail

variable {I V : Type*} [Fintype I] [Fintype V]

abbrev Slot (S : State I V) := {i : I // i ∈ S.remaining}

abbrev Domain (G : Input I V) (S : State I V) (i : Slot S) :=
  {v : V // v ∈ domain G S i.1}

def value (G : Input I V) (S : State I V) (v : Sigma (Domain G S)) : V := v.2.1

def graph (G : Input I V) (S : State I V) : SimpleGraph (Sigma (Domain G S)) :=
  G.graph.comap (value G S)

omit [Fintype I] [Fintype V] in
@[simp] theorem value_slot (G : Input I V) (S : State I V)
    (v : Sigma (Domain G S)) : G.slot (value G S v) = v.1.1 :=
  (Finset.mem_filter.mp v.2.2).2

omit [Fintype I] [Fintype V] in
theorem value_injective (G : Input I V) (S : State I V) :
    Function.Injective (value G S) := by
  rintro ⟨⟨i, hi⟩, ⟨v, hv⟩⟩ ⟨⟨j, hj⟩, ⟨w, hw⟩⟩ heq
  change v = w at heq
  subst w
  have hij : i = j := (Finset.mem_filter.mp hv).2.symm.trans
    (Finset.mem_filter.mp hw).2
  subst j
  rfl

omit [Fintype I] [Fintype V] in
theorem value_mem_current (G : Input I V) (S : State I V)
    (v : Sigma (Domain G S)) : value G S v ∈ currentVertices G S := by
  apply Finset.mem_filter.mpr
  exact ⟨(Finset.mem_filter.mp v.2.2).1, by rw [value_slot]; exact v.1.2⟩

omit [Fintype I] [Fintype V] in
@[simp] theorem card_domain (G : Input I V) (S : State I V) (i : Slot S) :
    Fintype.card (Domain G S i) = (domain G S i.1).card := by
  simp [Domain]

omit [Fintype I] [Fintype V] in

theorem noWithinSlotEdges (G : Input I V) (S : State I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w) :
    TailGraph.NoWithinSlotEdges (graph G S) Sigma.fst := by
  intro v w hadj hslot
  apply hno (value G S v) (value G S w)
  · rw [value_slot, value_slot, hslot]
  · exact hadj

omit [Fintype I] in

theorem degree_le (G : Input I V) (S : State I V)
    (v : Sigma (Domain G S)) :
    (graph G S).degree v ≤ degree G S (value G S v) := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  unfold degree
  apply Finset.card_le_card_of_injOn (value G S)
  · intro w hw
    apply Finset.mem_inter.mpr
    refine ⟨?_, value_mem_current G S w⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (SimpleGraph.mem_neighborFinset (graph G S) v w).mp hw⟩
  · exact (value_injective G S).injOn

omit [Fintype I] in

theorem tail_conditioning [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : Input I V) (S : State I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (L Δ : ℕ) (hL : 3 ≤ L)
    (hsize : ∀ i ∈ S.remaining, L ≤ (domain G S i).card)
    (hdegree : ∀ v ∈ currentVertices G S, degree G S v ≤ Δ)
    (hsparse : 8 * Δ ≤ L) :
    0 < (Slots.law (Domain G S)).real
      (TailConditioning.independentTransversals (Domain G S) (graph G S)) ∧
    ∀ (J : Finset (Slot S)) (a : Slots.Assignment (Domain G S)),
      TailConditioning.conditionalCylinder (Domain G S) (graph G S) J a ≤
        Real.exp ((J.card : ℝ) / 2) *
          ∏ i ∈ J, ((domain G S i.1).card : ℝ)⁻¹ := by
  classical
  let : ∀ i : Slot S, Nonempty (Domain G S i) := fun i =>
    Fintype.card_pos_iff.mp (by rw [card_domain]; exact lt_of_lt_of_le (by omega) (hsize i.1 i.2))
  simpa only [card_domain] using
    TailConditioning.tail_conditioning_of_bounds (graph G S) (noWithinSlotEdges G S hno)
      L Δ hL (fun i => by simpa only [card_domain] using hsize i.1 i.2)
      (fun v => (degree_le G S v).trans (hdegree _ (value_mem_current G S v))) hsparse

def complete (G : Input I V) (S : State I V) (fixed : I → V)
    (a : Slots.Assignment (Domain G S)) : I → V :=
  fun i => if hi : i ∈ S.remaining then (a ⟨i, hi⟩).1 else fixed i

omit [Fintype I] [Fintype V] in
@[simp] theorem complete_remaining (G : Input I V) (S : State I V) (fixed : I → V)
    (a : Slots.Assignment (Domain G S)) (i : Slot S) :
    complete G S fixed a i.1 = (a i).1 := by simp [complete, i.2]

omit [Fintype I] [Fintype V] in
@[simp] theorem complete_recorded (G : Input I V) (S : State I V) (fixed : I → V)
    (a : Slots.Assignment (Domain G S)) (i : I) (hi : i ∉ S.remaining) :
    complete G S fixed a i = fixed i := by simp [complete, hi]

omit [Fintype I] [Fintype V] in

theorem complete_agrees_recorded (G : Input I V) (S : State I V) (fixed : I → V)
    (hprefix : ∀ i ∉ S.remaining, S.recorded i = some (fixed i))
    (a : Slots.Assignment (Domain G S)) (i : I) (hi : i ∉ S.remaining) :
    S.recorded i = some (complete G S fixed a i) := by
  rw [complete_recorded G S fixed a i hi]
  exact hprefix i hi

omit [Fintype I] [Fintype V] in

theorem complete_isIndependentTransversal (G : Input I V) (S : State I V)
    (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (a : Slots.Assignment (Domain G S))
    (ha : a ∈ TailConditioning.independentTransversals (Domain G S) (graph G S)) :
    IsIndependentTransversal G (complete G S fixed a) := by
  constructor
  · intro i
    by_cases hi : i ∈ S.remaining
    · simp only [complete, dite_eq_left hi]
      exact (Finset.mem_filter.mp (a ⟨i, hi⟩).2).2
    · rw [complete_recorded G S fixed a i hi]
      exact hslot i hi
  · intro i j hij
    by_cases hi : i ∈ S.remaining <;> by_cases hj : j ∈ S.remaining
    · simpa only [complete, dite_eq_left hi, dite_eq_left hj, graph, SimpleGraph.comap_adj, value] using
        ha ⟨i, hi⟩ ⟨j, hj⟩
    · simp only [complete, dite_eq_left hi, dite_eq_right hj]
      exact fun h => hcross j hj _ (value_mem_current G S ⟨⟨i, hi⟩, a ⟨i, hi⟩⟩) h.symm
    · simp only [complete, dite_eq_right hi, dite_eq_left hj]
      exact hcross i hi _ (value_mem_current G S ⟨⟨j, hj⟩, a ⟨j, hj⟩⟩)
    · simp only [complete, dite_eq_right hi, dite_eq_right hj]
      exact hind i hi j hj hij

def successfulAssignments (G : Input I V) (S : State I V) :
    Finset (Slots.Assignment (Domain G S)) :=
  Finset.univ.filter (fun a =>
    a ∈ TailConditioning.independentTransversals (Domain G S) (graph G S))

omit [Fintype I] [Fintype V] in
@[simp] theorem mem_successfulAssignments (G : Input I V) (S : State I V)
    (a : Slots.Assignment (Domain G S)) :
    a ∈ successfulAssignments G S ↔
      a ∈ TailConditioning.independentTransversals (Domain G S) (graph G S) := by
  simp [successfulAssignments]

omit [Fintype I] in

theorem successfulAssignments_nonempty [MeasurableSpace V] [MeasurableSingletonClass V]
    (G : Input I V) (S : State I V)
    (hno : ∀ v w, G.slot v = G.slot w → ¬ G.graph.Adj v w)
    (L Δ : ℕ) (hL : 3 ≤ L)
    (hsize : ∀ i ∈ S.remaining, L ≤ (domain G S i).card)
    (hdegree : ∀ v ∈ currentVertices G S, degree G S v ≤ Δ)
    (hsparse : 8 * Δ ≤ L) : (successfulAssignments G S).Nonempty := by
  classical
  let : ∀ i : Slot S, Nonempty (Domain G S i) := fun i =>
    Fintype.card_pos_iff.mp (by rw [card_domain]; exact lt_of_lt_of_le (by omega) (hsize i.1 i.2))
  apply (Slots.law_real_pos_iff_nonempty (successfulAssignments G S)).mp
  have h := (tail_conditioning G S hno L Δ hL hsize hdegree hsparse).1
  have he : (successfulAssignments G S : Set (Slots.Assignment (Domain G S))) =
      TailConditioning.independentTransversals (Domain G S) (graph G S) := by
    ext a
    exact mem_successfulAssignments G S a
  rwa [he]

def completionPMF (G : Input I V) (S : State I V) (fixed : I → V)
    (hG : (successfulAssignments G S).Nonempty) : PMF (I → V) :=
  (PMF.uniformOfFinset (successfulAssignments G S) hG).map (complete G S fixed)

omit [Fintype I] [Fintype V] in
theorem completionPMF_supported (G : Input I V) (S : State I V) (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty) (a : I → V)
    (ha : a ∈ (completionPMF G S fixed hG).support) :
    IsIndependentTransversal G a := by
  rcases (PMF.mem_support_map_iff _ _ _).mp ha with ⟨b, hb, rfl⟩
  apply complete_isIndependentTransversal G S fixed hslot hind hcross b
  exact (mem_successfulAssignments G S b).mp (by simpa using hb)

theorem sum_pmf_real (p : PMF (I → V)) : (∑ a, (p a).toReal) = 1 := by
  rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
  have h : (∑ a, p a) = 1 := by simpa only [tsum_fintype] using p.tsum_coe
  rw [h]
  simp

def completionOutputLaw (G : Input I V) (S : State I V) (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty) : OutputLaw G where
  weight a := (completionPMF G S fixed hG a).toReal
  nonnegative _ := ENNReal.toReal_nonneg
  mass_le_one := (sum_pmf_real _).le
  supported a ha := completionPMF_supported G S fixed hslot hind hcross hG a
    ((PMF.apply_pos_iff _ _).mp (ENNReal.toReal_pos_iff.mp ha).1)

theorem successMass_completionOutputLaw (G : Input I V) (S : State I V) (fixed : I → V)
    (hslot : ∀ i ∉ S.remaining, G.slot (fixed i) = i)
    (hind : ∀ i ∉ S.remaining, ∀ j ∉ S.remaining, i ≠ j →
      ¬ G.graph.Adj (fixed i) (fixed j))
    (hcross : ∀ i ∉ S.remaining, ∀ v ∈ currentVertices G S,
      ¬ G.graph.Adj (fixed i) v)
    (hG : (successfulAssignments G S).Nonempty) :
    successMass (completionOutputLaw G S fixed hslot hind hcross hG) = 1 :=
  sum_pmf_real _

end Balanced.Selection.Process.Tail

end

end OAI
