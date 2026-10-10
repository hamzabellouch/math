import OAI.Probability.BenjaminiSchramm.ThinSphereProbability

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

def ballSnapshotCell (G : BondGraph V E) (x : V) (j : ℕ) (U W : Finset V) : Set (Set E) :=
  {ω | intrinsicBall G ω x (j-1) = U ∧ intrinsicBall G ω x j = W}

theorem ballSnapshotCell_dependsOn (G : BondGraph V E) (x : V)
    (j : ℕ) (U W : Finset V) :
    DependsOn (fun ω => ω ∈ ballSnapshotCell G x j U W) (ballIncidentEdges G U) := by
  intro ω η hagree
  apply propext
  have hforward (ω η : Set E)
      (hωη : ∀ e ∈ ballIncidentEdges G U, e ∈ ω ↔ e ∈ η)
      (hω : ω ∈ ballSnapshotCell G x j U W) : η ∈ ballSnapshotCell G x j U W := by
    have hballs := intrinsicBall_history_eq_of_incident_agreement G ω η x j (by
      intro e he
      rw [hω.1] at he
      exact hωη e he)
    exact ⟨(hballs (j-1) (Nat.sub_le j 1)).symm.trans hω.1,(hballs j le_rfl).symm.trans hω.2⟩
  exact ⟨hforward ω η (fun e he => (hagree e he).to_iff),
    hforward η ω (fun e he => (hagree e he).symm.to_iff)⟩

theorem measurableSet_ballSnapshotCell [Countable V] (G : BondGraph V E)
    (hloc : LocallyFinite G) (x : V) (j : ℕ) (U W : Finset V) :
    MeasurableSet (ballSnapshotCell G x j U W) := by
  have hU := measurableSet_intrinsicBall_eq G hloc Set.univ x (j-1) U
  have hW := measurableSet_intrinsicBall_eq G hloc Set.univ x j W
  simpa only [ballSnapshotCell, Set.inter_univ, Set.ofPred_and] using hU.inter hW

theorem ballSnapshotCell_pairwise (G : BondGraph V E) (x : V) (j : ℕ) :
    Pairwise (fun a b : Finset V × Finset V =>
      Disjoint (ballSnapshotCell G x j a.1 a.2) (ballSnapshotCell G x j b.1 b.2)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro ω ha hb
  apply hab
  exact Prod.ext (Finset.coe_injective (ha.1.symm.trans hb.1))
    (Finset.coe_injective (ha.2.symm.trans hb.2))

theorem exists_ballSnapshotCell (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x : V) (j : ℕ) :
    ∃ a : Finset V × Finset V, ω ∈ ballSnapshotCell G x j a.1 a.2 := by
  let hU := (finite_reachBall hloc x (j-1)).subset (intrinsicBall_subset_reachBall G ω x (j-1))
  let hW := (finite_reachBall hloc x j).subset (intrinsicBall_subset_reachBall G ω x j)
  exact ⟨(hU.toFinset,hW.toFinset),hU.coe_toFinset.symm,hW.coe_toFinset.symm⟩

theorem ballSnapshotCell_fresh_connection_factor [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    (x y z : V) (j : ℕ) (U W : Finset V) :
    law p (ballSnapshotCell G x j U W ∩
      {ω | Conn G (ω \ ballIncidentEdges G U) z y}) =
      law p (ballSnapshotCell G x j U W) *
        law p {ω | Conn G (ω \ ballIncidentEdges G U) z y} := by
  have hm : Measurable (fun ω : Set E => ω \ ballIncidentEdges G U) :=
    measurable_set_iff.mpr (fun e => (measurable_set_mem e).and measurable_const)
  unfold law
  rw [←CriticalPercolation.BernoulliProduct.law_const]
  apply CriticalPercolation.BernoulliProduct.measure_inter_of_separate_blocks
    (fun _ => p) (ballIncidentEdges G U) _ _
    (measurableSet_ballSnapshotCell G hloc x j U W)
    ((measurableSet_conn G z y).preimage hm)
    (ballSnapshotCell_dependsOn G x j U W)
  intro ω η hagree
  have he : Set.diff ω (ballIncidentEdges G U) = Set.diff η (ballIncidentEdges G U) := by
    apply Set.ext
    intro e
    change (ω e ∧ e ∉ ballIncidentEdges G U) ↔ (η e ∧ e ∉ ballIncidentEdges G U)
    by_cases hi : e ∈ ballIncidentEdges G U
    · simp only [hi,not_true_eq_false,and_false]
    · simp only [hi,not_false_eq_true,and_true]
      exact (hagree e hi).to_iff
  change (Conn G (Set.diff ω (ballIncidentEdges G U)) z y) =
    (Conn G (Set.diff η (ballIncidentEdges G U)) z y)
  rw [he]

end Percolation.BenjaminiSchramm

end OAI
