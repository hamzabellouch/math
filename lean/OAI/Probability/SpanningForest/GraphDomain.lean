import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336

def ReachLength (G : GraphCode) : ℕ → ℕ → ℕ → Prop
  | 0, u, v => u = v
  | n + 1, u, v => ∃ w, ReachLength G n u w ∧ Adj G w v

theorem reachLength_reflTransGen {G : GraphCode} {n u v : ℕ}
    (h : ReachLength G n u v) : Relation.ReflTransGen (Adj G) u v := by
  induction n generalizing v with
  | zero =>
      change u = v at h
      subst v
      exact .refl
  | succ n ih =>
      obtain ⟨w, hw, hv⟩ := h
      exact (ih hw).tail hv

theorem reflTransGen_iff_exists_reachLength (G : GraphCode) (u v : ℕ) :
    Relation.ReflTransGen (Adj G) u v ↔ ∃ n, ReachLength G n u v := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail v w h hv ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, v, hn, hv⟩
  · rintro ⟨n, hn⟩
    exact reachLength_reflTransGen hn

theorem measurable_adj (u v : ℕ) :
    Measurable (fun G : GraphCode => Adj G u v) := by
  have h : Measurable (fun G : GraphCode => G.1 u v) :=
    (measurable_pi_apply v).comp
      ((measurable_pi_apply u).comp measurable_subtype_coe)
  exact h.eq_const true

theorem measurable_reachLength (n u v : ℕ) :
    Measurable (fun G : GraphCode => ReachLength G n u v) := by
  induction n generalizing v with
  | zero => exact measurable_const
  | succ n ih =>
      exact Measurable.exists (fun w => (ih w).and (measurable_adj w v))

theorem measurable_reflTransGen (u v : ℕ) :
    Measurable (fun G : GraphCode => Relation.ReflTransGen (Adj G) u v) := by
  simp_rw [reflTransGen_iff_exists_reachLength]
  exact Measurable.exists (fun n => measurable_reachLength n u v)

theorem measurable_graphConnected : Measurable GraphConnected := by
  exact Measurable.forall (fun u =>
    Measurable.forall (fun v => measurable_reflTransGen u v))

theorem measurableSet_graphConnected :
    MeasurableSet {G : GraphCode | GraphConnected G} :=
  measurable_graphConnected.setOf

theorem graphLocallyFinite_iff_bounded_neighbors (G : GraphCode) :
    GraphLocallyFinite G ↔ ∀ u, ∃ n, ∀ v, Adj G u v → v ≤ n := by
  simp only [GraphLocallyFinite, Set.finite_iff_bddAbove]
  rfl

theorem measurable_graphLocallyFinite : Measurable GraphLocallyFinite := by
  change Measurable (fun G : GraphCode => GraphLocallyFinite G)
  simp_rw [graphLocallyFinite_iff_bounded_neighbors]
  exact Measurable.forall (fun u => Measurable.exists (fun n =>
    Measurable.forall (fun v => (measurable_adj u v).imp measurable_const)))

theorem measurableSet_graphLocallyFinite :
    MeasurableSet {G : GraphCode | GraphLocallyFinite G} :=
  measurable_graphLocallyFinite.setOf

theorem measurableSet_validGraph :
    MeasurableSet {G : GraphCode | GraphConnected G ∧ GraphLocallyFinite G} :=
  measurableSet_graphConnected.inter measurableSet_graphLocallyFinite

end Problem336

end

end OAI
