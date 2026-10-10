import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem336.GraphBorel

def FiniteReach {ι : Type*} (r : ι → ι → Prop) : ℕ → ι → ι → Prop
  | 0, a, b => a = b
  | n + 1, a, b => FiniteReach r n a b ∨ ∃ c, FiniteReach r n a c ∧ r c b

theorem finiteReach_reflTransGen {ι : Type*} {r : ι → ι → Prop}
    {n : ℕ} {a b : ι} (h : FiniteReach r n a b) : Relation.ReflTransGen r a b := by
  induction n generalizing a b with
  | zero =>
      cases h
      exact .refl
  | succ n ih =>
      rcases h with h | ⟨c, hac, hcb⟩
      · exact ih h
      · exact (ih hac).tail hcb

theorem reflTransGen_iff_exists_finiteReach {ι : Type*} {r : ι → ι → Prop}
    {a b : ι} : Relation.ReflTransGen r a b ↔ ∃ n, FiniteReach r n a b := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | @tail b c hab hbc ih =>
        obtain ⟨n, hn⟩ := ih
        exact ⟨n + 1, Or.inr ⟨b, hn, hbc⟩⟩
  · rintro ⟨n, hn⟩
    exact finiteReach_reflTransGen hn

theorem measurable_finiteReach {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {r : α → ι → ι → Prop} (hr : ∀ a b, Measurable (fun x => r x a b))
    (n : ℕ) (a b : ι) : Measurable (fun x => FiniteReach (r x) n a b) := by
  induction n generalizing a b with
  | zero => exact measurable_const
  | succ n ih =>
      exact (ih a b).or (Measurable.exists (fun c => (ih a c).and (hr c b)))

theorem measurable_reflTransGen {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {r : α → ι → ι → Prop} (hr : ∀ a b, Measurable (fun x => r x a b))
    (a b : ι) : Measurable (fun x => Relation.ReflTransGen (r x) a b) := by
  simpa only [reflTransGen_iff_exists_finiteReach] using
    Measurable.exists (fun n => measurable_finiteReach hr n a b)

theorem measurable_adj (u v : ℕ) : Measurable (fun G : GraphCode => Adj G u v) := by
  have h₁ : Measurable (fun G : GraphCode => G.1) := measurable_subtype_coe
  have h₂ : Measurable (fun G : GraphCode => G.1 u) :=
    (measurable_pi_apply u).comp h₁
  have h₃ : Measurable (fun G : GraphCode => G.1 u v) :=
    (measurable_pi_apply v).comp h₂
  exact h₃.eq_const true

theorem measurable_graphConnected : Measurable (GraphConnected : GraphCode → Prop) := by
  exact Measurable.forall (fun u => Measurable.forall (fun v =>
    measurable_reflTransGen measurable_adj u v))

theorem measurableSet_graphConnected : MeasurableSet {G : GraphCode | GraphConnected G} :=
  measurable_graphConnected.setOf

private theorem finite_setOf_iff {ι : Type*} (p : ι → Prop) :
    Set.Finite {i | p i} ↔ ∃ s : Finset ι, ∀ i, p i → i ∈ s := by
  classical
  constructor
  · intro h
    exact ⟨h.toFinset, fun i hi => h.mem_toFinset.mpr hi⟩
  · rintro ⟨s, hs⟩
    exact s.finite_toSet.subset hs

theorem measurable_finite_setOf {α ι : Type*} [MeasurableSpace α] [Countable ι]
    {p : α → ι → Prop} (hp : ∀ i, Measurable (fun x => p x i)) :
    Measurable (fun x => Set.Finite {i | p x i}) := by
  simp only [finite_setOf_iff]
  exact Measurable.exists (fun s => Measurable.forall (fun i =>
    (hp i).imp measurable_const))

theorem measurable_graphLocallyFinite : Measurable (GraphLocallyFinite : GraphCode → Prop) := by
  exact Measurable.forall (fun u => measurable_finite_setOf (fun v => measurable_adj u v))

theorem measurableSet_graphLocallyFinite :
    MeasurableSet {G : GraphCode | GraphLocallyFinite G} :=
  measurable_graphLocallyFinite.setOf

theorem measurableSet_graphSupported :
    MeasurableSet {G : GraphCode | GraphConnected G ∧ GraphLocallyFinite G} :=
  measurableSet_graphConnected.inter measurableSet_graphLocallyFinite

theorem measurable_isFiniteConnectedSubgraph (K : FiniteSubgraphCode) :
    Measurable (fun G : GraphCode => IsFiniteConnectedSubgraph G K) := by
  exact measurable_const.and ((Measurable.forall (fun p : ℕ × ℕ =>
    measurable_const.imp (measurable_const.and (measurable_const.and
      (measurable_const.and (measurable_adj p.1 p.2)))))).and measurable_const)

theorem measurable_isConnectedExhaustion (H : ℕ → FiniteSubgraphCode) :
    Measurable (fun G : GraphCode => IsConnectedExhaustion G H) := by
  exact (Measurable.forall (fun n => measurable_isFiniteConnectedSubgraph (H n))).and
    (measurable_const.and (Measurable.forall (fun u => Measurable.forall (fun v =>
      measurable_const.imp ((measurable_adj u v).imp measurable_const)))))

theorem measurable_injective_labels :
    Measurable (fun U : ℕ → ℝ => Function.Injective U) := by
  exact Measurable.forall (fun u => Measurable.forall (fun v =>
    ((measurable_pi_apply u).eq (measurable_pi_apply v)).imp measurable_const))

theorem measurableSet_injective_labels :
    MeasurableSet {U : ℕ → ℝ | Function.Injective U} :=
  measurable_injective_labels.setOf

end Problem336.GraphBorel

end

end OAI
