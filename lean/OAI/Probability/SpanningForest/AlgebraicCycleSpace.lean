import OAI.Probability.SpanningForest.Definitions

namespace OAI

noncomputable section

namespace Problem336

abbrev EdgeFlow := EdgeCode →₀ ℝ

def edgeBoundary : EdgeFlow →ₗ[ℝ] (ℕ →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun e : EdgeCode =>
    Finsupp.single e.1.1 1 - Finsupp.single e.1.2 1)

@[simp] theorem edgeBoundary_single (e : EdgeCode) (c : ℝ) :
    edgeBoundary (Finsupp.single e c) =
      c • (Finsupp.single e.1.1 1 - Finsupp.single e.1.2 1) := by
  simp [edgeBoundary]

def finiteCodeEdges (K : FiniteSubgraphCode) : Set EdgeCode :=
  {e | e.1 ∈ K.2}

def graphCodeEdges (G : GraphCode) : Set EdgeCode :=
  {e | Adj G e.1.1 e.1.2}

def finiteCycleSpace (K : FiniteSubgraphCode) : Submodule ℝ EdgeFlow :=
  Finsupp.supported ℝ ℝ (finiteCodeEdges K) ⊓ LinearMap.ker edgeBoundary

def graphCycleSpace (G : GraphCode) : Submodule ℝ EdgeFlow :=
  Finsupp.supported ℝ ℝ (graphCodeEdges G) ⊓ LinearMap.ker edgeBoundary

@[simp] theorem mem_finiteCycleSpace (K : FiniteSubgraphCode) (f : EdgeFlow) :
    f ∈ finiteCycleSpace K ↔
      (∀ e ∈ f.support, e.1 ∈ K.2) ∧ edgeBoundary f = 0 := by
  simp [finiteCycleSpace, Finsupp.mem_supported, finiteCodeEdges, Set.subset_def]

@[simp] theorem mem_graphCycleSpace (G : GraphCode) (f : EdgeFlow) :
    f ∈ graphCycleSpace G ↔
      (∀ e ∈ f.support, Adj G e.1.1 e.1.2) ∧ edgeBoundary f = 0 := by
  simp [graphCycleSpace, Finsupp.mem_supported, graphCodeEdges, Set.subset_def]

 theorem finiteCycleSpace_mono {K L : FiniteSubgraphCode} (h : K.2 ⊆ L.2) :
    finiteCycleSpace K ≤ finiteCycleSpace L := by
  apply inf_le_inf_right
  exact Finsupp.supported_mono (fun _ he => h he)

 theorem IsFiniteConnectedSubgraph.finiteCycleSpace_le {G : GraphCode}
    {K : FiniteSubgraphCode} (hK : IsFiniteConnectedSubgraph G K) :
    finiteCycleSpace K ≤ graphCycleSpace G := by
  apply inf_le_inf_right
  exact Finsupp.supported_mono (fun e he => (hK.2.1 e.1 he).2.2.2)

 theorem IsConnectedExhaustion.finiteCodeEdges_monotone {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => finiteCodeEdges (H n)) := by
  apply monotone_nat_of_le_succ
  intro n e he
  exact (hH.2.1 n).2 he

 theorem IsConnectedExhaustion.iUnion_finiteCodeEdges {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    (⋃ n, finiteCodeEdges (H n)) = graphCodeEdges G := by
  ext e
  constructor
  · intro he
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp he
    exact ((hH.1 n).2.1 e.1 hn).2.2.2
  · intro he
    obtain ⟨n, hn⟩ := hH.2.2 e.1.1 e.1.2 e.2 he
    exact Set.mem_iUnion.mpr ⟨n, hn⟩

 theorem IsConnectedExhaustion.finiteCycleSpace_monotone {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => finiteCycleSpace (H n)) := by
  apply monotone_nat_of_le_succ
  intro n
  exact finiteCycleSpace_mono (hH.2.1 n).2

 theorem IsConnectedExhaustion.iSup_finiteCycleSpace {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    (⨆ n, finiteCycleSpace (H n)) = graphCycleSpace G := by
  have hm : Monotone (fun n => Finsupp.supported ℝ ℝ (finiteCodeEdges (H n))) :=
    fun _ _ h => Finsupp.supported_mono (hH.finiteCodeEdges_monotone h)
  unfold finiteCycleSpace graphCycleSpace
  rw [← hm.directed_le.iSup_inf_eq, ← Finsupp.supported_iUnion,
    hH.iUnion_finiteCodeEdges]

 theorem finiteCodeEdges_finite (K : FiniteSubgraphCode) :
    (finiteCodeEdges K).Finite :=
  Set.Finite.preimage Subtype.val_injective.injOn K.2.finite_toSet

instance finiteDimensional_finiteCycleSpace (K : FiniteSubgraphCode) :
    FiniteDimensional ℝ (finiteCycleSpace K) := by
  let : Fintype (finiteCodeEdges K) := (finiteCodeEdges_finite K).fintype
  let : FiniteDimensional ℝ (Finsupp.supported ℝ ℝ (finiteCodeEdges K)) :=
    (Finsupp.supportedEquivFinsupp (M := ℝ) (R := ℝ) (finiteCodeEdges K)).symm.finiteDimensional
  exact Submodule.finiteDimensional_of_le
    (show finiteCycleSpace K ≤ Finsupp.supported ℝ ℝ (finiteCodeEdges K) from inf_le_left)

abbrev EdgeHilbert := lp (fun _ : EdgeCode => ℝ) 2

def edgeFlowToHilbert : EdgeFlow →ₗ[ℝ] EdgeHilbert :=
  Finsupp.linearCombination ℝ (fun e : EdgeCode => lp.single 2 e (1 : ℝ))

@[simp] theorem edgeFlowToHilbert_single (e : EdgeCode) (c : ℝ) :
    edgeFlowToHilbert (Finsupp.single e c) = lp.single 2 e c := by
  simp [edgeFlowToHilbert, ← lp.single_smul]

@[simp] theorem edgeFlowToHilbert_apply (f : EdgeFlow) (e : EdgeCode) :
    edgeFlowToHilbert f e = f e := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a b f ha hb ih =>
    simp only [map_add, edgeFlowToHilbert_single, lp.coeFn_add, Pi.add_apply,
      Finsupp.add_apply, ih]
    simp [lp.single_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

 theorem edgeFlowToHilbert_injective : Function.Injective edgeFlowToHilbert := by
  intro f g h
  ext e
  simpa only [edgeFlowToHilbert_apply] using congrArg (fun x : EdgeHilbert => x e) h

def finiteHilbertCycleSpace (K : FiniteSubgraphCode) : Submodule ℝ EdgeHilbert :=
  (finiteCycleSpace K).map edgeFlowToHilbert

def closedGraphCycleSpace (G : GraphCode) : Submodule ℝ EdgeHilbert :=
  ((graphCycleSpace G).map edgeFlowToHilbert).topologicalClosure

instance finiteDimensional_finiteHilbertCycleSpace (K : FiniteSubgraphCode) :
    FiniteDimensional ℝ (finiteHilbertCycleSpace K) := by
  unfold finiteHilbertCycleSpace
  infer_instance

 theorem finiteHilbertCycleSpace_closed (K : FiniteSubgraphCode) :
    IsClosed (finiteHilbertCycleSpace K : Set EdgeHilbert) :=
  Submodule.closed_of_finiteDimensional _

 theorem IsConnectedExhaustion.finiteHilbertCycleSpace_monotone {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    Monotone (fun n => finiteHilbertCycleSpace (H n)) := by
  intro m n hmn
  exact Submodule.map_mono (hH.finiteCycleSpace_monotone hmn)

 theorem IsConnectedExhaustion.closure_iSup_finiteHilbertCycleSpace {G : GraphCode}
    {H : ℕ → FiniteSubgraphCode} (hH : IsConnectedExhaustion G H) :
    (⨆ n, finiteHilbertCycleSpace (H n)).topologicalClosure = closedGraphCycleSpace G := by
  unfold finiteHilbertCycleSpace closedGraphCycleSpace
  rw [← Submodule.map_iSup, hH.iSup_finiteCycleSpace]

end Problem336

end

end OAI
