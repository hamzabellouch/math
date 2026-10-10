import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteOpenWitness
import OAI.Probability.CriticalPercolation.Gluing.CorridorNormalization
import OAI.Probability.CriticalPercolation.Criticality.RestrictedSeed

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def boxMove (t z : V → ℝ) (m : ℕ) (precision radius : ℝ) (y : V) (s : ℝ) : Set (Set E) :=
  {ω | ∃ a∈G.vertexBall y m, ∃ b, ∃ w : (G.openGraph ω).Walk a b,
    (∀ x∈w.support, |t x-t y|≤radius ∧ |z x-z y|≤radius) ∧
    |t b-(t y+1)|≤precision ∧ |z b-(z y+s)|≤precision}

lemma coordinateMove_eq_boxMove (t z : V → ℝ) (m : ℕ) (e : ℝ) (y : V) (s : ℝ) :
    G.coordinateMove t z m e y s=G.boxMove t z m (e/4) 100 y s := rfl

lemma walk_induced_support {S : Set V} {ω : Set E} {a b : V}
    (w : (G.openGraph (ω∩G.inducedEdges S)).Walk a b) (hb : b∈S) :
    ∀ x∈w.support, x∈S := by
  induction w with
  | nil =>
    intro x hx
    simp only [SimpleGraph.Walk.support_nil,List.mem_singleton] at hx
    subst x
    exact hb
  | @cons a c b hac w ih =>
    intro x hx
    rcases (List.mem_cons.mp hx) with hxa|hx
    · rw [hxa]
      exact ((G.open_induced_adj S ω a c).mp hac).2.1
    · exact ih hb x hx

lemma boxMove_eq_restrictedSeed (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    G.boxMove t z m q B y s=G.restrictedSeed (G.vertexBall y m)
      {b | (|t b-(t y+1)|≤q ∧ |z b-(z y+s)|≤q) ∧ |t b-t y|≤B ∧ |z b-z y|≤B}
      (G.inducedEdges {x | |t x-t y|≤B ∧ |z x-z y|≤B}) := by
  ext ω
  constructor
  · rintro ⟨a,ha,b,w,hw,ht,hz⟩
    exact Set.mem_iUnion₂.mpr ⟨a,ha,b,G.walk_reachable_induced _ ω w hw,⟨ht,hz⟩,hw b w.end_mem_support⟩
  · intro h
    obtain ⟨a,ha,b,⟨w⟩,hb⟩ := Set.mem_iUnion₂.mp h
    let w' := w.mapLe (G.openGraph_mono Set.inter_subset_left)
    refine ⟨a,ha,b,w',?_,hb.1.1,hb.1.2⟩
    intro x hx
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hx
    exact G.walk_induced_support w hb.2 x hx

lemma restrictedSeed_upper (A T : Set V) (S : Set E) : IsUpperSet (G.restrictedSeed A T S) := by
  intro ω τ h hω
  exact G.seedHitEvent_upper A T (Set.inter_subset_inter_left S h) hω

lemma restrictedSeed_finiteWitness (A T : Set V) (S : Set E) :
    BernoulliProduct.HasFiniteOpenWitness (G.restrictedSeed A T S) := by
  intro ω hω
  obtain ⟨a,ha,b,hr,hb⟩ := Set.mem_iUnion₂.mp hω
  obtain ⟨K,hK,hKsub,hKr⟩ := G.mem_cluster_finite_witness hr
  refine ⟨K,hK,fun _ he => (hKsub he).1,?_⟩
  change K∩S∈G.seedHitEvent A T
  rw [Set.inter_eq_left.mpr (fun _ he => (hKsub he).2)]
  exact Set.mem_iUnion₂.mpr ⟨a,ha,b,hKr,hb⟩

lemma boxMove_upper (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    IsUpperSet (G.boxMove t z m q B y s) := by
  rw [G.boxMove_eq_restrictedSeed]
  exact G.restrictedSeed_upper _ _ _

lemma boxMove_finiteWitness (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    BernoulliProduct.HasFiniteOpenWitness (G.boxMove t z m q B y s) := by
  rw [G.boxMove_eq_restrictedSeed]
  exact G.restrictedSeed_finiteWitness _ _ _

lemma boxMove_measurable [Countable V] [Countable E]
    (t z : V → ℝ) (m : ℕ) (q B : ℝ) (y : V) (s : ℝ) :
    MeasurableSet (G.boxMove t z m q B y s) := by
  rw [G.boxMove_eq_restrictedSeed]
  exact G.restrictedSeed_measurable _ _ _

lemma lower_two_boxMoves [Countable E] (t z : V → ℝ) (m : ℕ) (q B : ℝ)
    (o : V) (pc : unitInterval) (hpc : 0<pc) (eta : ℝ)
    (hm : ∀ b : Bool, 1-eta<(BernoulliProduct.law (fun _ : E => pc)).real
      (G.boxMove t z m q B o (Corridor.sign b))) :
    ∃ p : unitInterval, (pc : ℝ)/2≤p ∧ p<pc ∧ ∀ b : Bool,
      1-eta<(BernoulliProduct.law (fun _ : E => p)).real
        (G.boxMove t z m q B o (Corridor.sign b)) :=
  BernoulliProduct.exists_lower_parameter _ (fun _ => G.boxMove_upper _ _ _ _ _ _ _)
    (fun _ => G.boxMove_finiteWitness _ _ _ _ _ _ _) pc hpc (fun _ => 1-eta) hm

end CriticalPercolation.BondGraph
end
end
end

end OAI
