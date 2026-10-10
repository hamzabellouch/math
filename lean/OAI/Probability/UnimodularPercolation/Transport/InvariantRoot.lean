import Mathlib
import OAI.Probability.UnimodularPercolation.Main
import OAI.Probability.UnimodularPercolation.Graph.FullTopology

namespace OAI

/-! Haar measures and root transport for the full automorphism group. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory Topology
open scoped ENNReal
universe u v
variable {V : Type u} {E : Type v}
variable [TopologicalSpace V] [DiscreteTopology V]

noncomputable instance fullGraphAutMeasurableSpace (G : BondGraph V E) :
    MeasurableSpace (GraphAut G) := borel (GraphAut G)

instance graphAutBorel (G : BondGraph V E) : BorelSpace (GraphAut G) := ⟨rfl⟩

noncomputable def graphAutHaar (G : BondGraph V E) (hinj : Function.Injective G)
    (hloc : LocallyFinite G) (hconn : Connected G) (x : V) : Measure (GraphAut G) := by
  letI := locallyCompact_graphAut G hinj hloc hconn x
  exact Measure.haar

instance graphAutHaar_isHaar (G : BondGraph V E) (hinj : Function.Injective G)
    (hloc : LocallyFinite G) (hconn : Connected G) (x : V) :
    (graphAutHaar G hinj hloc hconn x).IsHaarMeasure := by
  let := locallyCompact_graphAut G hinj hloc hconn x
  exact inferInstanceAs (Measure.IsHaarMeasure Measure.haar)

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem graphStabilizer_eq_action (G : BondGraph V E) (x : V) :
    graphStabilizer G x = actionStabilizer (H := GraphAut G) x := rfl

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem graphStabilizer_inv (G : BondGraph V E) (x : V) :
    (graphStabilizer G x)⁻¹ = graphStabilizer G x := by
  ext g
  change (graphAutPerm G g).symm x = x ↔ graphAutPerm G g x = x
  rw [Equiv.symm_apply_eq,eq_comm]

theorem graphAutHaar_stabilizer_pos (G : BondGraph V E)
    (hinj : Function.Injective G) (hloc : LocallyFinite G) (hconn : Connected G) (x y : V) :
    0 < (graphAutHaar G hinj hloc hconn x).real (actionStabilizer (H := GraphAut G) y) := by
  apply ENNReal.toReal_pos
  · exact ((isOpen_graphStabilizer G y).measure_pos _ ⟨1,rfl⟩).ne'
  · exact (isCompact_graphStabilizer G hinj hloc hconn y).measure_lt_top.ne

theorem graphAutHaar_stabilizer_finite (G : BondGraph V E)
    (hinj : Function.Injective G) (hloc : LocallyFinite G) (hconn : Connected G) (x y : V) :
    graphAutHaar G hinj hloc hconn x (actionStabilizer (H := GraphAut G) y) ≠ ∞ :=
  (isCompact_graphStabilizer G hinj hloc hconn y).measure_lt_top.ne

def GraphUnimodular (G : BondGraph V E) (hinj : Function.Injective G)
    (hloc : LocallyFinite G) (hconn : Connected G) (x : V) : Prop :=
  (graphAutHaar G hinj hloc hconn x).IsMulRightInvariant

theorem graphAutHaar_invInvariant [Countable V] (G : BondGraph V E)
    (hinj : Function.Injective G) (hloc : LocallyFinite G) (hconn : Connected G) (x : V)
    (hu : GraphUnimodular G hinj hloc hconn x) :
    (graphAutHaar G hinj hloc hconn x).IsInvInvariant := by
  let := locallyCompact_graphAut G hinj hloc hconn x
  let μ := graphAutHaar G hinj hloc hconn x
  let : μ.IsMulRightInvariant := hu
  constructor
  have hc := Measure.isMulLeftInvariant_eq_smul_of_regular μ.inv μ
  have hf : μ (graphStabilizer G x) ≠ ∞ :=
    (isCompact_graphStabilizer G hinj hloc hconn x).measure_lt_top.ne
  have hp : μ (graphStabilizer G x) ≠ 0 :=
    ((isOpen_graphStabilizer G x).measure_pos μ ⟨1,rfl⟩).ne'
  have he := congrArg (fun ν : Measure (GraphAut G) => ν (graphStabilizer G x)) hc
  rw [Measure.inv_apply,graphStabilizer_inv,Measure.smul_apply] at he
  have hz : (μ.inv.haarScalarFactor μ : ℝ≥0∞) = 1 := by
    apply (ENNReal.mul_left_inj hp hf).mp
    simpa only [ENNReal.smul_def,smul_eq_mul,one_mul] using he.symm
  rw [hc,show μ.inv.haarScalarFactor μ = 1 from ENNReal.coe_eq_one.mp hz,one_smul]

theorem exists_rootTransport_of_unimodular [Nonempty V]
    (G : BondGraph V E) (hinj : Function.Injective G)
    (hloc : LocallyFinite G) (hconn : Connected G) (hqt : QuasiTransitive G) (x₀ : V)
    (hu : GraphUnimodular G hinj hloc hconn x₀) :
    ∃ (n : ℕ) (root : Fin n → V) (weight : Fin n → ℝ),
      weight = inverseStabilizerWeight (graphAutHaar G hinj hloc hconn x₀) root ∧
      (∀ i, 0 < weight i) ∧ (∑ i, weight i = 1) ∧
      RootTransport root weight (vertexAut G) ∧
      (∀ x, ∃ i, ∃ g ∈ vertexAut G, g (root i) = x) := by
  classical
  let : Countable V := countable_vertices hloc hconn
  let : MeasurableSpace V := borel V
  let : BorelSpace V := ⟨rfl⟩
  let : Finite (GraphOrbit G) := finite_graphOrbit G hqt
  let : Fintype (GraphOrbit G) := Fintype.ofFinite _
  let n := Fintype.card (GraphOrbit G)
  let q : Fin n ≃ GraphOrbit G := (Fintype.equivFin _).symm
  let root : Fin n → V := fun i => fullGraphOrbitRoot G (q i)
  let μ := graphAutHaar G hinj hloc hconn x₀
  let : μ.IsInvInvariant := graphAutHaar_invInvariant G hinj hloc hconn x₀ hu
  have hcov (x : V) : ∃ i : Fin n, x ∈ actionOrbit (H := GraphAut G) (root i) := by
    obtain ⟨i,g,hg⟩ := graphOrbitRoot_covers G x
    refine ⟨q.symm i,g,?_⟩
    simpa only [root,Equiv.apply_symm_apply] using hg
  let : Nonempty (Fin n) := ⟨(hcov x₀).choose⟩
  have hsep (i j : Fin n) (h : root j ∈ actionOrbit (H := GraphAut G) (root i)) : i = j :=
    q.injective (graphOrbitRoot_separates G (q i) (q j) h)
  have hvol (i : Fin n) : 0 < μ.real (actionStabilizer (H := GraphAut G) (root i)) :=
    graphAutHaar_stabilizer_pos G hinj hloc hconn x₀ (root i)
  refine ⟨n,root,inverseStabilizerWeight μ root,rfl,
    inverseStabilizerWeight_pos μ root hvol,
    inverseStabilizerWeight_sum μ root hvol,?_,?_⟩
  · apply rootTransport_of_invariant_measure μ
      (fun x => (continuous_aut_apply G x).measurable) root hvol
      (fun i => graphAutHaar_stabilizer_finite G hinj hloc hconn x₀ (root i))
      hcov hsep (vertexAut G)
    intro g
    exact graphAutPerm_mem G g
  · intro x
    obtain ⟨i,g,hg⟩ := hcov x
    exact ⟨i,graphAutPerm G g,graphAutPerm_mem G g,hg⟩

end Percolation

end OAI
