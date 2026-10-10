import OAI.GroupTheory.PolycyclicRecognition.Lattices.SolvableLatticeModel
import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import Mathlib.Topology.Connected.Clopen

namespace OAI

/-!
# Compatible metrics for the solvable Lie model

The metric existence input is the precise specialization of Cornulier–de
la Harpe, *Metric Geometry of Locally Compact Groups*, EMS Tracts in
Mathematics 25 (2016), Proposition 4.B.9, p.108: a second-countable locally
compact group is compactly generated if and only if it admits a proper
compatible left-invariant large-scale-geodesic metric.

We prove compact generation from a compact identity neighborhood and
connectedness. The metric-existence input is separate from Dekimpe's
lattice-realization theorem and contains no recognition assertion.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Filter Topology
open scoped Manifold

/-- A compatible proper left-invariant metric together with its explicit
large-scale-geodesic chains. -/
structure ProperChainMetric (G : Type*) [Group G] [TopologicalSpace G] where
  metric : MetricSpace G
  topology_eq : metric.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace G›
  proper : letI := metric; ProperSpace G
  leftInvariant : letI := metric; IsIsometricSMul G G
  chains : letI := metric; LinearMetricChains G

namespace ProperChainMetric

variable {G : Type*} [Group G] [TopologicalSpace G] (d : ProperChainMetric G)

/-- Normalize the metric so that its topology is definitionally the
original topology; the existing Lie charts then remain usable. -/
abbrev compatibleMetric : MetricSpace G :=
  d.metric.replaceTopology d.topology_eq.symm

theorem compatibleMetric_eq : d.compatibleMetric = d.metric :=
  d.metric.replaceTopology_eq d.topology_eq.symm

theorem proper_compatibleMetric : letI := d.compatibleMetric; ProperSpace G := by
  rw [d.compatibleMetric_eq]
  exact d.proper

theorem isometric_compatibleMetric : letI := d.compatibleMetric; IsIsometricSMul G G := by
  rw [d.compatibleMetric_eq]
  exact d.leftInvariant

def chains_compatibleMetric : letI := d.compatibleMetric; LinearMetricChains G := by
  rw [d.compatibleMetric_eq]
  exact d.chains

end ProperChainMetric

/-- Any compact identity neighborhood in a connected topological group
generates the entire group. -/
theorem closure_eq_top_of_mem_nhds_one
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ConnectedSpace G] {K : Set G} (hK : K ∈ 𝓝 (1 : G)) :
    Subgroup.closure K = ⊤ := by
  let J := Subgroup.closure K
  have hopen : IsOpen (J : Set G) := J.isOpen_of_mem_nhds
    (Filter.mem_of_superset hK Subgroup.subset_closure)
  have hclopen : IsClopen (J : Set G) := ⟨J.isClosed_of_isOpen hopen, hopen⟩
  have hall : (J : Set G) = Set.univ := hclopen.eq_univ ⟨1, J.one_mem⟩
  exact SetLike.coe_injective hall

/-- A connected locally compact group has a compact generating set. -/
theorem exists_compact_generating_set
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ConnectedSpace G] [LocallyCompactSpace G] :
    ∃ K : Set G, IsCompact K ∧ Subgroup.closure K = ⊤ := by
  obtain ⟨K, hK, hnhds⟩ := exists_compact_mem_nhds (1 : G)
  exact ⟨K, hK, closure_eq_top_of_mem_nhds_one hnhds⟩

/-- The implication (i)⇒(ii) of Cornulier–de la Harpe (2016),
Proposition 4.B.9, with the chain witnesses retained. -/
def GeodesicMetricExistenceInput : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G],
    (∃ K : Set G, IsCompact K ∧ Subgroup.closure K = ⊤) →
      Nonempty (ProperChainMetric G)

/-- Connectedness discharges the compact-generation hypothesis of the
published metric-existence theorem for the solvable Lie model. -/
theorem SimplyConnectedSolvableLieModel.nonempty_properChainMetric
    (S : SimplyConnectedSolvableLieModel) (metricInput : GeodesicMetricExistenceInput) :
    Nonempty (ProperChainMetric S.carrier) := by
  let : IsTopologicalGroup S.carrier :=
    topologicalGroup_of_lieGroup (𝓘(ℝ, S.modelSpace)) ⊤
  let : LocallyCompactSpace S.carrier :=
    Manifold.locallyCompact_of_finiteDimensional (𝓘(ℝ, S.modelSpace))
  exact metricInput S.carrier (exists_compact_generating_set S.carrier)

end PolycyclicRecognition

end

end OAI
