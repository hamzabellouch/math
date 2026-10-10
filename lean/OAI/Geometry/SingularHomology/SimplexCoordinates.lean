import OAI.Combinatorics.PerfectMatching.Simplex
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import Mathlib.Geometry.Convex.ConvexSpace.Barycenter
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Algebra.Module.LocallyConvex

namespace OAI

noncomputable section

open Convexity

namespace Problem340.RealSimplex

variable {Index : Type*} [Fintype Index]

instance coordinatesFun : CoeFun (StdSimplex ℝ Index) (fun _ => Index → ℝ) :=
  ⟨fun point => point.weights⟩

def coordinates (point : StdSimplex ℝ Index) : Index → ℝ := point.weights

omit [Fintype Index] in
@[simp] lemma single_apply [DecidableEq Index] (vertex index : Index) :
    StdSimplex.single (R := ℝ) vertex index = if vertex = index then 1 else 0 := by
  change (StdSimplex.single vertex).weights index = _
  simp [Finsupp.single_apply]

@[simp] lemma barycenter_apply [Nonempty Index] (index : Index) :
    (StdSimplex.barycenter : StdSimplex ℝ Index) index = (Fintype.card Index : ℝ)⁻¹ :=
  StdSimplex.weights_barycenter_apply index

lemma map_apply {Target : Type*} [Fintype Target] [DecidableEq Target]
    (mapping : Index → Target) (point : StdSimplex ℝ Index) (index : Target) :
    point.map mapping index =
      ∑ source ∈ Finset.univ.filter (fun source => mapping source = index), point source := by
  classical
  change (point.map mapping).weights index = _
  rw [StdSimplex.weights_map, Finsupp.mapDomain_apply,
    Finsupp.sum_fintype _ _ (by simp), Finset.sum_filter]
  simp [Finsupp.single_apply]

lemma coordinates_injective : Function.Injective (coordinates (Index := Index)) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ Index).injective

def coordinateSet (Index : Type*) [Fintype Index] : Set (Index → ℝ) :=
  {weights | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1}

lemma mem_coordinateSet (point : StdSimplex ℝ Index) :
    coordinates point ∈ coordinateSet Index :=
  ⟨point.weights_nonneg, point.total_of_fintype⟩

lemma convex_coordinateSet : Convex ℝ (coordinateSet Index) :=
  MatchingEntropy.convex_probabilitySimplex Index

def coordinateHomeomorph : StdSimplex ℝ Index ≃ₜ coordinateSet Index :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ Index).toHomeomorph.trans
    (Homeomorph.setCongr (by
      rw [StdSimplex.range_toFun_comp_weights]
      ext weights
      simp [coordinateSet]))

@[simp] lemma coordinateHomeomorph_apply (point : StdSimplex ℝ Index) :
    (coordinateHomeomorph point : Index → ℝ) = coordinates point := rfl

@[simp] lemma coordinateHomeomorph_symm_apply (point : coordinateSet Index) :
    coordinates (coordinateHomeomorph.symm point) = point :=
  congrArg Subtype.val (coordinateHomeomorph.apply_symm_apply point)

instance metricSpace : MetricSpace (StdSimplex ℝ Index) :=
  (StdSimplex.isEmbedding_toFun_comp_weights ℝ Index).comapMetricSpace _

@[simp] lemma coordinateHomeomorph_symm_apply_at (point : coordinateSet Index) (index : Index) :
    coordinateHomeomorph.symm point index = point.val index :=
  congrFun (coordinateHomeomorph_symm_apply point) index

lemma contractible [Nonempty Index] : ContractibleSpace (StdSimplex ℝ Index) := by
  have : ContractibleSpace (coordinateSet Index) :=
    convex_coordinateSet.contractibleSpace
      ⟨coordinates (StdSimplex.single (Classical.arbitrary Index)), mem_coordinateSet _⟩
  exact (coordinateHomeomorph (Index := Index)).contractibleSpace

lemma locallyPathConnected : LocallyPathConnectedSpace (StdSimplex ℝ Index) := by
  have : LocallyPathConnectedSpace (coordinateSet Index) :=
    convex_coordinateSet.locallyPathConnectedSpace
  exact (coordinateHomeomorph (Index := Index)).symm.locallyPathConnectedSpace

end Problem340.RealSimplex

end

end OAI
