import Mathlib
import OAI.Geometry.Cannon.ScalarLimits.InteriorScalar
import OAI.Geometry.Cannon.Boundary.BoundaryBasedRay

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open Set Filter Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open Set Metric

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification CannonApprox CannonPlanar CannonChart CannonCharts
open CannonGrid CannonCells Set Metric Filter Topology MeasureTheory

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_record_scalar_limit (φ : Boundary D ≃ₜ CannonRelease.SphereTwo) :
    let _ := visualMetricSpace D hδ
    let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
    let _ : BorelSpace (Boundary D) := ⟨rfl⟩
    let a := Real.exp (2*visualExponent δ)
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D)
    (hpsep : ∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hunbounded : ∀ B : ℝ, ∃ n,
      B < modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)/lam^n),
    let M := fun n => modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
    ∃ e : Plane → Boundary D, ∃ he : IsOpenEmbedding e,
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (M ∘ N) atTop atTop ∧
        (∀ j l, l ≤ N j → M (N j-l) ≤ (lam^l)⁻¹*M (N j)) ∧
        ∃ ρ : (j : ℕ) → ι (N j) → ℝ, ∃ m : ℕ → ℕ, ∃ hm : ∀ j, 0 < m j,
        ∃ hρ : ∀ j i, 0 ≤ ρ j i,
        ∃ hadm : ∀ j, Admissible
            (fun i => (e ∘ squareMap) ⁻¹' ball (p (N j) i) (2*(a^(N j))⁻¹)) (ρ j),
          (∀ j, (∑ i, (ρ j i)^2) ≤ A/M (N j)) ∧
          (∀ j z, ∀ i : Index (3*m j), weight (3*m j) z i ≠ 0 →
            dist ((e ∘ squareMap) z)
              ((e ∘ squareMap) (vertex (3*m j) (by have := hm j; omega) i)) < (a^(N j))⁻¹) ∧
          let f := fun j => interiorScalar (e ∘ squareMap)
            (he.isEmbedding.comp squareMap_embedding) (p (N j)) ((a^(N j))⁻¹)
            (ρ j) (hρ j) (hadm j) (m j) (hm j)
          let μ := fun j => CannonAtomic.atomic (p (N j)) (ρ j) (M (N j))
            (by
              apply Real.sInf_nonneg
              rintro t ⟨w,_,rfl⟩
              exact sq_nonneg _)
          ∃ u : C(interior (range (e ∘ squareMap)), ℝ),
            (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧
            (∃ top bot, u top = 0 ∧ u bot = 1) ∧
            ∃ ν : FiniteMeasure (Boundary D), (ν.mass : ℝ) ≤ A ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
              Tendsto (f ∘ ψ) atTop (𝓝 u) ∧ Tendsto (μ ∘ ψ) atTop (𝓝 ν) := by
  let _ := visualMetricSpace D hδ
  let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
  let _ : BorelSpace (Boundary D) := ⟨rfl⟩
  let _ : LocallyPathConnectedSpace CannonRelease.SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  dsimp only
  intro d hd hdia hdc ι hι p hpsep hpnet lam hlam hunbounded
  obtain ⟨Q,CP,_hQ,hCP,hpack⟩ := relative_polynomial_packing D hδ
  obtain ⟨L,hL,hpaths⟩ := boundary_controlled_paths D hδ φ
  exact geometric_scalar_limit φ d hd hdia (Real.exp (2*visualExponent δ))
    (Real.one_lt_exp_iff.mpr (mul_pos (by norm_num) (visualExponent_pos δ))) Q CP
    (2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ)))
    (1/((8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ)))*3^2)) L hpack hCP.le
    (by positivity) (by positivity) hL hdc hpaths (boundary_smallball_expansion D hδ)
    ι p hpsep hpnet lam hlam hunbounded

end CannonRelease

end

section

section

open Set Topology

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G)

variable (hthin : D.ThinTriangles)

local instance boundaryRecordScalarLimitSetoid1 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) (hthin : D.ThinTriangles)

local instance boundaryRecordScalarLimitSetoid2 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid3 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid4 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid5 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid6 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid7 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid8 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid9 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid10 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid11 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid12 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid13 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid14 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid15 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid16 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid17 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

open Set Metric Topology

namespace CannonRelease

open CannonGraph CannonVisual CannonPaths Set Metric

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryRecordScalarLimitSetoid18 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

open Set MeasureTheory
open scoped BigOperators
open scoped NNReal ENNReal
open Set Metric
open Set Filter Topology

end
end
end
end
end
end
end
end
end
end

end OAI
