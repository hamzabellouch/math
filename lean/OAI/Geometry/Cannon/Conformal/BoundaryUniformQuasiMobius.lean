import Mathlib
import OAI.Geometry.Cannon.Boundary.VisualScale
import OAI.Geometry.Cannon.Conformal.Distinct

namespace OAI

section
section
section
noncomputable section
namespace CannonRelease
open CannonGraph CannonVisual CannonQM
open scoped NNReal

universe v
variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_uniform_quasiMobius :
    let _ := visualMetricSpace D hδ
    ∃ η : Distortion, ∀ g : G, Controlled (boundaryHomeomorph D ⟨δ,hδ⟩ g) η := by
  let _ := visualMetricSpace D hδ
  let C : ℝ≥0 := ⟨16*Real.exp (visualExponent δ*(8*(8*δ+6):ℕ)),by positivity⟩
  have hC : 0 < C := by change 0 < (16*Real.exp (visualExponent δ*(8*(8*δ+6):ℕ)):ℝ); positivity
  refine ⟨OrderIso.mulLeft₀ C hC,?_⟩
  intro g
  apply controlled_of_product_bound _ (boundaryHomeomorph D ⟨δ,hδ⟩ g).injective C hC
  intro x y z w hh
  have H := boundary_uniform_cross_bound D hδ g x y z w hh.1 hh.2.2.2.2.2 hh.2.2.1 hh.2.2.2.1
  change (nndist (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g y) *
    nndist (boundaryTranslate D ⟨δ,hδ⟩ g z) (boundaryTranslate D ⟨δ,hδ⟩ g w) *
    nndist x w * nndist y z) ≤ C *
      (nndist (boundaryTranslate D ⟨δ,hδ⟩ g x) (boundaryTranslate D ⟨δ,hδ⟩ g w) *
       nndist (boundaryTranslate D ⟨δ,hδ⟩ g y) (boundaryTranslate D ⟨δ,hδ⟩ g z) *
       nndist x y * nndist z w)
  exact_mod_cast H

theorem boundary_uniform_conjugates {Y : Type*} [MetricSpace Y] (ψ : Boundary D ≃ₜ Y) :
    let _ := visualMetricSpace D hδ
    QuasiMobius ψ → ∃ η : Distortion, ∀ g : G,
      Controlled (ψ ∘ boundaryHomeomorph D ⟨δ,hδ⟩ g ∘ ψ.symm) η := by
  let _ := visualMetricSpace D hδ
  dsimp only
  rintro ⟨θ,hθ⟩
  obtain ⟨η,hη⟩ := boundary_uniform_quasiMobius D hδ
  exact ⟨((reciprocal θ.symm).trans η).trans θ,
    controlled_conjugates ψ hθ (boundaryHomeomorph D ⟨δ,hδ⟩) hη⟩

end CannonRelease

end
end
section
noncomputable section

section

open Set Topology

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G)

variable (hthin : D.ThinTriangles)

include hthin in
local instance boundaryUniformQuasiMobiusSetoid1 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) (hthin : D.ThinTriangles)

local instance boundaryUniformQuasiMobiusSetoid2 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid3 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid4 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid5 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid6 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid7 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid8 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid9 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid10 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid11 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid12 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid13 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid14 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid15 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid16 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance boundaryUniformQuasiMobiusSetoid17 : Setoid (BasedRay D) := raySetoid D

end CannonRelease

end

end
end
end
end

end OAI
