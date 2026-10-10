import Mathlib
import OAI.Geometry.Cannon.Flows.FlowSetup
import OAI.Geometry.Cannon.Boundary.BoundaryModulusSubexponential
import OAI.Geometry.Cannon.Boundary.BoundaryRecordData

namespace OAI

section
section
section
noncomputable section
section
section
namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification CannonPacking CannonApprox CannonCells CannonCharts
open CannonNode CannonAnnular Set Metric Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

theorem boundary_record_flow (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
    let ell := 2*visualExponent δ
    let a := Real.exp ell
    let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D),
    (∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j)) →
    (∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹) →
    (∀ B : ℝ, ∃ n, B < modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)) →
    ∃ Q : ℕ, 2 ≤ Q ∧ ∃ CP : ℝ, 0 < CP ∧ PolynomialPacking (X:=Boundary D) Q CP ∧
    ∃ L : ℝ, 1 ≤ L ∧
      (∀ x u v : Boundary D, ∀ s : ℝ, 0 < s → dist u x ≤ s → dist v x ≤ s →
        JoinedIn (ball x (L*s)) u v) ∧
    ∃ Ns : ℕ → ℕ, StrictMono Ns ∧ ∃ R : RecordData
      (boundaryHomeomorph D ⟨δ,hδ⟩) (fun n => ι (Ns n)) (fun n => p (Ns n))
        (fun n => (a^(Ns n))⁻¹), Nonempty (FlowSetup R ell L CE LE Q) := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
  let _ : BorelSpace (Boundary D) := ⟨rfl⟩
  let _ : LocallyPathConnectedSpace SphereTwo := CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D) := φ.symm.isQuotientMap.locallyPathConnectedSpace
  dsimp only
  intro d hd hdia hdc ι hι p hpsep hpnet hunbounded
  let ell := 2*visualExponent δ
  let a := Real.exp ell
  let CE := 2*Real.exp (visualExponent δ*(2*(8*δ+6):ℕ))
  let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
  have hell : 0 < ell := mul_pos (by norm_num) (visualExponent_pos δ)
  have hr (j : ℕ) : 0 < (a^j)⁻¹ := inv_pos.mpr (pow_pos (Real.exp_pos _) _)
  let M := fun j => modulus (fun i => ball (p j i) (2*(a^j)⁻¹)) (macroFamily d)
  have hmin (j : ℕ) : 0 < M j ∧ ∃ ω : ι j → ℝ,
      MacroscopicAdmissible (p j) ((a^j)⁻¹) d ω ∧ (∑ i, (ω i)^2)=M j := by
    apply sphere_macro_modulus_minimum φ d hd hdia (p j) ((a^j)⁻¹)
    intro x
    obtain ⟨i,hi⟩ := hpnet j x
    exact ⟨i,mem_ball.mpr (by rw [dist_comm]; linarith only [hi,hr j])⟩
  choose ω hω using fun j => (hmin j).2
  obtain ⟨Q,CP,hQ,hCP,hpack⟩ := relative_polynomial_packing D hδ
  obtain ⟨L,hL,hpaths⟩ := boundary_controlled_paths D hδ φ
  have hp : ∀ x u v : Boundary D, ∀ s : ℝ, 0 < s → dist u x ≤ s → dist v x ≤ s →
      JoinedIn (ball x (L*s)) u v := by
    intro x u v s hs hu hv
    convert hpaths x u v s hs (by simpa only [dist_comm] using hu) (by simpa only [dist_comm] using hv) using 1
    ext z
    simp only [mem_ball,mem_ofPred_eq,dist_comm]
  obtain ⟨Ns,hNs,⟨R⟩⟩ := boundary_record_data D hδ φ d hd hdia hdc ι p hpsep hpnet hunbounded
  refine ⟨Q,hQ,CP,hCP,hpack,L,hL,hp,Ns,hNs,R,?_⟩
  apply R.make_flow Q CP CE LE ell L d hpack hCP.le (by dsimp [CE]; positivity)
    (by dsimp [LE]; positivity) hell hL (by
      change d ≤ 1/(LE*3^2) at hdc
      simpa only [show (3:ℝ)^2=9 by norm_num,mul_comm LE 9] using hdc)
    M (fun j => (hmin j).1.le)
    (boundary_modulus_subexponential D hδ φ d hd hdia hdc ι p hpsep hpnet) ι p
    (fun j i i' hne => by simpa only [radius_eq_power] using hpsep j i i' hne) ω
    (fun j => by simpa only [radius_eq_power] using (hω j).1)
    (fun j => (hω j).2.le) (boundaryExpansion D hδ)
    (fun x j => by simpa only [radius_eq_power] using boundaryExpansion_formula D hδ x j) hp

end CannonRelease

end

section

open Set Topology

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G)

variable (hthin : D.ThinTriangles)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open Set Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) (hthin : D.ThinTriangles)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology
open scoped NNReal

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Filter Topology Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

namespace CannonRelease

open CannonGraph CannonVisual Set

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

local instance : Setoid (BasedRay D) := raySetoid D

end CannonRelease

end
end
end
end
end
end

end OAI
