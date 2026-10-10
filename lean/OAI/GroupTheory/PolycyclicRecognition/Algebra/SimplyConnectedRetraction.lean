import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import OAI.GroupTheory.PolycyclicRecognition.Algebra.QuotientSectionCoordinates

namespace OAI

/-! # Simple connectivity of a split kernel

A continuous retraction preserves simple connectivity. A group quotient with
a normalized continuous section retracts onto its actual kernel.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped ContinuousMap

theorem simplyConnectedSpace_of_continuous_retraction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace Y] (i : X → Y) (r : Y → X)
    (hi : Continuous i) (hr : Continuous r) (hri : Function.LeftInverse r i) :
    SimplyConnectedSpace X := by
  have : PathConnectedSpace X := hri.surjective.pathConnectedSpace hr
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨inferInstance, ?_⟩
  intro x y p q
  have h := (SimplyConnectedSpace.paths_homotopic (p.map hi) (q.map hi)).map
    (⟨r, hr⟩ : C(Y, X))
  have h' := h.pathCast (hri x).symm (hri y).symm
  have hp : ((p.map hi).map hr).cast (hri x).symm (hri y).symm = p := by
    ext t
    exact hri (p t)
  have hq : ((q.map hi).map hr).cast (hri x).symm (hri y).symm = q := by
    ext t
    exact hri (q t)
  rwa [hp, hq] at h'

theorem simplyConnectedSpace_kernel_of_section
    {G Q : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [SimplyConnectedSpace G]
    (π : G →* Q) (hπ : Continuous π) (s : C(Q, G))
    (hs : ∀ q, π (s q) = q) (hsone : s 1 = 1) : SimplyConnectedSpace π.ker := by
  let r := quotientSectionResidual π s hs
  have hr : Continuous r := by
    exact (continuous_id.mul (s.continuous.comp hπ).inv).subtype_mk _
  apply simplyConnectedSpace_of_continuous_retraction
    (fun k : π.ker => (k : G)) r continuous_subtype_val hr
  intro k
  apply Subtype.ext
  change (k : G) * (s (π k))⁻¹ = k
  rw [show π k = 1 from k.property, hsone, inv_one, mul_one]

end PolycyclicRecognition

end

end OAI
