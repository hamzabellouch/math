import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.Coordinates
import OAI.Analysis.BiholderTransport.LocalFlow.LocalDomainFlow

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_smooth_coordinate_flow
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S) (hi : ∀ x ∈ S, (g x).IsInvertible)
    (x v : E) (hx : x ∈ S) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : (ℝ × (E × E)) → E × E,
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball (x,v) r) ∧
      (∀ z ∈ Metric.ball (x,v) r, Φ (0,z) = z) ∧
      ∀ t ∈ Ioo (-r) r, ∀ z ∈ Metric.ball (x,v) r,
        (Φ (t,z)).1 ∈ S ∧
        HasDerivAt (fun q => (Φ (q,z)).1) (Φ (t,z)).2 t ∧
        HasDerivAt (fun q => (Φ (q,z)).2)
          (-coordinateChristoffel g (Φ (t,z)).1 (Φ (t,z)).2 (Φ (t,z)).2) t := by
  have hf : ContDiffOn ℝ ∞ (coordinateGeodesicField g) (S ×ˢ (univ : Set E)) := by
    intro z hz
    exact (contDiffAt_coordinateGeodesicField ((hg z.1 hz.1).contDiffAt
      (hS.mem_nhds hz.1)) (hi z.1 hz.1)).contDiffWithinAt
  obtain ⟨r,hr,_,Φ,hΦ,hΦ0,hder⟩ := exists_smooth_local_flow_on
    (hS.prod isOpen_univ) hf (a := (x,v)) ⟨hx,mem_univ _⟩
  refine ⟨r,hr,Φ,hΦ,hΦ0,?_⟩
  intro t ht z hz
  have h := hder t ht z hz
  exact ⟨h.1.1,h.2.fst,h.2.snd⟩

end WeakMTWTransport

end

end OAI
