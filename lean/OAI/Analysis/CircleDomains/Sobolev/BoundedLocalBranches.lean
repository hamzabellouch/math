import OAI.Analysis.CircleDomains.Selection.BandStability
import OAI.Analysis.CircleDomains.Sobolev.CircleBranchEnergy
import OAI.Analysis.CircleDomains.Uniformization.Conformal

namespace OAI

/-! Local bounded lifts can be used in the compact-band construction by
setting them to zero outside their patch. Their bands, local continuity,
and physical derivatives within the open patch are unchanged. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

def localBranchRepresentative {X : Type*} (V : Set X) (u : X → ℝ) : X → ℝ := V.indicator u

theorem localBranchRepresentative_bound {X : Type*} {D V : Set X}
    {u : X → ℝ} {M : ℝ} (hM : 0 ≤ M) (hu : ∀ x ∈ D ∩ V, |u x| ≤ M) :
    ∀ x ∈ D, |localBranchRepresentative V u x| ≤ M := by
  classical
  intro x hx
  by_cases hV : x ∈ V
  · simpa only [localBranchRepresentative, indicator_of_mem hV] using hu x ⟨hx, hV⟩
  · simpa only [localBranchRepresentative, indicator_of_notMem hV, abs_zero] using hM

theorem localBranchRepresentative_eventuallyEq
    {X : Type*} [TopologicalSpace X] {V : Set X} (hV : IsOpen V)
    (u : X → ℝ) {x : X} (hx : x ∈ V) :
    localBranchRepresentative V u =ᶠ[𝓝 x] u := by
  filter_upwards [hV.mem_nhds hx] with y hy
  exact indicator_of_mem hy u

theorem localBranchRepresentative_circle_band
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {D V : Set X} (hV : IsOpen V) (u : X → ℝ) {x : X} (hx : x ∈ V) :
    {θ | (x, θ) ∈ circleBandGraph D (localBranchRepresentative V u)} =
      {θ | (x, θ) ∈ circleBandGraph D u} := by
  have heq : localBranchRepresentative V u =ᶠ[𝓝[D] x] u :=
    (localBranchRepresentative_eventuallyEq hV u hx).filter_mono nhdsWithin_le_nhds
  have herr : Tendsto (fun y => localBranchRepresentative V u y - u y) (𝓝[D] x) (𝓝 0) := by
    have hz : (fun y => localBranchRepresentative V u y - u y) =ᶠ[𝓝[D] x] fun _ => 0 :=
      heq.mono (fun y hy => by dsimp only; rw [hy, sub_self])
    exact Tendsto.congr' hz.symm tendsto_const_nhds
  exact circleBand_fiber_eq_of_vanishing_difference herr

theorem localBranchRepresentative_continuousOn
    {X : Type*} [TopologicalSpace X] {D V : Set X} {u : X → ℝ}
    (hu : ContinuousOn u (D ∩ V)) : ContinuousOn (localBranchRepresentative V u) (D ∩ V) := by
  apply hu.congr
  intro x hx
  exact indicator_of_mem hx.2 u

theorem localBranchRepresentative_contDiffOn
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]
    {V : Set X} (hV : IsOpen V) (u : X → ℝ) (p : E → X) (hp : Continuous p)
    {A : Set E} {n : WithTop ℕ∞} (hu : ContDiffOn ℝ n (u ∘ p) A)
    (hA : MapsTo p A V) : ContDiffOn ℝ n (localBranchRepresentative V u ∘ p) A := by
  intro z hz
  apply (hu z hz).congr_of_eventuallyEq
  · exact ((localBranchRepresentative_eventuallyEq hV u (hA hz)).comp_tendsto
      (hp.tendsto z)).filter_mono nhdsWithin_le_nhds
  · exact indicator_of_mem (hA hz) u

end CircleDomainRigidity

end

end OAI
