import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.RealMarkedModels
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Vanishing transfer errors and shrinking physical marked neighborhoods. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def modelError (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem modelError_pos (n : ℕ) : 0 < modelError n := by
  unfold modelError
  positivity

theorem modelError_tendsto : Tendsto modelError atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

attribute [local instance] sphereMetric

def markedNeighborhoods {S : Type*} (σ : S → Sphere) (n : ℕ) (s : S) : Set Sphere :=
  ball (σ s) (modelError n)

theorem markedNeighborhoods_nhds {S : Type*} (σ : S → Sphere) (n : ℕ) (s : S) :
    markedNeighborhoods σ n s ∈ 𝓝 (σ s) :=
  ball_mem_nhds _ (modelError_pos n)

theorem markedNeighborhoods_shrink {S : Type*} (σ : S → Sphere) (s : S)
    {W : Set Sphere} (hW : W ∈ 𝓝 (σ s)) :
    ∀ᶠ n in atTop, markedNeighborhoods σ n s ⊆ W := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hW
  filter_upwards [modelError_tendsto.eventually (gt_mem_nhds hδ)] with n hn
  exact (ball_subset_ball hn.le).trans hball

theorem exists_shrinking_real_model_exhaustion
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G)
    {π : Sphere → Sphere} (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    {S : Type*} [Countable S] {σ : S → Sphere} (d : CountableRealCoordinates G π σ)
    (hcompat : d.NaturalCompatibility) :
    Nonempty (RealModelExhaustion d (markedNeighborhoods σ) modelError) :=
  exists_real_model_exhaustion hsard hsch hcompact hfinite hG hconn hinf
    hπ hclosed hsurj hr hTD d hcompat (markedNeighborhoods σ) (markedNeighborhoods_nhds σ)
    modelError modelError_pos

theorem RealModelExhaustion.eventually_marked_cap_in_nhds
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    (M : RealModelExhaustion d (markedNeighborhoods σ) modelError)
    (s : S) {W : Set Sphere} (hW : W ∈ 𝓝 (σ s)) :
    ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) ⊆
      π ⁻¹' W :=
  M.eventually_marked_cap_subset s (markedNeighborhoods_shrink σ s hW)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
