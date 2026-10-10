import OAI.Analysis.CircleDomains.Transfer.MixedMarkedModels
import OAI.Analysis.CircleDomains.Uniformization.AssignedParameterLimits

namespace OAI

/-! Assigned normal limits of the actual mixed stages, retaining the
convergent center and radius sequences used by Stokes. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

structure AssignedMixedModelLimit {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} {d : CountableRealCoordinates G π σ}
    {C : Type*} [LinearOrder C] {data : C → MaskedCoordinateData G d.source π σ}
    {retained : ℕ → C} {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ) where
  assignment : ∀ n, TerminalComponentAssignment (M.stages n).terminals.H
    (M.stages n).model.forward (M.stages n).model.domain
  subsequence : ℕ → ℕ
  function : ℂ → ℂ
  center : S → ℂ
  radius : S → ℝ
  cores : ℕ → SmoothJordanCore G
  contours : ∀ j, Fin (cores j).count → ℂ ≃ₜ ℂ
  strict : StrictMono subsequence
  converges : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
    finiteCoord ((M.stages (subsequence n)).model.forward (z : Sphere))) function
    atTop (((↑) : ℂ → Sphere) ⁻¹' G)
  normalized : IsPrincipalNormalized (extendAtInfinity function)
  conformal : IsConformalEquivalence (extendAtInfinity function) G (extendAtInfinity function '' G)
  bounds : ∀ s, ‖center s‖ ≤ 3 * M.real.radius ∧ radius s ∈ Icc 0 (3 * M.real.radius)
  nested : ∀ j, (cores j).carrier ⊆ interior (cores (j + 1)).carrier
  exhausts : (⋃ j, interior (cores j).carrier) = G
  boundary : ∀ j i, extendAtInfinity function ''
    (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((cores j).disk i))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior (contours j i))
  disjoint : ∀ j, Pairwise (Disjoint on fun i => closure (jordanInterior (contours j i)))
  image_core : ∀ j, (extendAtInfinity function '' (cores j).carrier)ᶜ =
    ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (contours j i)
  side : ∀ j i, extendAtInfinity function ''
    (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((cores j).disk i))) =
    (extendAtInfinity function '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (contours j i))
  marked : ∀ s, ∃ (index : ∀ j, Fin (cores j).count) (p : Sphere),
    p ∈ (extendAtInfinity function '' G)ᶜ ∧
    connectedComponentIn Gᶜ (d.sourceMark s) = ⋂ j, closedTerminalCap ((cores j).disk (index j)) ∧
    connectedComponentIn (extendAtInfinity function '' G)ᶜ p =
      ⋂ j, closedTerminalCap (contours j (index j)) ∧
    ((↑) : ℂ → Sphere) '' closedBall (center s) (radius s) ⊆
      connectedComponentIn (extendAtInfinity function '' G)ᶜ p ∧
    Tendsto (fun n => hausdorffDist
      (finiteCoord '' connectedComponentIn (M.stages (subsequence n)).model.domainᶜ
        ((assignment (subsequence n)).point (M.markIndex (subsequence n) s)))
      (closedBall (center s) (radius s))) atTop (𝓝 0)

  disk_center : ℕ → S → ℂ
  disk_radius : ℕ → S → ℝ
  disk_bounds : ∀ n s, ‖disk_center n s‖ ≤ 3 * M.real.radius ∧
    disk_radius n s ∈ Icc 0 (3 * M.real.radius)
  disk_eq : ∀ s, ∀ᶠ n in atTop,
    connectedComponentIn (M.stages (subsequence n)).model.domainᶜ
      ((assignment (subsequence n)).point (M.markIndex (subsequence n) s)) =
        ((↑) : ℂ → Sphere) '' closedBall (disk_center n s) (disk_radius n s)
  center_tendsto : ∀ s, Tendsto (fun n => disk_center n s) atTop (𝓝 (center s))
  radius_tendsto : ∀ s, Tendsto (fun n => disk_radius n s) atTop (𝓝 (radius s))

 theorem MixedModelExhaustion.exists_assigned_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {S : Type*} [Countable S] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {C : Type*} [LinearOrder C] {data : C → MaskedCoordinateData G d.source π σ}
    {retained : ℕ → C} {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ) (hG : IsOpen G) (hconn : IsConnected G) :
    Nonempty (AssignedMixedModelLimit M) := by
  let _ : ∀ n, Fintype (M.stages n).indices := fun n => (M.stages n).indices_finite.fintype
  have hconf (n : ℕ) : IsConformalOn (M.stages n).model.forward (M.real.cores n) := by
    rw [M.same_forward n]
    exact M.real.core_conformal n
  obtain ⟨a, s, F, c, r, K, J, hs, hl, hn, he, hb, hnest, hcover, hboundary,
      hdisj, himage, hside, hmark, cn, rn, hbn, hdisks, hcl, hrl⟩ :=
    exists_normalized_limit_with_assigned_parameters harea hmontel hhurwitz hzero hsard hsch
      (fun n => (M.stages n).terminals.H) (fun n => (M.stages n).terminals.disjoint_closures)
      (fun n => (M.stages n).model.forward) (fun n => (M.stages n).model.inverse)
      (fun n => (M.stages n).model.domain) (fun n => (M.stages n).model.equivalence)
      (fun n => (M.stages n).model.circle_domain) M.real.plane_open M.real.plane_connected
      M.real.plane_monotone
      (fun n z hz => M.core_model n (M.real.plane_core n (Or.inl ⟨z, hz, rfl⟩)))
      (fun n => (hconf n).mono (fun _ hp => M.real.plane_core n (Or.inl hp)))
      M.real.radius_pos (fun n => (M.real.exterior_core n).trans (M.core_model n))
      (fun n => (hconf n).mono
        ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.real.exterior_core n)))
      (fun n => (M.stages n).model.principal) M.real.exterior_plane hG hconn M.real.exhausts
      d.sourceMark d.sourceMark_outside M.markIndex M.eventually_sourceMark_captured
  exact ⟨⟨a, s, F, c, r, K, J, hs, hl, hn, he, hb, hnest, hcover, hboundary,
    hdisj, himage, hside, hmark, cn, rn, hbn, hdisks, hcl, hrl⟩⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
