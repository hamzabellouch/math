import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Transfer.CountableRealTransfer
import OAI.Analysis.CircleDomains.Selection.RealStageEstimates
import OAI.Analysis.CircleDomains.Topology.SphereCoreExhaustion

namespace OAI

/-!
# Exhausting real transfer models

The prescribed source sets and the common exterior are constructed from
the domain. Thus the normal-family hypotheses follow from the actual
finite transfers, rather than being extra assumptions on their maps.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

structure RealModelExhaustion {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (d : CountableRealCoordinates G π σ)
    (O : ℕ → S → Set Sphere) (ε : ℕ → ℝ) where
  radius : ℝ
  radius_pos : 0 < radius
  plane : ℕ → Set ℂ
  plane_open : ∀ n, IsOpen (plane n)
  plane_connected : ∀ n, IsConnected (plane n)
  plane_monotone : Monotone plane
  cores : ℕ → Set Sphere
  core_compact : ∀ n, IsCompact (cores n)
  core_source : ∀ n, cores n ⊆ G
  plane_core : ∀ n, ((↑) : ℂ → Sphere) '' plane n ∪ {OnePoint.infty} ⊆ cores n
  exhausts : ((↑) : ℂ → Sphere) '' (⋃ n, plane n) ∪ {OnePoint.infty} = G
  exterior_core : ∀ n, ((((↑) : ℂ → Sphere) '' ball 0 radius)ᶜ) ⊆ cores n
  exterior_plane : {z : ℂ | 2 * radius ≤ ‖z‖} ⊆ plane 0
  flags : ℕ → Set S
  flags_finite : ∀ n, (flags n).Finite
  flags_monotone : Monotone flags
  stages : ∀ n, d.Stage n (flags n) (O n) (realChartDomain (cores n)) (ε n)
  indices_nonempty : ∀ n, Nonempty S → (stages n).indices.Nonempty
  marks : ∀ s, ∀ᶠ n in atTop, s ∈ (stages n).indices

theorem exists_real_model_exhaustion
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G)
    {π : Sphere → Sphere} (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    {S : Type*} [Countable S] {σ : S → Sphere} (d : CountableRealCoordinates G π σ)
    (hcompat : d.NaturalCompatibility)
    (O : ℕ → S → Set Sphere) (hO : ∀ n s, O n s ∈ 𝓝 (σ s))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) : Nonempty (RealModelExhaustion d O ε) := by
  obtain ⟨R, D, K, hR, hDo, hDc, hDm, hKdef, hK, hDK, hcover, hext, _⟩ :=
    exists_sphere_connected_core_exhaustion hG hconn hinf
  obtain ⟨Flag, hfin, hmono, hne, M, hmarks⟩ := exists_countable_real_transfer
    hsard hsch hcompact hfinite hG hinf hπ hclosed hsurj hr hTD d hcompat
    (fun n => realChartDomain (K n))
    (fun n => isClosed_realChartDomain (hK n).1.isClosed)
    (fun n => preimage_mono (hK n).2) O hO ε hε
  have hplane (n : ℕ) : ((↑) : ℂ → Sphere) '' D n ∪ {OnePoint.infty} ⊆ K n :=
    (hDK n).trans interior_subset
  refine ⟨{
    radius := 2 * R
    radius_pos := mul_pos (by norm_num) hR
    plane := D
    plane_open := hDo
    plane_connected := hDc
    plane_monotone := hDm
    cores := K
    core_compact := fun n => (hK n).1
    core_source := fun n => (hK n).2
    plane_core := hplane
    exhausts := ?_
    exterior_core := ?_
    exterior_plane := ?_
    flags := Flag
    flags_finite := hfin
    flags_monotone := hmono
    stages := M
    indices_nonempty := fun n h => (hne n h).mono (M n).flags
    marks := hmarks }⟩
  · simpa only [image_iUnion, iUnion_union, iUnion_const] using hcover
  · intro n p hp
    apply hplane n
    cases p using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe z =>
      refine Or.inl ⟨z, hDm (Nat.zero_le n) (hext ?_), rfl⟩
      change 2 * R ≤ ‖z‖
      simpa only [mem_compl_iff, OnePoint.coe_injective.mem_set_image,
        mem_ball, dist_zero_right, not_lt] using hp
  · intro z hz
    apply hext
    dsimp only [mem_ofPred_eq] at hz ⊢
    linarith

namespace RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

theorem core_model (n : ℕ) : M.cores n ⊆ openCompletedRegion (M.stages n).terminals.H := by
  intro p hp
  apply (M.stages n).prescribed_core_model
  cases p using OnePoint.rec with
  | infty => exact infty_mem_sphericalCore _
  | coe z => simpa only [coe_mem_sphericalCore, realChartDomain, mem_preimage,
      ContinuousLinearEquiv.symm_apply_apply] using hp

theorem core_conformal (n : ℕ) : IsConformalOn (M.stages n).forward (M.cores n) := by
  apply (M.stages n).prescribed_core_conformal.mono
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact infty_mem_sphericalCore _
  | coe z => simpa only [coe_mem_sphericalCore, realChartDomain, mem_preimage,
      ContinuousLinearEquiv.symm_apply_apply] using hp

theorem exists_conformal_limit
    (harea : ExteriorCoefficientAreaTheorem) (hmontel : MontelExhaustion)
    (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
        finiteCoord ((M.stages (s n)).forward (z : Sphere))) F
        atTop (((↑) : ℂ → Sphere) ⁻¹' G) ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G) := by
  obtain ⟨s, F, hs, hlim, hn, he⟩ := exists_conformal_limit_of_sphere_models
    harea hmontel hhurwitz hzero (fun n => (M.stages n).forward)
    (fun n => (M.stages n).inverse) (fun n => openCompletedRegion (M.stages n).terminals.H)
    (fun n => (M.stages n).domain) (fun n => (M.stages n).equivalence)
    (fun n => (M.stages n).circle_domain.1) M.plane_open M.plane_connected M.plane_monotone
    (fun n z hz => M.core_model n (M.plane_core n (Or.inl ⟨z, hz, rfl⟩)))
    (fun n => (M.core_conformal n).mono (fun _ hp => M.plane_core n (Or.inl hp)))
    M.radius_pos (fun n => (M.exterior_core n).trans (M.core_model n))
    (fun n => (M.core_conformal n).mono
      ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.exterior_core n)))
    (fun n => (M.stages n).principal) M.exterior_plane
  rw [M.exhausts] at he
  have hchart : ((↑) : ℂ → Sphere) ⁻¹' G = ⋃ n, M.plane n := by
    conv_lhs => rw [← M.exhausts]
    ext z
    simp
  exact ⟨s, F, hs, hchart ▸ hlim, hn, he⟩

end RealModelExhaustion

end CircleDomainRigidity.FiniteTransfer

end

end OAI
