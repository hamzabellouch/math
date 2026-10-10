import OAI.Analysis.CircleDomains.Topology.FiniteJordanModelInput
import OAI.Analysis.CircleDomains.Topology.RealModelExhaustion

namespace OAI

/-! Enlarge the common exterior radius without changing the actual finite
models or their transferred coordinates. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}

def RealModelExhaustion.withRadius (M : RealModelExhaustion d O ε)
    (R : ℝ) (hR : M.radius ≤ R) : RealModelExhaustion d O ε where
  radius := R
  radius_pos := M.radius_pos.trans_le hR
  plane := M.plane
  plane_open := M.plane_open
  plane_connected := M.plane_connected
  plane_monotone := M.plane_monotone
  cores := M.cores
  core_compact := M.core_compact
  core_source := M.core_source
  plane_core := M.plane_core
  exhausts := M.exhausts
  exterior_core := fun n =>
    (compl_subset_compl.mpr (image_mono (ball_subset_ball hR))).trans (M.exterior_core n)
  exterior_plane := by
    intro z hz
    apply M.exterior_plane
    change 2 * M.radius ≤ ‖z‖
    exact (mul_le_mul_of_nonneg_left hR (by norm_num)).trans hz
  flags := M.flags
  flags_finite := M.flags_finite
  flags_monotone := M.flags_monotone
  stages := M.stages
  indices_nonempty := M.indices_nonempty
  marks := M.marks

theorem exists_real_model_exhaustion_large_radius
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hG : IsOpen G) (hconn : IsConnected G) (hinf : OnePoint.infty ∈ G)
    (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ)) [Countable S]
    (d : CountableRealCoordinates G π σ)
    (hcompat : d.NaturalCompatibility)
    (O : ℕ → S → Set Sphere) (hO : ∀ n s, O n s ∈ 𝓝 (σ s))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (R : ℝ) :
    ∃ M : RealModelExhaustion d O ε, R ≤ M.radius := by
  obtain ⟨M⟩ := exists_real_model_exhaustion hsard hsch hcompact hfinite
    hG hconn hinf hπ hclosed hsurj hr hTD d hcompat O hO ε hε
  exact ⟨M.withRadius (max M.radius R) (le_max_left _ _), le_max_right _ _⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
