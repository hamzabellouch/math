import OAI.Analysis.CircleDomains.Modulus.NormalizedMarkedModels

namespace OAI

/-!
# Every fixed compact core is eventually retained

The plane domains exhaust the source, and every finite model contains a
fixed neighborhood of infinity. These two facts give eventual retention
of any compact sphere core; no extra exhaustion hypothesis is required.
-/

open Set Function Filter Metric
open scoped Topology

namespace CircleDomainRigidity

theorem eventually_compact_subset_model
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n)) (hmono : Monotone D)
    {Q : ℕ → Set Sphere} (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    {R : ℝ} (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ Q n)
    {K : Set Sphere} (hK : IsCompact K)
    (hKG : K ⊆ ((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty}) :
    ∀ᶠ n in atTop, K ⊆ Q n := by
  let S : Set ℂ := (((↑) : ℂ → Sphere) ⁻¹' K) ∩ closedBall 0 R
  have hS : IsCompact S := (isCompact_closedBall (0 : ℂ) R).inter_left
    (hK.isClosed.preimage OnePoint.continuous_coe)
  have hSD : S ⊆ ⋃ n, D n := by
    intro z hz
    rcases hKG hz.1 with hzD | hzi
    · exact OnePoint.coe_injective.mem_set_image.mp hzD
    · exact (OnePoint.coe_ne_infty z hzi).elim
  obtain ⟨m, hm⟩ := hS.elim_directed_cover D hD hSD hmono.directed_le
  filter_upwards [eventually_ge_atTop m] with n hn
  intro x hx
  cases x using OnePoint.rec with
  | infty => exact hsource n (by simp)
  | coe z =>
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · exact hDQ n z (hmono hn (hm ⟨hx, hz⟩))
    · apply hsource n
      rintro ⟨w, hw, he⟩
      have hwz : w = z := OnePoint.coe_injective he
      exact hz (hwz ▸ ball_subset_closedBall hw)

end CircleDomainRigidity

end OAI
