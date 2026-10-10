import OAI.Analysis.CircleDomains.Selection.MixedCircuitRetention
import OAI.Analysis.CircleDomains.Topology.JordanBoundaryBound
import OAI.Analysis.CircleDomains.Modulus.NormalizedUniformBounds

namespace OAI

/-! The common exterior normalization bounds every retained image collar
by one fixed ball, independently of its finite terminal family. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.eventually_image_collar_bound
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (H : ℂ ≃ₜ ℂ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    (J : ℕ → ℂ ≃ₜ ℂ)
    (hJ : ∀ᶠ n in atTop,
      (M.stages n).model.forward '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n))) :
    ∀ᶠ n in atTop, closure (jordanInterior (J n)) ⊆ closedBall 0 (5 * M.real.radius) := by
  have hbound (n : ℕ) := (normalized_model_uniform_bound harea (M.real.stages n).equivalence
    (M.real.stages n).circle_domain.1 M.real.radius_pos
    ((M.real.exterior_core n).trans (M.real.core_model n))
    ((M.real.core_conformal n).mono
      ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.real.exterior_core n)))
    (M.real.stages n).principal).2
  have hK : IsCompact (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) :=
    ((isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier
      frontier_subset_closure).image OnePoint.continuous_coe
  filter_upwards [hJ, M.real.eventually_model_contains hK hG] with n hn hret
  apply jordan_closure_subset_closedBall_of_frontier (J n) (mul_pos (by norm_num) M.real.radius_pos)
  intro z hz
  have hm : (z : Sphere) ∈ (M.stages n).model.forward ''
      (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := hn.symm ▸ mem_image_of_mem _ hz
  obtain ⟨_, ⟨w, hw, rfl⟩, he⟩ := hm
  have hb := hbound n w (hret (mem_image_of_mem _ hw)) (hH w hw)
  rw [← M.same_forward n, he] at hb
  exact OnePoint.coe_injective.mem_set_image.mp hb

 theorem MixedModelExhaustion.eventually_all_image_collar_bounds
    (harea : ExteriorCoefficientAreaTheorem)
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (H : ℂ ≃ₜ ℂ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G)
    (hH : ∀ z ∈ frontier (jordanInterior H), ‖z‖ ≤ 4 * M.real.radius)
    : ∀ᶠ n in atTop, ∀ J : ℂ ≃ₜ ℂ,
      (M.stages n).model.forward '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) →
      closure (jordanInterior J) ⊆ closedBall 0 (5 * M.real.radius) := by
  have hbound (n : ℕ) := (normalized_model_uniform_bound harea (M.real.stages n).equivalence
    (M.real.stages n).circle_domain.1 M.real.radius_pos
    ((M.real.exterior_core n).trans (M.real.core_model n))
    ((M.real.core_conformal n).mono
      ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.real.exterior_core n)))
    (M.real.stages n).principal).2
  have hK : IsCompact (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) :=
    ((isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier
      frontier_subset_closure).image OnePoint.continuous_coe
  filter_upwards [M.real.eventually_model_contains hK hG] with n hret
  intro J hn
  apply jordan_closure_subset_closedBall_of_frontier J (mul_pos (by norm_num) M.real.radius_pos)
  intro z hz
  have hm : (z : Sphere) ∈ (M.stages n).model.forward ''
      (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := hn.symm ▸ mem_image_of_mem _ hz
  obtain ⟨_, ⟨w, hw, rfl⟩, he⟩ := hm
  have hb := hbound n w (hret (mem_image_of_mem _ hw)) (hH w hw)
  rw [← M.same_forward n, he] at hb
  exact OnePoint.coe_injective.mem_set_image.mp hb


end CircleDomainRigidity.FiniteTransfer

end

end OAI
