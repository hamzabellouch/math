import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryEnergyProjection

namespace OAI

/-! # Energy descent for the lazy symmetric averaging operator

The quantitative descent estimate produces almost harmonic coboundaries from
slowly decaying regular-representation energy.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset
variable {G E : Type*} [Group G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitaryCoboundary (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (g : G) : E := ρ g x - x

theorem unitaryCoboundary_isCocycle (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    IsUnitaryCocycle ρ (unitaryCoboundary ρ x) := by
  intro g h
  simp [unitaryCoboundary, map_mul, map_sub]

def unitaryGeneratorLaplacian (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) : E →ₗ[ℝ] E :=
  ∑ s ∈ S, (LinearMap.id - (ρ s).toLinearEquiv.toLinearMap)

theorem unitaryGeneratorLaplacian_apply (S : Finset G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    unitaryGeneratorLaplacian S ρ x = ∑ s ∈ S, (x - ρ s x) := by
  simp [unitaryGeneratorLaplacian]

theorem unitaryCoboundary_sum (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    (∑ s ∈ S, unitaryCoboundary ρ x s) = -unitaryGeneratorLaplacian S ρ x := by
  simp only [unitaryCoboundary, unitaryGeneratorLaplacian_apply, ← sum_neg_distrib,
    neg_sub]

theorem unitaryGeneratorLaplacian_selfAdjoint (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x y : E) :
    inner ℝ (unitaryGeneratorLaplacian S ρ x) y =
      inner ℝ x (unitaryGeneratorLaplacian S ρ y) := by
  have hi (s : G) : inner ℝ (ρ s x) y = inner ℝ x (ρ s⁻¹ y) := by
    have he : ρ s (ρ s⁻¹ y) = y := by
      change (ρ s * ρ s⁻¹) y = y
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    calc
      _ = inner ℝ (ρ s x) (ρ s (ρ s⁻¹ y)) := by rw [he]
      _ = _ := (ρ s).inner_map_map _ _
  simp only [unitaryGeneratorLaplacian_apply, sum_inner, inner_sum,
    inner_sub_left, inner_sub_right, hi]
  apply sum_bij (fun s _ => s⁻¹)
  · exact fun s hs => hS s hs
  · intro s _ t _ h
    exact inv_injective h
  · intro t ht
    exact ⟨t⁻¹, hS t ht, inv_inv t⟩
  · intro s _
    rfl

theorem unitaryCoboundaryEnergy_inner (S : Finset G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    unitaryCocycleEnergy S (unitaryCoboundary ρ x) =
      2 * inner ℝ (unitaryGeneratorLaplacian S ρ x) x := by
  simp only [unitaryCocycleEnergy, unitaryCoboundary, unitaryGeneratorLaplacian_apply,
    sum_inner, mul_sum]
  apply sum_congr rfl
  intro s _
  rw [norm_sub_sq_real, (ρ s).norm_map, inner_sub_left, real_inner_self_eq_norm_sq]
  ring

theorem unitaryCoboundaryEnergy_upper (S : Finset G)
    (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    unitaryCocycleEnergy S (unitaryCoboundary ρ x) ≤ 4 * S.card * ‖x‖ ^ 2 := by
  calc
    _ ≤ ∑ _s ∈ S, 4 * ‖x‖ ^ 2 := by
      apply sum_le_sum
      intro s _
      have hn : ‖unitaryCoboundary ρ x s‖ ≤ 2 * ‖x‖ := by
        exact (norm_sub_le _ _).trans_eq (by rw [(ρ s).norm_map]; ring)
      nlinarith [norm_nonneg (unitaryCoboundary ρ x s)]
    _ = _ := by simp; ring

def unitaryLazyStep (S : Finset G) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) : E :=
  x - (1 / (2 * S.card : ℝ)) • unitaryGeneratorLaplacian S ρ x

theorem unitaryCoboundaryEnergy_step_exact (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) (c : ℝ) :
    unitaryCocycleEnergy S (unitaryCoboundary ρ
      (x - c • unitaryGeneratorLaplacian S ρ x)) =
      unitaryCocycleEnergy S (unitaryCoboundary ρ x) -
      4 * c * ‖unitaryGeneratorLaplacian S ρ x‖ ^ 2 +
      c ^ 2 * unitaryCocycleEnergy S
        (unitaryCoboundary ρ (unitaryGeneratorLaplacian S ρ x)) := by
  simp only [unitaryCoboundaryEnergy_inner, map_sub, map_smul,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [unitaryGeneratorLaplacian_selfAdjoint S hS ρ
    (unitaryGeneratorLaplacian S ρ x) x, real_inner_self_eq_norm_sq]
  ring

theorem unitaryLazyStep_energy_descent (S : Finset G) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hne : S.Nonempty) (ρ : G →* (E ≃ₗᵢ[ℝ] E)) (x : E) :
    ‖unitaryGeneratorLaplacian S ρ x‖ ^ 2 / S.card ≤
      unitaryCocycleEnergy S (unitaryCoboundary ρ x) -
      unitaryCocycleEnergy S (unitaryCoboundary ρ (unitaryLazyStep S ρ x)) := by
  have hm : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hne)
  have he := unitaryCoboundaryEnergy_upper S ρ (unitaryGeneratorLaplacian S ρ x)
  rw [unitaryLazyStep, unitaryCoboundaryEnergy_step_exact S hS]
  have hc : 0 ≤ (1 / (2 * S.card : ℝ)) ^ 2 := sq_nonneg _
  have ht := mul_le_mul_of_nonneg_left he hc
  field_simp at ht ⊢
  nlinarith

end PolycyclicRecognition

end

end OAI
