import OAI.MeasureTheory.Falconer.Fourier.RootNormalizedKernel
import OAI.MeasureTheory.Falconer.Estimates.RootCoefficientSubpower
import OAI.MeasureTheory.Falconer.Fourier.SpatialFourierSeparation

namespace OAI

namespace PlanarFalconer

theorem rootAbsorbedCoefficient_norm (d e : RootEndpointData) (N j : ℕ) {sig : ℝ}
    (hsig : 0 ≤ sig)
    (hL₁ : ∀ b ∈ d.S, descriptorLength b ≤ N/2)
    (hL₂ : ∀ b ∈ e.S, descriptorLength b ≤ N/2)
    {b : ℂ × (RootMaskIndex → ℕ)} (hb : b ∈ inverseLeibnizTerms j (rootMaskIndices d e)) :
    ‖rootAbsorbedCoefficient d e N sig j b‖ ≤ ‖b.1‖ := by
  have hh := root_assignment_scale_absorbed d e N j hsig hL₁ hL₂ hb
  rw [rootAbsorbedCoefficient,sub_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hh.1]
  exact (mul_le_mul_of_nonneg_left hh.2 (norm_nonneg _)).trans_eq (mul_one _)

noncomputable def rootSpatialLeibnizCost (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (d e : RootEndpointData) (j : ℕ) : ℝ :=
  spatialFourierCost δ L hδ hL j *
    (((inverseLeibnizTerms j (rootMaskIndices d e)).map (fun b => ‖b.1‖)).sum * (2:ℝ)^j)

theorem uniform_root_spatialLeibniz_subpower (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    {eps : ℝ} (heps : 0 < eps) (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    rootSpatialLeibnizCost δ L hδ hL d e j ≤ ((2:ℝ)^N)^eps := by
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) (spatialFourierCost δ L hδ hL j)
  obtain ⟨N₂,h₂⟩ := uniform_root_inverseLeibniz_subpower (half_pos heps) j
  refine ⟨max N₁ N₂,?_⟩
  intro N hN d e hd he
  unfold rootSpatialLeibnizCost
  calc
    _ ≤ spatialFourierCost δ L hδ hL j * ((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_left (h₂ N ((le_max_right _ _).trans hN) d e hd he)
        (spatialFourierCost_nonneg δ L hδ hL j)
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_right (h₁ N ((le_max_left _ _).trans hN)) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem uniform_root_spatialLeibniz_sum_subpower (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    {eps : ℝ} (heps : 0 < eps) (n : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ d e : RootEndpointData,
    d.S.card ≤ (N+1)^3+1 → e.S.card ≤ (N+1)^3+1 →
    (∑ j ∈ Finset.range (n+1), rootSpatialLeibnizCost δ L hδ hL d e j) ≤ ((2:ℝ)^N)^eps := by
  classical
  choose K hK using (fun j => uniform_root_spatialLeibniz_subpower δ L hδ hL (half_pos heps) j)
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) ((n:ℝ)+1)
  refine ⟨max N₁ ((Finset.range (n+1)).sup K),?_⟩
  intro N hN d e hd he
  have hb : ∀ j ∈ Finset.range (n+1), rootSpatialLeibnizCost δ L hδ hL d e j ≤ ((2:ℝ)^N)^(eps/2) := by
    intro j hj
    exact hK j N ((Finset.le_sup hj).trans ((le_max_right _ _).trans hN)) d e hd he
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((2:ℝ)^N)^(eps/2) := Finset.sum_le_sum hb
    _ = ((n:ℝ)+1)*((2:ℝ)^N)^(eps/2) := by simp
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_right (h₁ N ((le_max_left _ _).trans hN)) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end PlanarFalconer

end OAI
