import OAI.MeasureTheory.Falconer.Fourier.SpatialFourierSeparation
import OAI.MeasureTheory.Falconer.Shells.HighShellSubpower

namespace OAI

namespace PlanarFalconer

noncomputable def spatialLeibnizCost (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    (j : ℕ) (A : ℕ → ℝ) (N q a t : ℕ) : ℝ :=
  spatialFourierCost δ L hδ hL j *
    (((inverseLeibnizTerms j (pairMaskIndices (policyDescriptorList A N q a t))).map
      (fun b => ‖b.1‖)).sum * (2:ℝ)^j)

theorem uniform_spatialLeibniz_subpower (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    {eps : ℝ} (heps : 0 < eps) (j : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : ℕ → ℝ) (q a t : ℕ), 0 < q →
      spatialLeibnizCost δ L hδ hL j A N q a t ≤ ((2:ℝ)^N)^eps := by
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) (spatialFourierCost δ L hδ hL j)
  obtain ⟨N₂,h₂⟩ := uniform_minimal_inverseLeibniz_subpower (half_pos heps) j
  refine ⟨max N₁ N₂,?_⟩
  intro N hN A q a t hq
  unfold spatialLeibnizCost
  calc
    _ ≤ spatialFourierCost δ L hδ hL j * ((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_left (h₂ N ((le_max_right _ _).trans hN) A q a t hq)
        (spatialFourierCost_nonneg δ L hδ hL j)
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_right (h₁ N ((le_max_left _ _).trans hN)) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem uniform_spatialLeibniz_sum_subpower (δ L : ℝ) (hδ : 0 < δ) (hL : 0 < L)
    {eps : ℝ} (heps : 0 < eps) (n : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (A : ℕ → ℝ) (q a t : ℕ), 0 < q →
      (∑ j ∈ Finset.range (n+1), spatialLeibnizCost δ L hδ hL j A N q a t) ≤
        ((2:ℝ)^N)^eps := by
  classical
  choose K hK using (fun j => uniform_spatialLeibniz_subpower δ L hδ hL (half_pos heps) j)
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos heps) ((n:ℝ)+1)
  refine ⟨max N₁ ((Finset.range (n+1)).sup K),?_⟩
  intro N hN A q a t hq
  have hb : ∀ j ∈ Finset.range (n+1), spatialLeibnizCost δ L hδ hL j A N q a t ≤
      ((2:ℝ)^N)^(eps/2) := by
    intro j hj
    exact hK j N ((Finset.le_sup hj).trans ((le_max_right _ _).trans hN)) A q a t hq
  calc
    _ ≤ ∑ j ∈ Finset.range (n+1), ((2:ℝ)^N)^(eps/2) := Finset.sum_le_sum hb
    _ = ((n:ℝ)+1)*((2:ℝ)^N)^(eps/2) := by simp
    _ ≤ ((2:ℝ)^N)^(eps/2)*((2:ℝ)^N)^(eps/2) :=
      mul_le_mul_of_nonneg_right (h₁ N ((le_max_left _ _).trans hN)) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end PlanarFalconer

end OAI
