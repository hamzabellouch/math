import OAI.MeasureTheory.DyadicAvoidance.GridStability
import OAI.MeasureTheory.DyadicAvoidance.GridSeparation

namespace OAI

universe u_ι

noncomputable section
namespace Problem310

/-- Bridge from quantitative stability to the canonical finite selector addresses. -/
theorem gridStableCenters_preserves_fin {ι : Type u_ι} {a b : ι → ℕ} {x t : ℝ}
    (hx : x ∈ gridStableCenters a b) (i : ι) {c n : ℕ}
    (hc : c ≤ b i) (hn : a i ≤ n) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    GridSeparation.dyadicKey c (x + t * ((2 : ℝ)⁻¹) ^ n) =
      GridSeparation.dyadicKey c x := by
  apply (GridSeparation.dyadicKey_eq_iff c _ _).mpr
  exact gridStableCenters_preserves hx i hc hn ht

/-- Choose the gap using only the finite number of grids, before their resolutions
are assigned. Every subsequent assignment has a periodic measurable stable set
with the same prescribed exceptional-density budget. -/
theorem exists_uniform_grid_stability {ι : Type u_ι} [Fintype ι]
    (p : ℝ) (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ ∀ b : ι → ℕ, ∃ G : Set ℝ,
      MeasurableSet G ∧ (∀ x : ℝ, x + 1 ∈ G ↔ x ∈ G) ∧
      MeasureTheory.volume (Gᶜ ∩ Set.Icc (0 : ℝ) 1) ≤ ENNReal.ofReal p ∧
      ∀ x ∈ G, ∀ i : ι, ∀ n : ℕ, b i + g + 1 ≤ n →
        ∀ t ∈ Set.Icc (1 : ℝ) 2,
          GridSeparation.dyadicKey (b i) (x + t * ((2 : ℝ)⁻¹) ^ n) =
            GridSeparation.dyadicKey (b i) x := by
  obtain ⟨g, hg, hbudget⟩ := exists_dyadic_gap_budget (Fintype.card ι) hp
  refine ⟨g, hg, fun b ↦ ?_⟩
  let a : ι → ℕ := fun i ↦ b i + g + 1
  refine ⟨gridStableCenters a b, measurableSet_gridStableCenters a b,
    gridStableCenters_add_one a b, ?_, ?_⟩
  · exact (volume_gridStableCenters_compl_gap_le a b g hg (fun i ↦ rfl)).trans
      (ENNReal.ofReal_le_ofReal hbudget.le)
  · intro x hx i n hn t ht
    exact gridStableCenters_preserves_fin hx i le_rfl hn ht

end Problem310

end

end OAI
