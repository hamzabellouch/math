import OAI.MeasureTheory.DyadicAvoidance.GridStabilityFin
import OAI.MeasureTheory.DyadicAvoidance.FiniteTableModel

namespace OAI

universe u_ι

noncomputable section
namespace Problem310.FiniteTableModel

/-- Stable geometry preserves the full dependent selector address. -/
theorem selectorAddress_eq_of_grid_stability {ι : Type u_ι} {a b : ι → ℕ}
    {M d : ℕ} (bS : Node M d → Fin M → ℕ) {x t : ℝ}
    (hx : x ∈ gridStableCenters a b) (e : ι) (P : Node M d) (i : Fin M)
    {n : ℕ} (hresolution : bS P i ≤ b e) (hindex : a e ≤ n)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    selectorAddress bS P i (x + t * ((2 : ℝ)⁻¹) ^ n) = selectorAddress bS P i x := by
  unfold selectorAddress
  rw [gridStableCenters_preserves_fin hx e hresolution hindex ht]

/-- Therefore every completion of the random tables preserves the earlier
selector evaluations at a stable center. -/
theorem selectorValue_eq_of_grid_stability {ι : Type u_ι} {a b : ι → ℕ}
    {M d : ℕ} (bS : Node M d → Fin M → ℕ) (ω : SelectorTable bS) {x t : ℝ}
    (hx : x ∈ gridStableCenters a b) (e : ι) (P : Node M d) (i : Fin M)
    {n : ℕ} (hresolution : bS P i ≤ b e) (hindex : a e ≤ n)
    (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    selectorValue bS ω P.val i (x + t * ((2 : ℝ)⁻¹) ^ n) =
      selectorValue bS ω P.val i x := by
  rw [selectorValue_valid, selectorValue_valid,
    selectorAddress_eq_of_grid_stability bS hx e P i hresolution hindex ht]

end Problem310.FiniteTableModel

end

end OAI
