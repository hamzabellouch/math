import OAI.NumberTheory.TotientAsymptotic.CoordinateBandTransfer

namespace OAI

/-! A fixed bad coordinate has exponentially small mass after the exact
unit-box affine correction. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace TotientAsymptotic

theorem coordinate_grid_concentration : ∃ C c : ℝ,0<C ∧ 0<c ∧
    ∀ N : ℕ,∀ B β₀ S : ℝ,∀ β κ : Fin (N+2) → ℝ,
    ∀ i : Fin (N+2),i.val<N →
    0<B → 0<β₀ → 0<S →
    (∀ j,0<β j) → (∀ j,1 ≤ κ j) →
    (∀ j,β₀ ≤ κ j) → (∀ j k,j<k → β j*κ j ≤ κ k) →
    (99/100:ℝ)*S ≤ κ i*fordSimplexCenter N (B+prefixCubeCost (N+2)) i →
    κ i*fordSimplexCenter N (B+prefixCubeCost (N+2)) i ≤ (101/100:ℝ)*S →
    1+κ i*coordinateCubeShift (N+2) i ≤ S/100 →
    ∀ K : Finset (Fin (N+2) → ℕ),
    (∀ b∈K,∃ u∈unitGridCell b,u∈enlargedSimplex (N+2) B β₀ β ∧
      (u i<(19/20:ℝ)*S ∨ (21/20:ℝ)*S<u i)) →
    (K.card:ℝ) ≤ (∏ j,κ j)*
      (C*Real.exp (-c*(N+2-(i.val+1):ℕ)))*
      (volume (prefixRegion (N+2) (B+prefixCubeCost (N+2)) 0 0)).toReal := by
  obtain ⟨C,c,hC,hc,hconc⟩ := prefix_coordinate_concentration_unconditional
  refine ⟨C,c,hC,hc,?_⟩
  intro N B β₀ S β κ i hi hB hβ₀ hS hβ hκ htop hstep hlo hhi herr K hK
  have hB' : 0<B+prefixCubeCost (N+2) := add_pos_of_pos_of_nonneg hB
    (prefixCubeCost_nonneg _)
  have hcenter : 0<fordSimplexCenter N (B+prefixCubeCost (N+2)) i := by
    unfold fordSimplexCenter
    have hN : (0:ℝ)<N+2 := by positivity
    have hi' : (i.val+1:ℝ)<N+2 := by exact_mod_cast (show i.val+1<N+2 by omega)
    exact mul_pos (mul_pos hB' (pow_pos rho_pos _))
      (sub_pos.mpr ((div_lt_one hN).mpr hi'))
  have hgrid := coordinate_grid_volume_bound (N:=N+2) (by omega) B β₀ β κ K
    (fordCoordinateBad N (B+prefixCubeCost (N+2)) i)
    (measurableSet_fordCoordinateBad _ _ _) hβ₀ hβ hκ htop hstep (by
      intro b hb
      obtain ⟨u,hu,hsimplex,hbad⟩ := hK b hb
      refine ⟨u,hu,hsimplex,?_⟩
      intro v hv
      change (1/40:ℝ) < |((simplexScale κ v+coordinateCubeShift (N+2)) i)/
        fordSimplexCenter N (B+prefixCubeCost (N+2)) i-1|
      by_contra hn
      have hh := coordinate_cube_band_transfer hu hv hS hcenter (hκ i)
        ⟨hlo,hhi⟩ herr (le_of_not_gt hn)
      rcases hbad with hbad | hbad <;> linarith only [hh.1,hh.2,hbad])
  apply hgrid.trans
  have hprod : 0 ≤ ∏ j,κ j := Finset.prod_nonneg (fun j _ => zero_le_one.trans (hκ j))
  have hh := mul_le_mul_of_nonneg_left (hconc N _ hB' i hi) hprod
  simpa only [mul_assoc] using hh

end TotientAsymptotic

end

end OAI
