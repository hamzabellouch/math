import OAI.MeasureTheory.Falconer.Geometry.PlanarScalarGrid

namespace OAI

/-! The original normalized planar ball bound survives injective grid
rounding, with the exact scale and radius losses exposed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem planarGridFloor_regular {δ σ α C t K : ℝ} (hσ : 0 < σ) (hα : 0 < α)
    (hC : 1 ≤ C) (hscale : δ ≤ C*α) (herror : 2*σ ≤ (C-1)*α)
    (ht : 0 ≤ t) (hK : 1 ≤ K) (G : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t K G)
    (hinj : Set.InjOn (planarGridFloor σ) (G:Set (Space 2))) :
    NormalizedFiniteBallBound α t (K*C^t) (G.image (planarGridFloor σ)) := by
  classical
  have hcard : (G.image (planarGridFloor σ)).card = G.card := Finset.card_image_of_injOn hinj
  intro z r hr _
  have hr0 : 0 < r := hα.trans_le hr
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hCr : δ ≤ C*r := hscale.trans (mul_le_mul_of_nonneg_left hr hC0)
  have herr : r+2*σ ≤ C*r := by
    have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ C-1 by linarith)
    nlinarith
  have hsub : (G.image (planarGridFloor σ)).filter (fun p => dist p z ≤ r) ⊆
      (G.filter (fun p => dist p z ≤ C*r)).image (planarGridFloor σ) := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := dist_triangle x (planarGridFloor σ x) z
    have he := planarGridFloor_error hσ x
    linarith
  have hc : (((G.image (planarGridFloor σ)).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((G.filter (fun p => dist p z ≤ C*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hb := normalized_ball_bound_all_radii ht hK hreg z (C*r) hCr
  rw [Real.mul_rpow hC0 hr0.le] at hb
  rw [hcard]
  exact hc.trans (by nlinarith)

end Falconer

end OAI
