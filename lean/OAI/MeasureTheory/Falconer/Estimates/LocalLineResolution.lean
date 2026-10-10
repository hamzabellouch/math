import OAI.MeasureTheory.Falconer.Estimates.LocalCellLines

namespace OAI

/-! The local line map preserves regularity at each required coarser resolution. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localCellLine_regular_at {δ Δ ρ s K y a : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hy : |y| ≤ 1)
    (hρ : 0 < ρ) (hδρ : δ ≤ ρ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (T : Finset (Space 2)) (hT : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound ρ s (K*3^s) (T.image (localCellLine Δ y a)) := by
  intro z r hr _
  have hr0 : 0 ≤ r := hρ.le.trans hr
  let w := unlocalCellLine Δ y a z
  have hsub : (T.image (localCellLine Δ y a)).filter (fun l => dist l z ≤ r) ⊆
      (T.filter (fun l => dist l w ≤ 3*r)).image (localCellLine Δ y a) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr ⟨hm,?_⟩,rfl⟩
    have hh := unlocalCellLine_dist (a := a) hΔ.le hΔ1 hy (localCellLine Δ y a m) z
    rw [localCellLine_leftInverse hΔ y a m] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlr (by norm_num))
  rw [Finset.card_image_of_injective _ (localCellLine_injective hΔ y a)]
  calc
    _ ≤ ((T.filter (fun l => dist l w ≤ 3*r)).card:ℝ) :=
      Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
    _ ≤ K*(3*r)^s*(T.card:ℝ) := normalized_ball_bound_all_radii hs hK hT w (3*r)
      (hδρ.trans (by linarith only [hr,hr0]))
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr0]; ring

end Falconer

end OAI
