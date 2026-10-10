import OAI.MeasureTheory.Falconer.Incidence.QuarterPencilGeometry
import OAI.MeasureTheory.Falconer.Estimates.CoarsePlanarRounding

namespace OAI

/-! A fixed contraction changes the actual rounded point cover by at most
25 per original grid cell. No covering hypothesis is added. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem planarQuarter_coarse_cover {ρ : ℝ} (hρ : 0 < ρ) (P : Finset (Space 2)) :
    (((P.image planarQuarter).image (coarsePlanarRound (ρ/2))).card:ℝ) ≤
      25*((P.image (coarsePlanarRound ρ)).card:ℝ) := by
  let C := P.image (coarsePlanarRound ρ)
  let S := fun c => P.filter fun p => coarsePlanarRound ρ p = c
  let A := fun c => ((S c).image planarQuarter).image (coarsePlanarRound (ρ/2))
  have hρ' : 0 < ρ/2 := by positivity
  have hA (c : Space 2) (_hc : c ∈ C) : ((A c).card:ℝ) ≤ 25 := by
    have hwithin : ∀ z ∈ A c, dist z (planarQuarter c) ≤ 2*(ρ/2) := by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      have hpc := (Finset.mem_filter.mp hp).2
      have hd := coarsePlanarRound_near hρ p
      rw [hpc] at hd
      have hquarter : dist (planarQuarter p) (planarQuarter c) ≤ ρ/4 := by
        rw [planarQuarter_dist]
        exact div_le_div_of_nonneg_right hd (by norm_num)
      have hnear := coarsePlanarRound_near hρ' (planarQuarter p)
      rw [dist_comm] at hnear
      have htri := dist_triangle (coarsePlanarRound (ρ/2) (planarQuarter p))
        (planarQuarter p) (planarQuarter c)
      linarith
    have hh := separated_ball_card (A c) (planarQuarter c) hρ'
      (r := 2*(ρ/2)) (by positivity)
      (coarsePlanarRound_separated hρ' ((S c).image planarQuarter)) hwithin
    have he : (2*(2*(ρ/2))/(ρ/2)+1)^2 = (25:ℝ) := by field_simp; ring
    rwa [he] at hh
  have hcover : (P.image planarQuarter).image (coarsePlanarRound (ρ/2)) ⊆ C.biUnion A := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_biUnion.mpr ⟨coarsePlanarRound ρ p,Finset.mem_image_of_mem _ hp,?_⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp,rfl⟩))
  calc
    _ ≤ ((C.biUnion A).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ c ∈ C, ((A c).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, (25:ℝ) := Finset.sum_le_sum hA
    _ = _ := by simp; ring

end Falconer

end OAI
