import OAI.MeasureTheory.Falconer.Incidence.FiniteLoomisWhitney
import OAI.MeasureTheory.Falconer.Geometry.IntegerRectangle
import OAI.MeasureTheory.Falconer.Geometry.TransverseGridCoordinates

namespace OAI

/-! # Counting physical tube intersections in transverse grid coordinates -/

namespace Falconer

theorem transverse_grid_tube_count (e : Space 3 ≃L[ℝ] Space 3)
    (v : Fin 3 → Space 3) (A : Fin 3 → Finset (Space 3))
    (S : Finset (ℤ × ℤ × ℤ)) {δ C : ℝ} (hδ : 0 < δ)
    (haxis : ∀ i j : Fin 3, j ≠ i → (e.symm (v i)) j = 0)
    (L : ℕ) (hL : ‖e.symm.toContinuousLinearMap‖*C+1/2 ≤ (L:ℝ))
    (hcover : ∀ i : Fin 3, ∀ z ∈ S, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (e (tripleGridPoint δ z)-a)‖ ≤ C*δ) :
    (S.card:ℝ)^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*(2*(L:ℝ)+1)^6 := by
  classical
  have hxy : (S.image (fun z => (z.1,z.2.1))).card ≤ (A 2).card*(2*L+1)^2 := by
    apply integer_rectangle_cover_card _ (A 2)
      (fun a => (e.symm a) 0/δ) (fun a => (e.symm a) 1/δ)
      (‖e.symm.toContinuousLinearMap‖*C) L hL
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,ht⟩ := hcover 2 w hw
    refine ⟨a,ha,?_,?_⟩
    · have hh := transverse_grid_coordinate e (v 2) a w 0 hδ (haxis 2 0 (by decide)) ht
      simpa [hδ.ne'] using hh
    · have hh := transverse_grid_coordinate e (v 2) a w 1 hδ (haxis 2 1 (by decide)) ht
      simpa [hδ.ne'] using hh
  have hyz : (S.image (fun z => (z.2.1,z.2.2))).card ≤ (A 0).card*(2*L+1)^2 := by
    apply integer_rectangle_cover_card _ (A 0)
      (fun a => (e.symm a) 1/δ) (fun a => (e.symm a) 2/δ)
      (‖e.symm.toContinuousLinearMap‖*C) L hL
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,ht⟩ := hcover 0 w hw
    refine ⟨a,ha,?_,?_⟩
    · have hh := transverse_grid_coordinate e (v 0) a w 1 hδ (haxis 0 1 (by decide)) ht
      simpa [hδ.ne'] using hh
    · have hh := transverse_grid_coordinate e (v 0) a w 2 hδ (haxis 0 2 (by decide)) ht
      simpa [hδ.ne'] using hh
  have hzx : (S.image (fun z => (z.2.2,z.1))).card ≤ (A 1).card*(2*L+1)^2 := by
    apply integer_rectangle_cover_card _ (A 1)
      (fun a => (e.symm a) 2/δ) (fun a => (e.symm a) 0/δ)
      (‖e.symm.toContinuousLinearMap‖*C) L hL
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨a,ha,ht⟩ := hcover 1 w hw
    refine ⟨a,ha,?_,?_⟩
    · have hh := transverse_grid_coordinate e (v 1) a w 2 hδ (haxis 1 2 (by decide)) ht
      simpa [hδ.ne'] using hh
    · have hh := transverse_grid_coordinate e (v 1) a w 0 hδ (haxis 1 0 (by decide)) ht
      simpa [hδ.ne'] using hh
  have hxy' : ((S.image (fun z => (z.1,z.2.1))).card:ℝ) ≤
      ((A 2).card:ℝ)*(2*(L:ℝ)+1)^2 := by exact_mod_cast hxy
  have hyz' : ((S.image (fun z => (z.2.1,z.2.2))).card:ℝ) ≤
      ((A 0).card:ℝ)*(2*(L:ℝ)+1)^2 := by exact_mod_cast hyz
  have hzx' : ((S.image (fun z => (z.2.2,z.1))).card:ℝ) ≤
      ((A 1).card:ℝ)*(2*(L:ℝ)+1)^2 := by exact_mod_cast hzx
  calc
    _ ≤ ((S.image (fun z => (z.1,z.2.1))).card:ℝ)*
        ((S.image (fun z => (z.2.1,z.2.2))).card:ℝ)*
        ((S.image (fun z => (z.2.2,z.1))).card:ℝ) := finite_loomis_whitney_three_arbitrary S
    _ ≤ (((A 2).card:ℝ)*(2*(L:ℝ)+1)^2)*
        (((A 0).card:ℝ)*(2*(L:ℝ)+1)^2)*
        (((A 1).card:ℝ)*(2*(L:ℝ)+1)^2) := by gcongr
    _ = _ := by ring

end Falconer

end OAI
