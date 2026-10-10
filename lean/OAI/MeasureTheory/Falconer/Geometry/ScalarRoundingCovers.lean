import OAI.MeasureTheory.Falconer.Estimates.ScalarRounding

namespace OAI

/-! Scalar projection covers and ball counts are stable under the actual
 half-cell rounding used by the dyadic projection theorem. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_matched_projection_cover {δ a : ℝ} (hδ : 0 < δ) (ha : |a| ≤ 1)
    (X Y : Finset ℝ) (hnear : ∀ y ∈ Y, ∃ x ∈ X, |y-x| ≤ δ/2) :
    (scalarCells δ (Y+Y.image (fun x => a*x))).card ≤
      5*(scalarCells δ (X+X.image (fun x => a*x))).card := by
  apply scalarCells_near_card_nat hδ _ _ 1
  intro z hz
  obtain ⟨y,hy,v,hv,rfl⟩ := Finset.mem_add.mp hz
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨x,hx,hyx⟩ := hnear y hy
  obtain ⟨u,hu,hwu⟩ := hnear w hw
  refine ⟨x+a*u,Finset.add_mem_add hx (Finset.mem_image.mpr ⟨u,hu,rfl⟩),?_⟩
  have hm := mul_le_mul ha hwu (abs_nonneg (w-u)) (by norm_num : (0:ℝ) ≤ 1)
  calc
    |y+a*w-(x+a*u)| = |(y-x)+a*(w-u)| := by congr 1; ring
    _ ≤ |y-x|+|a*(w-u)| := abs_add_le _ _
    _ ≤ δ/2+δ/2 := by rw [abs_mul]; linarith
    _ = (1:ℕ)*δ := by norm_num

 theorem scalar_image_ball_bound {ρ : ℝ} (X : Finset ℝ) (f : ℝ → ℝ)
    (hnear : ∀ x ∈ X, |f x-x| ≤ ρ) (u r : ℝ) :
    scalarBallMass (X.image f) u r ≤ scalarBallMass X u (r+ρ) := by
  have hsub : (X.image f).filter (fun y => |y-u| ≤ r) ⊆
      (X.filter (fun x => |x-u| ≤ r+ρ)).image f := by
    intro y hy
    obtain ⟨hyX,hyB⟩ := Finset.mem_filter.mp hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hyX
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := abs_sub_le x (f x) u
    have he := hnear x hx
    rw [abs_sub_comm x (f x)] at hh
    linarith
  unfold scalarBallMass
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_image_le (s :=
    X.filter (fun x => |x-u| ≤ r+ρ)))

end Falconer

end OAI
