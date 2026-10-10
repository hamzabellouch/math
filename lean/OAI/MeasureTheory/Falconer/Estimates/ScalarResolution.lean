import OAI.MeasureTheory.Falconer.Geometry.ScalarRoundingBalls

namespace OAI

/-! Comparing scalar covering and ball counts at two nearby resolutions. -/
namespace Falconer

 theorem scalar_cells_resolution {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 < ρ)
    (m : ℕ) (hscale : ρ ≤ (m:ℝ)*δ) (X : Finset ℝ) :
    (scalarCells δ X).card ≤ (2*m+3)*(scalarCells ρ X).card := by
  classical
  let q : ℝ → ℤ := fun x => ⌊x/ρ⌋
  let g := Function.invFunOn q (X : Set ℝ)
  let F := (scalarCells ρ X).image g
  have hnear : ∀ x ∈ X, ∃ y ∈ F, |x-y| ≤ (m:ℝ)*δ := by
    intro x hx
    have hrep := Function.invFunOn_pos (f := q) (s := (X : Set ℝ)) ⟨x,hx,rfl⟩
    have hd : |x-g (q x)| < ρ := same_scalar_cell_dist_lt hρ hrep.2.symm
    exact ⟨g (q x),Finset.mem_image.mpr ⟨q x,Finset.mem_image.mpr ⟨x,hx,rfl⟩,rfl⟩,
      hd.le.trans hscale⟩
  have hh := scalarCells_near_card_nat hδ X F m hnear
  have hc : (scalarCells δ F).card ≤ (scalarCells ρ X).card :=
    Finset.card_image_le.trans Finset.card_image_le
  exact hh.trans (Nat.mul_le_mul_left _ hc)

 theorem scalar_refined_ball_bound {δ ρ C K s : ℝ} (hδ : 0 < δ) (hρ1 : ρ ≤ 1)
    (hC : 1 ≤ C) (hscale : ρ ≤ C*δ) (hK : 0 ≤ K) (hs : 0 ≤ s) (X : Finset ℝ)
    (hball : ∀ u r : ℝ, ρ ≤ r → r ≤ 1 → scalarBallMass X u r ≤ K*r^s*(X.card:ℝ)) :
    ∀ u r : ℝ, δ ≤ r → r ≤ 1 → scalarBallMass X u r ≤
      (C^s*K)*r^s*(X.card:ℝ) := by
  intro u r hr hr1
  have hr0 : 0 < r := hδ.trans_le hr
  have hb := hball u (max r ρ) (le_max_right _ _) (max_le hr1 hρ1)
  have hm := scalarBallMass_radius_mono X u (le_max_left r ρ)
  have hmax : max r ρ ≤ C*r := by
    apply max_le
    · nlinarith
    · exact hscale.trans (mul_le_mul_of_nonneg_left hr (by linarith))
  have hp := Real.rpow_le_rpow (le_trans hr0.le (le_max_left _ _)) hmax hs
  rw [Real.mul_rpow (by linarith : 0 ≤ C) hr0.le] at hp
  have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg hK (Nat.cast_nonneg X.card))
  nlinarith

end Falconer

end OAI
