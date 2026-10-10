import OAI.MeasureTheory.Falconer.Geometry.RoundedProjectionCoordinates

namespace OAI

/-! Compatible original, grid and analysis scales for a weakly separated
pair of projection bases. All costs are polynomial in the inverse separation. -/
namespace Falconer

 theorem planar_grid_scale_bounds {δ M a b : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : 1 ≤ M) (hab : b ≠ a) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hgap : 4/M ≤ |b-a|) :
    let σ := δ/(64*M)
    let α := δ/(64*M^2)
    let C := 128*M^2
    0 < σ ∧ σ ≤ 1/2 ∧ 0 < α ∧ σ = M*α ∧ δ = (64*M)*σ ∧ δ = (64*M^2)*α ∧
      1 ≤ C ∧ 4*σ < (δ/(4/|b-a|))/4 ∧
      (δ/(4/|b-a|))/4 ≤ C*α ∧ 2*σ ≤ (C-1)*α := by
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hd : 0 < |b-a| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hd2 : |b-a| ≤ 2 := (abs_sub b a).trans (by linarith)
  let σ := δ/(64*M)
  let α := δ/(64*M^2)
  let C := 128*M^2
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hs : σ = M*α := by dsimp [σ,α]; field_simp
  have hdσ : δ = (64*M)*σ := by dsimp [σ]; field_simp
  have hdα : δ = (64*M^2)*α := by dsimp [α]; field_simp
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  have hcoord : (δ/(4/|b-a|))/4 = δ*|b-a|/16 := by field_simp; ring
  have hgap' : 4 ≤ M*|b-a| := by
    have hh := (div_le_iff₀ hM0).1 hgap
    nlinarith
  have hσ1 : σ ≤ 1/2 := by nlinarith [hdσ]
  have hsmall : 4*σ < (δ/(4/|b-a|))/4 := by
    rw [hcoord,hdσ]
    have hh := mul_le_mul_of_nonneg_right hgap' hσ.le
    nlinarith
  have hscale : (δ/(4/|b-a|))/4 ≤ C*α := by
    rw [hcoord]
    have hh := mul_le_mul_of_nonneg_left hd2 hδ.le
    change δ*|b-a|/16 ≤ (128*M^2)*α
    nlinarith [hdα]
  have herr : 2*σ ≤ (C-1)*α := by
    rw [hs]
    have hh : 2*M ≤ C-1 := by dsimp [C]; nlinarith
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh hα.le
  exact ⟨hσ,hσ1,hα,hs,hdσ,hdα,hC,hsmall,hscale,herr⟩

 theorem planar_analysis_dyadic (n l : ℕ) :
    (1/2:ℝ)^n/(64*((2:ℝ)^(l+2))^2) = (1/2:ℝ)^(n+2*l+10) := by
  have hp : ((2:ℝ)^l)^2 = (4:ℝ)^l := by
    rw [← pow_mul,Nat.mul_comm l 2,pow_mul]
    norm_num
  simp only [div_pow,one_pow,pow_add,pow_mul]
  norm_num
  field_simp
  rw [hp]
  ring

end Falconer

end OAI
