import OAI.Analysis.HenonEmden.CutoffTaylor

namespace OAI

universe uE uE2 uE3 uE4 uE5

section RadialGeometry

open MeasureTheory Set Metric NormedSpace
open scoped ENNReal InnerProductSpace
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap CapWeights

def radialFactor {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z : E × E) : ℝ :=
  (inner ℝ z.1 (z.1-z.2))^2/(‖z.1‖^2*‖z.1-z.2‖^2)

def fluxFactor {E : Type uE2} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (n : ℕ) (z : E × E) : ℝ :=
  inner ℝ (z.1-z.2) (X n z.1-X n z.2)/‖z.1-z.2‖^2

lemma radialFactor_eq {E : Type uE3} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x : E} (hx : x ≠ 0) (y : E) :
    radialFactor (x,y)=directionalFactor (direction x hx) (x,y) := by
  simp only [radialFactor,directionalFactor,direction,NormedSpace.normalize,real_inner_smul_left,mul_pow,
    div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

lemma radialFactor_bounds {E : Type uE4} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (z : E × E) :
    0 ≤ radialFactor z ∧ radialFactor z ≤ 1 := by
  by_cases hx : z.1 = 0
  · simp [radialFactor,hx]
  · rw [radialFactor_eq hx]
    exact directionalFactor_bounds _ _

lemma directionalFactor_oscillation {E : Type uE5} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e ω : sphere (0:E) 1) (z : E × E) :
    |directionalFactor e z-directionalFactor ω z| ≤ 2*dist e ω := by
  have he := abs_real_inner_le_norm (e:E) (z.1-z.2)
  have hω := abs_real_inner_le_norm (ω:E) (z.1-z.2)
  simp only [LineCoordinates.norm_unit,one_mul] at he hω
  have hdiff : |inner ℝ (e:E) (z.1-z.2)-inner ℝ (ω:E) (z.1-z.2)| ≤ dist e ω*‖z.1-z.2‖ := by
    rw [← inner_sub_left]
    exact (abs_real_inner_le_norm ((e:E)-(ω:E)) (z.1-z.2)).trans_eq (by rw [Subtype.dist_eq,dist_eq_norm])
  have hsum : |inner ℝ (e:E) (z.1-z.2)+inner ℝ (ω:E) (z.1-z.2)| ≤ 2*‖z.1-z.2‖ :=
    (abs_add_le _ _).trans (by linarith)
  by_cases hz : z.1-z.2=0
  · simp only [directionalFactor,hz,inner_zero_right,norm_zero,zero_pow (by omega : 2 ≠ 0),zero_div,sub_zero,abs_zero]
    positivity
  have hs : 0 < ‖z.1-z.2‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  unfold directionalFactor
  rw [← sub_div,abs_div,abs_of_pos hs,div_le_iff₀ hs]
  calc
    _ = |inner ℝ (e:E) (z.1-z.2)-inner ℝ (ω:E) (z.1-z.2)| *
        |inner ℝ (e:E) (z.1-z.2)+inner ℝ (ω:E) (z.1-z.2)| := by rw [← abs_mul]; congr 1; ring
    _ ≤ (dist e ω*‖z.1-z.2‖)*(2*‖z.1-z.2‖) := mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)
    _ = _ := by ring

lemma weight_directional_bound {n : ℕ} (_hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ)
    (e : sphere (0:Space n) 1) (x y : Space n) :
    weight volume κ e x*directionalFactor e (x,y) ≤
      weight volume κ e x*(radialFactor (x,y)+2*κ*d x) := by
  by_cases hw : weight volume κ e x=0
  · rw [hw,zero_mul,zero_mul]
  have hx : x ≠ 0 ∧ 0 < d x := by
    by_contra hh
    exact hw (by simp [weight,dite_eq_right hh])
  have he : e ∈ ball (direction x hx.1) (κ*d x) := by
    by_contra hh
    have hzero := profile_eq_zero (mul_pos hκ hx.2) hh
    exact hw (by simp only [weight,dite_eq_left hx,normalized,hzero,zero_div,mul_zero])
  rw [radialFactor_eq hx.1]
  apply mul_le_mul_of_nonneg_left _ (weight_nonneg volume κ e x)
  have hb := (directionalFactor_oscillation e (direction x hx.1) (x,y)).trans
    (mul_le_mul_of_nonneg_left (mem_ball.mp he).le (by norm_num : (0:ℝ) ≤ 2))
  linarith [(abs_le.mp hb).2]

end HenonLaneEmden
end
end RadialGeometry

end OAI
