import OAI.MathematicalPhysics.Transonic.Core

namespace OAI

section
noncomputable section
namespace SepticProfile.ShootingParameters

lemma d_e_monotone {x y : ℝ} (hx : x∈Set.Icc leftEnd rightEnd)
    (hy : y∈Set.Icc leftEnd rightEnd) (hxy : x≤y) : d x/e x≤d y/e y := by
  rw [div_le_div_iff₀ (e_pos hx) (e_pos hy)]
  have hrx := rough_bounds hx
  have hry := rough_bounds hy
  have hprod : 0≤x*y := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hp : 0≤(y-x)*(729*x*y-81*(x+y)+198) := mul_nonneg (by linarith) (by nlinarith)
  have hid : d y*e x-d x*e y=(y-x)*(729*x*y-81*(x+y)+198) := by
    dsimp [d,e];ring
  nlinarith

lemma sigma_monotone : MonotoneOn sigma (Set.Icc leftEnd rightEnd) := by
  intro x hx y hy hxy
  have hh := d_e_monotone hx hy hxy
  have hx0 := div_pos (d_pos hx) (e_pos hx)
  have hy0 := div_pos (d_pos hy) (e_pos hy)
  have hs : (d x/e x)^2≤(d y/e y)^2 := by nlinarith
  have hsx : sigma x=(3/5:ℝ)*(d x/e x)^2 := by dsimp [sigma];ring
  have hsy : sigma y=(3/5:ℝ)*(d y/e y)^2 := by dsimp [sigma];ring
  rw [hsx,hsy];linarith

lemma kappa_antitone : AntitoneOn kappa (Set.Icc leftEnd rightEnd) := by
  intro x hx y hy hxy
  have hxpos := e_pos hx
  have hypos := e_pos hy
  unfold kappa
  rw [div_le_div_iff₀ (by positivity : 0<2*e y) (by positivity : 0<2*e x)]
  have hrx := rough_bounds hx
  have hry := rough_bounds hy
  have hprod : 0≤x*y := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hp : 0≤(y-x)*(5103*x*y-567*(x+y)+1386) := mul_nonneg (by linarith) (by nlinarith)
  have hid : (162*x^2+45*x-49)*e y-(162*y^2+45*y-49)*e x=
      (y-x)*(5103*x*y-567*(x+y)+1386) := by dsimp [e];ring
  nlinarith

lemma slope_antitone : AntitoneOn slope (Set.Icc leftEnd rightEnd) := by
  intro x hx y hy hxy
  have hxpos := a_pos hx
  have hypos := a_pos hy
  unfold slope
  rw [div_le_div_iff₀ (by positivity : 0<3*a y) (by positivity : 0<3*a x)]
  have hrx := rough_bounds hx
  have hry := rough_bounds hy
  have hprod := mul_le_mul_of_nonneg_right (show -x≤71/100 by linarith) (show 0≤-y by linarith)
  have hp : 0≤(y-x)*(-243*x*y-162*(x+y)-45) := mul_nonneg (by linarith) (by nlinarith)
  have hid : e x*a y-e y*a x=(y-x)*(-243*x*y-162*(x+y)-45) := by dsimp [e,a];ring
  nlinarith

lemma ratio_monotone : MonotoneOn ratio (Set.Icc leftEnd rightEnd) := by
  intro x hx y hy hxy
  unfold ratio
  rw [div_le_div_iff₀ (k_pos hx) (k_pos hy)]
  have hrx := rough_bounds hx
  have hry := rough_bounds hy
  have hprod : 0≤x*y := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hp : 0≤(y-x)*(4374*x*y-8991*(x+y)+810) := mul_nonneg (by linarith) (by nlinarith)
  have hid : 9*a y*k x-9*a x*k y=(y-x)*(4374*x*y-8991*(x+y)+810) := by dsimp [a,k];ring
  nlinarith

lemma beta_monotone : MonotoneOn beta (Set.Icc leftEnd rightEnd) := by
  intro x hx y hy hxy
  have hxpos := d_pos hx
  have hypos := d_pos hy
  unfold beta
  rw [div_le_div_iff₀ (by positivity : 0<2*d x) (by positivity : 0<2*d y)]
  have hrx := rough_bounds hx
  have hry := rough_bounds hy
  have hprod : 0≤x*y := mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
  have hp : 0≤(y-x)*(6561*x*y-729*(x+y)+1782) := mul_nonneg (by linarith) (by nlinarith)
  have hid : 9*(1-9*y)*d x-9*(1-9*x)*d y=(y-x)*(6561*x*y-729*(x+y)+1782) := by dsimp [d];ring
  nlinarith

end SepticProfile.ShootingParameters

end
end

end OAI
