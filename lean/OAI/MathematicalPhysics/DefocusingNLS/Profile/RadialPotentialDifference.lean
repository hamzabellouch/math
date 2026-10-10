import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVelocityBounds
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDirichletLinearity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialVolterraCalculus

namespace OAI

/-! Quantitative dependence of the actual inner potential on its amplitude. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radialAverage_sub (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (r : ℝ) :
    radialAverage (f-g) r=radialAverage f r-radialAverage g r := by
  unfold radialAverage
  simp only [Pi.sub_apply,sub_mul]
  apply intervalIntegral.integral_sub
  · exact ((hf.comp (continuous_const.mul continuous_id)).mul
      (continuous_id.pow 11)).intervalIntegrable 0 1
  · exact ((hg.comp (continuous_const.mul continuous_id)).mul
      (continuous_id.pow 11)).intervalIntegrable 0 1

theorem radial_unit_square_difference (x y D : ℝ) (hD : 0 ≤ D)
    (hx : x ∈ Icc (999/1000 : ℝ) 1) (hy : y ∈ Icc (999/1000 : ℝ) 1)
    (hxy : |x-y| ≤ D) : |x^2-y^2| ≤ 2*D := by
  have he : x^2-y^2=(x-y)*(x+y) := by ring
  rw [he,abs_mul,abs_of_nonneg (by linarith [hx.1,hy.1] : 0 ≤ x+y)]
  have h := mul_le_mul hxy (by linarith [hx.2,hy.2] : x+y ≤ 2)
    (by linarith [hx.1,hy.1] : 0 ≤ x+y) hD
  linarith

theorem radialAverage_square_difference (R D : ℝ) (hD : 0 ≤ D) (A B : ℝ → ℝ)
    (hA : Continuous A) (hB : Continuous B)
    (hAI : ∀ t ∈ Icc 0 R, A t ∈ Icc (999/1000 : ℝ) 1)
    (hBI : ∀ t ∈ Icc 0 R, B t ∈ Icc (999/1000 : ℝ) 1)
    (hAB : ∀ t ∈ Icc 0 R, |A t-B t| ≤ D) (r : ℝ) (hr : r ∈ Icc 0 R) :
    |radialAverage (fun t => (A t)^2) r-radialAverage (fun t => (B t)^2) r| ≤ D/6 := by
  let f : ℝ → ℝ := (fun t => (A t)^2)-(fun t => (B t)^2)
  have hf : Continuous f := (hA.pow 2).sub (hB.pow 2)
  have hfb : ∀ t ∈ Icc 0 r, |f t| ≤ 2*D := by
    intro t ht
    have htR : t ∈ Icc 0 R := ⟨ht.1,ht.2.trans hr.2⟩
    exact radial_unit_square_difference (A t) (B t) D hD (hAI t htR) (hBI t htR) (hAB t htR)
  have hu := radialAverage_mono f (fun _ => 2*D) hf continuous_const r hr.1
    (fun t ht => (le_abs_self (f t)).trans (hfb t ht))
  have hl := radialAverage_mono (fun _ => -(2*D)) f continuous_const hf r hr.1
    (fun t ht => (abs_le.1 (hfb t ht)).1)
  rw [radialAverage_const] at hu hl
  have he : radialAverage f r=radialAverage (fun t => (A t)^2) r-
      radialAverage (fun t => (B t)^2) r := radialAverage_sub _ _ (hA.pow 2) (hB.pow 2) r
  rw [he] at hu hl
  exact abs_le.2 ⟨by linarith,by linarith⟩

theorem radial_velocity_quotient_difference (c u v x y D : ℝ) (hD : 0 ≤ D)
    (hc : c ∈ Icc 0 6) (hv : v ∈ Icc 0 (1/12 : ℝ))
    (hx : x ∈ Icc (999/1000 : ℝ) 1) (hy : y ∈ Icc (999/1000 : ℝ) 1)
    (huv : |u-v| ≤ D/6) (hxy : |x^2-y^2| ≤ 2*D) :
    |c*u/x^2-c*v/y^2| ≤ 3*D := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hxs : (9/10 : ℝ) ≤ x^2 := by nlinarith [hx.1]
  have hys : (9/10 : ℝ) ≤ y^2 := by nlinarith [hy.1]
  have hys1 : y^2 ≤ 1 := by nlinarith [hy.1,hy.2]
  have hden : (2/3 : ℝ) ≤ x^2*y^2 := by
    have h := mul_le_mul hxs hys (by norm_num : (0 : ℝ) ≤ 9/10) (sq_nonneg x)
    nlinarith
  have h1 : |(u-v)*y^2| ≤ D/6 := by
    rw [abs_mul,abs_of_nonneg (sq_nonneg y)]
    have h := mul_le_mul huv hys1 (sq_nonneg y) (by positivity : 0 ≤ D/6)
    simpa only [mul_one] using h
  have h2 : |v*(y^2-x^2)| ≤ D/6 := by
    rw [abs_mul,abs_of_nonneg hv.1,abs_sub_comm]
    have h := mul_le_mul hv.2 hxy (abs_nonneg (x^2-y^2)) (by norm_num : (0 : ℝ) ≤ 1/12)
    linarith
  have hn : |c*((u-v)*y^2+v*(y^2-x^2))| ≤ 2*D := by
    rw [abs_mul,abs_of_nonneg hc.1]
    have hs := (abs_add_le ((u-v)*y^2) (v*(y^2-x^2))).trans (add_le_add h1 h2)
    have h := mul_le_mul hc.2 hs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 6)
    linarith
  have he : c*u/x^2-c*v/y^2=
      c*((u-v)*y^2+v*(y^2-x^2))/(x^2*y^2) := by
    field_simp
    ring
  rw [he,abs_div,abs_of_nonneg (mul_nonneg (sq_nonneg x) (sq_nonneg y))]
  apply (div_le_iff₀ (by positivity : 0 < x^2*y^2)).2
  have h := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 3*D)
  linarith

theorem radialAverage_unit_square_bounds (R : ℝ) (A : ℝ → ℝ) (hA : Continuous A)
    (hAI : ∀ t ∈ Icc 0 R, A t ∈ Icc (999/1000 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc 0 R) :
    radialAverage (fun t => (A t)^2) r ∈ Icc 0 (1/12 : ℝ) := by
  have hl := radialAverage_mono (fun _ => (0 : ℝ)) (fun t => (A t)^2)
    continuous_const (hA.pow 2) r hr.1 (fun t _ => sq_nonneg (A t))
  have hu := radialAverage_mono (fun t => (A t)^2) (fun _ => (1 : ℝ))
    (hA.pow 2) continuous_const r hr.1 (by
      intro t ht
      have hi := hAI t ⟨ht.1,ht.2.trans hr.2⟩
      nlinarith [hi.1,hi.2])
  rw [radialAverage_const] at hl hu
  constructor <;> linarith

theorem radialVelocityRatio_difference (c R D : ℝ) (hc : c ∈ Icc (599/100 : ℝ) 6)
    (hD : 0 ≤ D) (A B : ℝ → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hAI : ∀ t ∈ Icc 0 R, A t ∈ Icc (999/1000 : ℝ) 1)
    (hBI : ∀ t ∈ Icc 0 R, B t ∈ Icc (999/1000 : ℝ) 1)
    (hAB : ∀ t ∈ Icc 0 R, |A t-B t| ≤ D) (r : ℝ) (hr : r ∈ Icc 0 R) :
    |radialVelocityRatio c A r-radialVelocityRatio c B r| ≤ 3*D := by
  exact radial_velocity_quotient_difference c _ _ (A r) (B r) D hD
    ⟨by linarith [hc.1],hc.2⟩ (radialAverage_unit_square_bounds R B hB hBI r hr)
    (hAI r hr) (hBI r hr)
    (radialAverage_square_difference R D hD A B hA hB hAI hBI hAB r hr)
    (radial_unit_square_difference (A r) (B r) D hD (hAI r hr) (hBI r hr) (hAB r hr))

theorem radialAmplitudePotential_difference (c b R D : ℝ)
    (hc : c ∈ Icc (599/100 : ℝ) 6) (hR : R^2 ≤ 11) (hD : 0 ≤ D)
    (A B : ℝ → ℝ) (hA : Continuous A) (hB : Continuous B)
    (hAI : ∀ t ∈ Icc 0 R, A t ∈ Icc (999/1000 : ℝ) 1)
    (hBI : ∀ t ∈ Icc 0 R, B t ∈ Icc (999/1000 : ℝ) 1)
    (hAB : ∀ t ∈ Icc 0 R, |A t-B t| ≤ D) (r : ℝ) (hr : r ∈ Icc 0 R) :
    |radialAmplitudePotential c b A r-radialAmplitudePotential c b B r| ≤ 10*D := by
  have hρA := radialVelocityRatio_bounds c R hc A hA hAI r hr
  have hρB := radialVelocityRatio_bounds c R hc B hB hBI r hr
  have hρ := radialVelocityRatio_difference c R D hc hD A B hA hB hAI hBI hAB r hr
  have hs : |(radialVelocityRatio c A r)^2-(radialVelocityRatio c B r)^2| ≤ (153/50 : ℝ)*D := by
    have he : (radialVelocityRatio c A r)^2-(radialVelocityRatio c B r)^2=
        (radialVelocityRatio c A r-radialVelocityRatio c B r)*
          (radialVelocityRatio c A r+radialVelocityRatio c B r) := by ring
    rw [he,abs_mul,abs_of_nonneg (by linarith [hρA.1,hρB.1] : 0 ≤ radialVelocityRatio c A r+radialVelocityRatio c B r)]
    have h := mul_le_mul hρ (by linarith [hρA.2,hρB.2] :
      radialVelocityRatio c A r+radialVelocityRatio c B r ≤ (102/100 : ℝ))
      (by linarith [hρA.1,hρB.1]) (by positivity : 0 ≤ 3*D)
    nlinarith
  have hrR : r^2 ≤ 11 := ((sq_le_sq₀ hr.1 (hr.1.trans hr.2)).2 hr.2).trans hR
  have he : radialAmplitudePotential c b A r-radialAmplitudePotential c b B r=
      r^2/4*((radialVelocityRatio c B r)^2-(radialVelocityRatio c A r)^2) := by
    unfold radialAmplitudePotential
    ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ r^2/4),abs_sub_comm]
  have h := mul_le_mul (by linarith : r^2/4 ≤ (11/4 : ℝ)) hs (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 11/4)
  nlinarith

theorem radialAmplitudePotential_congr (c b R : ℝ) (A B : ℝ → ℝ)
    (hAB : EqOn A B (Icc 0 R)) (r : ℝ) (hr : r ∈ Icc 0 R) :
    radialAmplitudePotential c b A r=radialAmplitudePotential c b B r := by
  have hav := radialAverage_congr (fun t => (A t)^2) (fun t => (B t)^2) r hr.1 (by
    intro t ht
    change (A t)^2=(B t)^2
    rw [hAB ⟨ht.1,ht.2.trans hr.2⟩])
  simp only [radialAmplitudePotential,radialVelocityRatio,hav,hAB hr]

end DefocusingNLS

end OAI
