import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import OAI.MathematicalPhysics.Transonic.Profile.Existence

namespace OAI

section
noncomputable section
namespace SepticProfile
open Set Filter
open scoped ContDiff Topology

structure GlobalProfile where
  beta : ℝ
  g : ℝ → ℝ
  beta_gt : 1 < beta
  beta_lt : beta*(ell+Real.sqrt ell)<3
  smooth : ContDiffOn ℝ ∞ g (Ici 0)
  range : ∀ y : ℝ, 0≤y → |y*g (y^2)|<1
  equation : ∀ y : ℝ, 0≤y →
    profileDenom ell y (y*g (y^2))*deriv (fun q => q*g (q^2)) y=
      profileNumer ell beta y (y*g (y^2))
  below : ∀ y : ℝ, 0<y → y*g (y^2)<y ∧ y*(y*g (y^2))<1
  radius_pos : 0<sonicRadius beta
  radius_lt : sonicRadius beta<1
  sonic_unique : ∀ y : ℝ, 0≤y →
    (velocityToU y (y*g (y^2))=sonicSpeed ↔ y=sonicRadius beta)
  sonic_slope : 0<deriv (fun y => velocityToU y (y*g (y^2))) (sonicRadius beta)

lemma globalProfile_of_exists (h : RelativisticProfileExists) : Nonempty GlobalProfile := by
  obtain ⟨β,g,hβ,hup,hg,hv,he,hb,hr,hr1,hu,hs⟩ := h
  exact ⟨⟨β,g,hβ,hup,hg,hv,he,hb,hr,hr1,hu,hs⟩⟩

def GlobalProfile.b (P : GlobalProfile) : ℝ := P.beta-1
def GlobalProfile.velocity (P : GlobalProfile) (y : ℝ) : ℝ := y*P.g (y^2)
def GlobalProfile.integrand (P : GlobalProfile) (y : ℝ) : ℝ :=
  P.velocity y/(1-y*P.velocity y)
def GlobalProfile.primitive (P : GlobalProfile) (y : ℝ) : ℝ :=
  ∫ q in (0:ℝ)..y, P.integrand q

def GlobalProfile.H (P : GlobalProfile) (y : ℝ) : ℝ :=
  (1/P.b)*Real.exp (P.b*P.primitive y)

lemma GlobalProfile.b_pos (P : GlobalProfile) : 0<P.b := sub_pos.mpr P.beta_gt
lemma GlobalProfile.velocity_zero (P : GlobalProfile) : P.velocity 0=0 := by simp [GlobalProfile.velocity]
lemma GlobalProfile.velocity_neg (P : GlobalProfile) (y : ℝ) : P.velocity (-y)= -P.velocity y := by
  simp [GlobalProfile.velocity]

lemma GlobalProfile.velocity_smooth (P : GlobalProfile) : ContDiff ℝ ∞ P.velocity := by
  have hg : ContDiff ℝ ∞ (fun y : ℝ => P.g (y^2)) := by
    rw [← contDiffOn_univ]
    exact P.smooth.comp (contDiff_id.pow 2).contDiffOn (fun y _ => sq_nonneg y)
  exact contDiff_id.mul hg

lemma GlobalProfile.pole_pos (P : GlobalProfile) (y : ℝ) : 0<1-y*P.velocity y := by
  rcases lt_trichotomy y 0 with hy|hy|hy
  · have h := (P.below (-y) (neg_pos.mpr hy)).2
    change (-y)*P.velocity (-y)<1 at h
    rw [P.velocity_neg] at h
    nlinarith only [h]
  · subst y
    simp
  · exact sub_pos.mpr (P.below y hy).2

lemma GlobalProfile.velocity_range (P : GlobalProfile) (y : ℝ) : |P.velocity y|<1 := by
  by_cases hy : 0≤y
  · exact P.range y hy
  · have h : |P.velocity (-y)|<1 := P.range (-y) (neg_nonneg.mpr (le_of_not_ge hy))
    simpa only [P.velocity_neg,abs_neg] using h

lemma GlobalProfile.integrand_smooth (P : GlobalProfile) : ContDiff ℝ ∞ P.integrand :=
  P.velocity_smooth.div (contDiff_const.sub (contDiff_id.mul P.velocity_smooth))
    (fun x => ne_of_gt (P.pole_pos x))

lemma GlobalProfile.primitive_derivative (P : GlobalProfile) (y : ℝ) :
    HasDerivAt P.primitive (P.integrand y) y := by
  have hc := P.integrand_smooth.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma GlobalProfile.primitive_smooth (P : GlobalProfile) : ContDiff ℝ ∞ P.primitive := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun y => (P.primitive_derivative y).differentiableAt,?_⟩
  have he : deriv P.primitive=P.integrand := funext fun y => (P.primitive_derivative y).deriv
  rw [he]
  exact P.integrand_smooth

lemma GlobalProfile.H_pos (P : GlobalProfile) (y : ℝ) : 0<P.H y :=
  mul_pos (one_div_pos.mpr P.b_pos) (Real.exp_pos _)
lemma GlobalProfile.H_smooth (P : GlobalProfile) : ContDiff ℝ ∞ P.H :=
  contDiff_const.mul (contDiff_const.mul P.primitive_smooth).exp
lemma GlobalProfile.H_derivative (P : GlobalProfile) (y : ℝ) :
    HasDerivAt P.H (P.b*P.H y*P.integrand y) y := by
  convert (((P.primitive_derivative y).const_mul P.b).exp).const_mul (1/P.b) using 1 <;>
    first | rfl | (unfold GlobalProfile.H; ring)

def GlobalProfile.A (P : GlobalProfile) (y : ℝ) : ℝ := P.b*P.H y+y*deriv P.H y
def GlobalProfile.B (P : GlobalProfile) (y : ℝ) : ℝ := deriv P.H y
def GlobalProfile.M0 (P : GlobalProfile) (y : ℝ) : ℝ := (P.A y)^2-(P.B y)^2

lemma GlobalProfile.A_eq (P : GlobalProfile) (y : ℝ) :
    P.A y=P.b*P.H y/(1-y*P.velocity y) := by
  rw [GlobalProfile.A,(P.H_derivative y).deriv,GlobalProfile.integrand]
  field_simp [ne_of_gt (P.pole_pos y)]
  ring
lemma GlobalProfile.B_eq (P : GlobalProfile) (y : ℝ) : P.B y=P.A y*P.velocity y := by
  rw [GlobalProfile.B,(P.H_derivative y).deriv,P.A_eq,GlobalProfile.integrand]
  ring
lemma GlobalProfile.A_pos (P : GlobalProfile) (y : ℝ) : 0<P.A y := by
  rw [P.A_eq]
  exact div_pos (mul_pos P.b_pos (P.H_pos y)) (P.pole_pos y)
lemma GlobalProfile.M0_eq (P : GlobalProfile) (y : ℝ) :
    P.M0 y=P.b^2*P.H y^2*(1-P.velocity y^2)/(1-y*P.velocity y)^2 := by
  rw [GlobalProfile.M0,P.B_eq,P.A_eq]
  field_simp [ne_of_gt (P.pole_pos y)]
lemma GlobalProfile.M0_pos (P : GlobalProfile) (y : ℝ) : 0<P.M0 y := by
  have hv : 0<1-(P.velocity y)^2 := by
    have hr := abs_lt.mp (P.velocity_range y)
    nlinarith only [hr.1,hr.2,sq_nonneg (P.velocity y)]
  rw [P.M0_eq]
  exact div_pos (mul_pos (mul_pos (sq_pos_of_pos P.b_pos) (sq_pos_of_pos (P.H_pos y))) hv)
    (sq_pos_of_pos (P.pole_pos y))

end SepticProfile

end
end

end OAI
