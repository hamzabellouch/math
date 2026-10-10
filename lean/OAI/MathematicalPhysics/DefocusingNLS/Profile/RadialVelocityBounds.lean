import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDirichletEquation

namespace OAI

/-! The nonsingular amplitude-to-velocity formula and its inner-ball potential bounds. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem radialAverage_const (c r : ℝ) : radialAverage (fun _ => c) r=c/12 := by
  simp only [radialAverage,intervalIntegral.integral_const_mul,integral_pow]
  norm_num
  ring

theorem radialAverage_mono (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (r : ℝ) (hr : 0 ≤ r) (hfg : ∀ t ∈ Icc 0 r, f t ≤ g t) :
    radialAverage f r ≤ radialAverage g r := by
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (((hf.comp (continuous_const.mul continuous_id)).mul
      (continuous_id.pow 11)).intervalIntegrable 0 1)
    (((hg.comp (continuous_const.mul continuous_id)).mul
      (continuous_id.pow 11)).intervalIntegrable 0 1)
  intro s hs
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hs.1 11)
  exact hfg _ ⟨mul_nonneg hr hs.1,mul_le_of_le_one_right hr hs.2⟩

noncomputable def radialVelocityRatio (c : ℝ) (A : ℝ → ℝ) (r : ℝ) : ℝ :=
  c*radialAverage (fun t => (A t)^2) r/(A r)^2

noncomputable def radialAmplitudePotential (c b : ℝ) (A : ℝ → ℝ) (r : ℝ) : ℝ :=
  b+r^2/16-r^2*(radialVelocityRatio c A r)^2/4

theorem radialVelocityRatio_bounds (c R : ℝ) (hc : c ∈ Icc (599/100 : ℝ) 6)
    (A : ℝ → ℝ) (hA : Continuous A)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc 0 R) :
    radialVelocityRatio c A r ∈ Icc (49/100 : ℝ) (51/100) := by
  have hsq : (999/1000 : ℝ)^2 ≤ (A r)^2 := by
    nlinarith [(hAI r hr).1]
  have hsq1 : (A r)^2 ≤ 1 := by
    have hi := hAI r hr
    exact pow_le_one₀ (le_trans (by norm_num) hi.1) hi.2
  have hpos : 0 < (A r)^2 := by nlinarith
  have hl := radialAverage_mono (fun _ => (999/1000 : ℝ)^2) (fun t => (A t)^2)
    continuous_const (hA.pow 2) r hr.1 (by
      intro t ht
      have hi := (hAI t ⟨ht.1,ht.2.trans hr.2⟩).1
      nlinarith)
  have hu := radialAverage_mono (fun t => (A t)^2) (fun _ => (1 : ℝ))
    (hA.pow 2) continuous_const r hr.1 (by
      intro t ht
      have hi := hAI t ⟨ht.1,ht.2.trans hr.2⟩
      nlinarith [hi.1,hi.2])
  rw [radialAverage_const] at hl hu
  have ha0 : 0 ≤ radialAverage (fun t => (A t)^2) r := by linarith
  have hnlo : (599/100 : ℝ)*((999/1000 : ℝ)^2/12) ≤
      c*radialAverage (fun t => (A t)^2) r :=
    mul_le_mul hc.1 hl (by positivity) (by linarith [hc.1])
  have hnhi : c*radialAverage (fun t => (A t)^2) r ≤ (6 : ℝ)*(1/12) :=
    mul_le_mul hc.2 hu ha0 (by norm_num)
  constructor
  · apply (le_div_iff₀ hpos).2
    nlinarith
  · apply (div_le_iff₀ hpos).2
    nlinarith

theorem radialAmplitudePotential_bounds (c b R : ℝ)
    (hc : c ∈ Icc (599/100 : ℝ) 6) (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (hR : R^2 ≤ 11) (A : ℝ → ℝ) (hA : Continuous A)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (r : ℝ) (hr : r ∈ Icc 0 R) :
    radialAmplitudePotential c b A r ∈ Icc (3/10 : ℝ) (1/2) := by
  have hw := radialVelocityRatio_bounds c R hc A hA hAI r hr
  have hl : (49/100 : ℝ)^2 ≤ (radialVelocityRatio c A r)^2 := by nlinarith [hw.1]
  have hu : (radialVelocityRatio c A r)^2 ≤ (51/100 : ℝ)^2 := by nlinarith [hw.1,hw.2]
  have hrR : r^2 ≤ 11 := ((sq_le_sq₀ hr.1 (hr.1.trans hr.2)).2 hr.2).trans hR
  have hp := mul_le_mul_of_nonneg_left hu (sq_nonneg r)
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg r)
  unfold radialAmplitudePotential
  constructor <;> nlinarith [hb.1,hb.2,sq_nonneg r]

end DefocusingNLS

end OAI
