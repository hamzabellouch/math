import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeShortBounds

namespace OAI

/-! Uniform second-order Taylor remainder for the short free initial-value solution. -/

open Set MeasureTheory Filter
namespace DefocusingNLS

theorem radialFreeForcing_remainder (b l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (hwidth : u-l ≤ (1/1000 : ℝ))
    (F G : ℝ → ℂ)
    (hB : ∀ r ∈ Icc l u, ‖G r‖ ≤ (35/100 : ℝ)*(r-l) ∧
      ‖F r-1‖ ≤ (175/1000 : ℝ)*(r-l)^2) :
    ∀ r ∈ Icc l u, ‖-radialFreeCoefficient r*G r-(b : ℂ)*F r+(b : ℂ)‖ ≤ (3/1000 : ℝ) := by
  intro r hr
  have he : -radialFreeCoefficient r*G r-(b : ℂ)*F r+(b : ℂ)=
      -radialFreeCoefficient r*G r-(b : ℂ)*(F r-1) := by ring
  rw [he]
  have hn := radialFreeForcing_norm b r hb ⟨hl.trans hr.1,hr.2.trans hu⟩ (F r-1) (G r)
  have hb' := hB r hr
  have hw : r-l ≤ (1/1000 : ℝ) := by linarith [hr.2]
  have hw0 : 0 ≤ r-l := sub_nonneg.mpr hr.1
  have hs : (r-l)^2 ≤ (1/1000 : ℝ)^2 := pow_le_pow_left₀ hw0 hw 2
  nlinarith [hb'.1,hb'.2]

theorem radial_integral_affine (b : ℂ) (l r : ℝ) :
    (∫ t in l..r, b*((t-l : ℝ) : ℂ))=b/2*((r-l : ℝ) : ℂ)^2 := by
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_ofReal,
    intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => l) (continuous_id.intervalIntegrable l r)
      (continuous_const.intervalIntegrable l r),integral_id,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  push_cast
  ring

theorem radial_free_taylor (b l u : ℝ)
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000)) (hl : (3 : ℝ) ≤ l)
    (hu : u ≤ (10/3 : ℝ)) (hlu : l ≤ u) (hwidth : u-l ≤ (1/1000 : ℝ))
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hF : ∀ r ∈ Icc l u, F r=1+∫ t in l..r, G t)
    (hG : ∀ r ∈ Icc l u, G r=∫ t in l..r, -radialFreeCoefficient t*G t-(b : ℂ)*F t)
    (hB : ∀ r ∈ Icc l u, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2) :
    ∀ r ∈ Icc l u,
      ‖G r+(b : ℂ)*((r-l : ℝ) : ℂ)‖ ≤ (3/1000 : ℝ)*(r-l) ∧
      ‖F r-1+(b : ℂ)/2*((r-l : ℝ) : ℂ)^2‖ ≤ (3/2000 : ℝ)*(r-l)^2 := by
  have hs := radial_free_short_bounds b l u hb hl hu hlu hwidth F G hF hG hB
  have hRem := radialFreeForcing_remainder b l u hb hl hu hwidth F G hs
  have hfInt (r : ℝ) (hr : r ∈ Icc l u) :
      IntervalIntegrable (fun t => -radialFreeCoefficient t*G t-(b : ℂ)*F t) volume l r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1
      ((radialFreeField_continuousOn_curve b l u (by linarith) (fun t => (F t,G t))
        (hFc.prodMk hGc)).snd.mono (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  have hGe : ∀ r ∈ Icc l u, ‖G r+(b : ℂ)*((r-l : ℝ) : ℂ)‖ ≤ (3/1000 : ℝ)*(r-l) := by
    intro r hr
    have he : G r+(b : ℂ)*((r-l : ℝ) : ℂ)=
        ∫ t in l..r, (-radialFreeCoefficient t*G t-(b : ℂ)*F t)+(b : ℂ) := by
      rw [intervalIntegral.integral_add (hfInt r hr) (continuous_const.intervalIntegrable l r),
        intervalIntegral.integral_const,← hG r hr,Complex.real_smul]
      ring
    rw [he]
    exact radial_complex_integral_bound l r (3/1000) hr.1 _
      (fun t ht => hRem t ⟨ht.1,ht.2.trans hr.2⟩)
  intro r hr
  refine ⟨hGe r hr,?_⟩
  have he : F r-1+(b : ℂ)/2*((r-l : ℝ) : ℂ)^2=
      ∫ t in l..r, G t+(b : ℂ)*((t-l : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_add (f := G) (g := fun t : ℝ => (b : ℂ)*((t-l : ℝ) : ℂ)) (hGc.intervalIntegrable l r)
      ((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_id.sub continuous_const))).intervalIntegrable l r),
      radial_integral_affine]
    linear_combination hF r hr
  rw [he]
  have hi : (∫ t in l..r, (3/1000 : ℝ)*(t-l))=(3/2000 : ℝ)*(r-l)^2 := by
    rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun _ : ℝ => l)
      (continuous_id.intervalIntegrable l r) (continuous_const.intervalIntegrable l r),
      integral_id,intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [← hi]
  exact intervalIntegral.norm_integral_le_of_norm_le hr.1
    (Eventually.of_forall (fun t ht => hGe t ⟨ht.1.le,ht.2.trans hr.2⟩))
    ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable l r)

end DefocusingNLS

end OAI
