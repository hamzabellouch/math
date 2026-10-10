import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialWeightedIntegral
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialLocalContinuity
import Mathlib.Topology.MetricSpace.Algebra

namespace OAI

/-! The actual pressure has an exact radial primitive, whose limit follows from C1 convergence. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_pressure_primitive_identity (P : RadialInnerData) (H : ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H) (r : ℝ) (hr : r ∈ Icc 0 P.R) :
    (∫ t in (0 : ℝ)..r, (H t)^P.p*t^11)=r^11*deriv H r+
      ∫ t in (0 : ℝ)..r, radialAmplitudePotential P.c P.b H t*H t*t^11 := by
  let V := radialAmplitudePotential P.c P.b H
  have hV : ContinuousOn V (Icc 0 P.R) := continuousOn_radialAmplitudePotential P.c P.b P.R H hH.1.continuous
    (fun t ht => by
      have hb := ((hH.2.2.2.2.1 t ht).1).1
      have hlo := P.lo_lower
      linarith)
  have hi₁ : IntervalIntegrable (fun t => (H t)^P.p*t^11) volume 0 r :=
    ((hH.1.continuous.pow P.p).mul (continuous_id.pow 11)).intervalIntegrable 0 r
  have hi₂ : IntervalIntegrable (fun t => V t*H t*t^11) volume 0 r :=
    ContinuousOn.intervalIntegrable_of_Icc hr.1
      ((hV.mul hH.1.continuous.continuousOn |>.mul (continuous_id.pow 11).continuousOn).mono
        (fun t ht => ⟨ht.1,ht.2.trans hr.2⟩))
  have hsplit : (∫ t in (0 : ℝ)..r, ((H t)^P.p-V t*H t)*t^11)=
      (∫ t in (0 : ℝ)..r, (H t)^P.p*t^11)-(∫ t in (0 : ℝ)..r, V t*H t*t^11) := by
    simp_rw [sub_mul]
    exact intervalIntegral.integral_sub hi₁ hi₂
  have hscale := radialAverage_scaling (fun t => (H t)^P.p-V t*H t) r
  have hd := radial_inner_integral_formula P H hH r hr
  change deriv H r=r*radialAverage (fun t => (H t)^P.p-V t*H t) r at hd
  change _=r^11*deriv H r+∫ t in (0 : ℝ)..r, V t*H t*t^11
  rw [hd]
  linear_combination -hsplit-hscale

theorem radial_uniform_product (R : ℝ) (f g : ℕ → ℝ → ℝ) (F G : ℝ → ℝ)
    (hf : TendstoUniformlyOn f F atTop (Icc 0 R))
    (hg : TendstoUniformlyOn g G atTop (Icc 0 R))
    (hF : ContinuousOn F (Icc 0 R)) (hG : ContinuousOn G (Icc 0 R)) :
    TendstoUniformlyOn (fun n r => f n r*g n r) (fun r => F r*G r) atTop (Icc 0 R) := by
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    (hf.tendstoLocallyUniformlyOn.mul₀ hg.tendstoLocallyUniformlyOn hF hG)

theorem radial_pressure_primitive_convergence (R : ℝ) (P : ℕ → RadialInnerData)
    (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (c b : ℝ) (hc : c ∈ Icc (599/100 : ℝ) 6)
    (hcT : Tendsto (fun n => (P n).c) atTop (𝓝 c))
    (hbT : Tendsto (fun n => (P n).b) atTop (𝓝 b))
    (A D : ℝ → ℝ) (hA : Continuous A) (hD : Continuous D)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (hTA : TendstoUniformlyOn H A atTop (Icc 0 R))
    (hTD : TendstoUniformlyOn (fun n => deriv (H n)) D atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n r => ∫ t in (0 : ℝ)..r, (H n t)^(P n).p*t^11)
      (fun r => r^11*D r+∫ t in (0 : ℝ)..r, radialAmplitudePotential c b A t*A t*t^11)
      atTop (Icc 0 R) := by
  have hR0 : 0 ≤ R := by have hh := (P 0).hR; rw [hR 0] at hh; linarith
  have hHI : ∀ n r, r ∈ Icc 0 R → H n r ∈ Icc (999/1000 : ℝ) 1 := by
    intro n r hr
    exact ⟨(P n).lo_lower.trans ((hH n).2.2.2.2.1 r hr).1.1,((hH n).2.2.2.2.1 r hr).1.2⟩
  have hV := radialAmplitudePotential_uniform_convergence R (by simpa only [hR 0] using (P 0).hR2)
    (fun n => (P n).c) (fun n => (P n).b) c b (fun n => (P n).hc) hc hcT hbT
    H A (fun n => (hH n).1.continuous) hA hHI hAI hTA
  have hVC : ContinuousOn (radialAmplitudePotential c b A) (Icc 0 R) :=
    continuousOn_radialAmplitudePotential c b R A hA
      (fun r hr => ne_of_gt (lt_of_lt_of_le (by norm_num) (hAI r hr).1))
  have hVnC (n : ℕ) : ContinuousOn (radialAmplitudePotential (P n).c (P n).b (H n)) (Icc 0 R) :=
    continuousOn_radialAmplitudePotential (P n).c (P n).b R (H n) (hH n).1.continuous
      (fun r hr => ne_of_gt (lt_of_lt_of_le (by norm_num) (hHI n r hr).1))
  have hprod := radial_uniform_product R _ H _ A hV hTA hVC hA.continuousOn
  have hprim := radial_weighted_integral_uniform R hR0 _ _
    (fun n => (hVnC n).mul (hH n).1.continuous.continuousOn)
    (hVC.mul hA.continuousOn) hprod
  have hpow : TendstoUniformlyOn (fun _ : ℕ => fun r : ℝ => r^11)
      (fun r : ℝ => r^11) atTop (Icc 0 R) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa only [dist_self] using hε)
  have hdprod := radial_uniform_product R _ _ _ D hpow hTD
    (continuous_id.pow 11).continuousOn hD.continuousOn
  have ht := hdprod.add hprim
  apply ht.congr
  filter_upwards [] with n r hr
  have hspec : RadialInnerOutputSpec (P n).p (P n).R (P n).lo (P n).c (P n).b (H n) (H n) := by
    simpa only [hR n] using hH n
  exact (radial_pressure_primitive_identity (P n) (H n) hspec r (by simpa only [hR n] using hr)).symm

end DefocusingNLS

end OAI
