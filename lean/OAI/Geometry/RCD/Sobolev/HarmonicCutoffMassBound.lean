import OAI.Geometry.RCD.Sobolev.HarmonicBochnerCutoffLimit

namespace OAI

/-! # A local energy error bounds the harmonic cutoff Bochner mass -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (Q : QuadraticCheegerEnergy μ)

omit [IsFiniteMeasureOnCompacts μ] in
theorem GoodLaplacianCutoff.harmonic_source_terms_zero
    {p : X} {r C b : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hb : 2*r < b) (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hd : d =ᵐ[μ.restrict (ball p b)] fun _ => 0) :
    (∫ x, χ.weight x*(d x)^2 ∂μ)=0 ∧ weightedGamma μ Q d u χ.sobolev=0 := by
  have hout (x : X) (hx : x∉ball p b) : 2*r < dist p x := by
    have hh : b ≤ dist p x := by simpa only [mem_ball,dist_comm,not_lt] using hx
    exact hb.trans_le hh
  constructor
  · apply integral_eq_zero_of_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hd] with x hx
    change χ.weight x*(d x)^2 = (0:ℝ)
    by_cases hm : x∈ball p b
    · simp only [hx hm,zero_pow (by decide : (2:ℕ)≠0),mul_zero]
    · rw [χ.zero x (hout x hm),zero_mul]
  · apply integral_eq_zero_of_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hd,χ.representative,
      localGamma_comm μ Q u χ.sobolev,localGamma_zero_on_level μ Q χ.sobolev u 0]
      with x hx hrep hcomm hlevel
    change d x*localGamma μ Q u χ.sobolev x = (0:ℝ)
    by_cases hm : x∈ball p b
    · rw [hx hm,zero_mul]
    · rw [hcomm,hlevel (hrep.trans (χ.zero x (hout x hm))),mul_zero]

theorem GoodLaplacianCutoff.energy_error_mass_bound
    {p : X} {r C K : ℝ} (χ : GoodLaplacianCutoff μ Q p r C)
    (hr : 0 < r) (hC : 0 ≤ C) (hK : K ≤ 0)
    (u : SobolevSpace μ Q) (c : ℝ) :
    (1/2:ℝ)*weightedGamma μ Q χ.laplacian u u-K*weightedGamma μ Q χ.weight u u ≤
      (C/r^2)/2*(∫ x in closedBall p (2*r), |localGamma μ Q u u x-c| ∂μ)+
      (-K)*((∫ x in closedBall p (2*r), |localGamma μ Q u u x-c| ∂μ)+
        c*μ.real (closedBall p (2*r))) := by
  let S := closedBall p (2*r)
  let g := localGamma μ Q u u
  let e := fun x => g x-c
  let D := C/r^2
  have hD : 0 ≤ D := div_nonneg hC (sq_nonneg r)
  let : IsFiniteMeasure (μ.restrict S) :=
    ⟨by simpa only [S,Measure.restrict_apply_univ] using (isCompact_closedBall p (2*r)).measure_lt_top⟩
  have hig : IntegrableOn g S μ := (localGamma_memL1 μ Q u u).integrableOn
  have hie : IntegrableOn e S μ := hig.sub (integrable_const _)
  have hiq : IntegrableOn χ.laplacian S μ := Integrable.of_bound
    (Lp.aestronglyMeasurable χ.laplacian).restrict D (by
      simpa only [Real.norm_eq_abs] using ae_restrict_of_ae χ.laplacian_bound)
  have hqzero : ∫ x, χ.laplacian x ∂μ=0 :=
    integral_weakLaplacian_eq_zero μ Q χ.sobolev χ.laplacian χ.weak_laplacian p
      (show 0 < 2*r by positivity)
      (by
        filter_upwards [χ.representative] with x hx hdist
        exact hx.trans (χ.zero x hdist))
      (by
        filter_upwards [χ.laplacian_locality] with x hx hdist
        exact hx (Or.inr hdist))
  have hqout : ∀ᵐ x ∂μ, x∉S → χ.laplacian x=0 := by
    filter_upwards [χ.laplacian_locality] with x hx hm
    exact hx (Or.inr (by simpa only [S,mem_closedBall,dist_comm,not_le] using hm))
  have hqS : ∫ x in S, χ.laplacian x ∂μ=0 :=
    (setIntegral_eq_integral_of_ae_compl_eq_zero hqout).trans hqzero
  have heq : weightedGamma μ Q χ.laplacian u u=
      ∫ x in S, χ.laplacian x*e x ∂μ := by
    have hloc : (∫ x in S, χ.laplacian x*g x ∂μ)=∫ x, χ.laplacian x*g x ∂μ := by
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [hqout] with x hx hm
      rw [hx hm,zero_mul]
    have hip : IntegrableOn (fun x => χ.laplacian x*g x) S μ :=
      hig.bdd_mul (Lp.aestronglyMeasurable χ.laplacian).restrict
        (by simpa only [Real.norm_eq_abs] using ae_restrict_of_ae χ.laplacian_bound)
    change (∫ x, χ.laplacian x*g x ∂μ)=_
    rw [← hloc]
    dsimp only [e]
    simp_rw [mul_sub]
    rw [integral_sub hip (hiq.mul_const c),integral_mul_const,hqS,zero_mul,sub_zero]
  have hqbound : weightedGamma μ Q χ.laplacian u u ≤ D*(∫ x in S, |e x| ∂μ) := by
    rw [heq]
    apply (le_abs_self _).trans
    apply abs_integral_le_integral_abs.trans
    calc
      _ ≤ ∫ x in S, D*|e x| ∂μ := by
        apply integral_mono_ae
          (hie.bdd_mul (Lp.aestronglyMeasurable χ.laplacian).restrict
            (by simpa only [Real.norm_eq_abs] using ae_restrict_of_ae χ.laplacian_bound)).abs
          (hie.abs.const_mul D)
        filter_upwards [ae_restrict_of_ae χ.laplacian_bound] with x hx
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  have hgi : (∫ x in S, g x ∂μ) ≤ (∫ x in S, |e x| ∂μ)+c*μ.real S := by
    have hh := integral_mono hie hie.abs (fun x => le_abs_self (e x))
    rw [integral_sub hig (integrable_const c)] at hh
    simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at hh
    linarith
  have hχbound : weightedGamma μ Q χ.weight u u ≤ (∫ x in S, |e x| ∂μ)+c*μ.real S := by
    have hloc : (∫ x in S, χ.weight x*g x ∂μ)=∫ x, χ.weight x*g x ∂μ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [χ.zero x (by simpa only [S,mem_closedBall,dist_comm,not_le] using hx),zero_mul]
    change (∫ x, χ.weight x*g x ∂μ) ≤ _
    rw [← hloc]
    apply le_trans _ hgi
    apply integral_mono_ae
      (hig.bdd_mul χ.weight.continuous.aestronglyMeasurable.restrict
        (Eventually.of_forall χ.weight.norm_coe_le_norm)) hig
    filter_upwards [ae_restrict_of_ae (localGamma_self μ Q u)] with x hx
    dsimp only [g]
    rw [hx]
    exact mul_le_of_le_one_left (sq_nonneg _) (χ.bounds x).2
  have hc := mul_le_mul_of_nonneg_left hχbound (neg_nonneg.mpr hK)
  change (1/2:ℝ)*_ - K*_ ≤ D/2*(∫ x in S, |e x| ∂μ)+(-K)*_
  linarith only [hqbound,hc]

end RegularPointCoordinates

end

end OAI
