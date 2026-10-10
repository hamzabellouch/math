import Mathlib
import OAI.Geometry.BallPacking.Energy.ResidualEnergy

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

def circlePlane (r θ : ℝ) : Plane := (r*Real.cos θ,r*Real.sin θ)

def circleTrace (u : ℂ → Phase n) (r θ : ℝ) : Phase n := realCurve u (circlePlane r θ)

lemma circlePlane_smooth (r : ℝ) : ContDiff ℝ ∞ (circlePlane r) := by
  unfold circlePlane
  fun_prop

lemma circleTrace_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    ContDiff ℝ ∞ (circleTrace u r) := (realCurve_smooth hu).comp (circlePlane_smooth r)

lemma circlePlane_hasDerivAt (r θ : ℝ) :
    HasDerivAt (circlePlane r) (planeRotation (circlePlane r θ)) θ := by
  have hh := ((Real.hasDerivAt_cos θ).const_mul r).prodMk ((Real.hasDerivAt_sin θ).const_mul r)
  change HasDerivAt (circlePlane r) (r * (-Real.sin θ),r * Real.cos θ) θ at hh
  simpa only [planeRotation,circlePlane,mul_neg] using hh

lemma circleTrace_deriv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (r θ : ℝ) :
    deriv (circleTrace u r) θ=fderiv ℝ (realCurve u) (circlePlane r θ) (planeRotation (circlePlane r θ)) := by
  exact (((realCurve_smooth hu).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt θ
    (circlePlane_hasDerivAt r θ)).deriv

lemma circleTrace_closed (u : ℂ → Phase n) (r : ℝ) : circleTrace u r Real.pi=circleTrace u r (-Real.pi) := by
  simp [circleTrace,circlePlane]

lemma plane_linear_energy_identity (L : Plane →L[ℝ] Phase n) (z : Plane) :
    stdDot n (L (planeRotation z)) (L (planeRotation z))+stdDot n (L z) (L z)=
      radiusSq z*(stdDot n (L (1,0)) (L (1,0))+stdDot n (L (0,1)) (L (0,1))) := by
  have hz : z=z.1 • ((1,0):Plane)+z.2 • ((0,1):Plane) := by ext <;> simp
  have hr : planeRotation z=(-z.2) • ((1,0):Plane)+z.1 • ((0,1):Plane) := by ext <;> simp [planeRotation]
  have hLr : L (planeRotation z)=(-z.2) • L (1,0)+z.1 • L (0,1) := by
    rw [hr,map_add,map_smul,map_smul]
  have hLz : L z=z.1 • L (1,0)+z.2 • L (0,1) := by
    conv_lhs => rw [hz,map_add,map_smul,map_smul]
  rw [hLr,hLz]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [stdDot_symm (L (0,1)) (L (1,0))]
  dsimp only [radiusSq]
  ring

lemma circleTrace_energy_le {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (r θ : ℝ) :
    stdDot n (deriv (circleTrace u r) θ) (deriv (circleTrace u r) θ)≤
      r^2*dirichletEnergy u (circlePlane r θ) := by
  rw [circleTrace_deriv hu]
  have h := plane_linear_energy_identity (fderiv ℝ (realCurve u) (circlePlane r θ)) (circlePlane r θ)
  have hr : radiusSq (circlePlane r θ)=r^2 := by
    have htr := Real.cos_sq_add_sin_sq θ
    dsimp [radiusSq,circlePlane]
    nlinarith [sq_nonneg r]
  rw [hr] at h
  change stdDot n _ _+stdDot n _ _=r^2*dirichletEnergy u (circlePlane r θ) at h
  linarith [stdDot_nonneg (fderiv ℝ (realCurve u) (circlePlane r θ) (circlePlane r θ))]

lemma circle_pullback_flux_le {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (r : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi,
      planarPullback (realCurve u) (stdOmega n) (circlePlane r θ) (planeRotation (circlePlane r θ)))≤
      ((2*Real.pi)^2+1)/2*r^2*(∫ θ in (-Real.pi)..Real.pi, dirichletEnergy u (circlePlane r θ)) := by
  have hloop := loop_symplectic_flux_le_energy (circleTrace_smooth hu r)
    (by linarith [Real.pi_pos] : -Real.pi≤Real.pi) (circleTrace_closed u r)
  have hdc : Continuous (fun θ => stdDot n (deriv (circleTrace u r) θ) (deriv (circleTrace u r) θ)) := by
    have hd := (circleTrace_smooth hu r).continuous_deriv (by simp)
    exact ((stdDot n).continuous.comp hd).clm_apply hd
  have hec : Continuous (fun θ => r^2*dirichletEnergy u (circlePlane r θ)) := continuous_const.mul
    ((dirichletEnergy_continuous hu).comp (circlePlane_smooth r).continuous)
  have hi := intervalIntegral.integral_mono (μ := volume) (by linarith [Real.pi_pos] : -Real.pi≤Real.pi)
    (hdc.intervalIntegrable _ _) (hec.intervalIntegrable _ _) (circleTrace_energy_le hu r)
  rw [intervalIntegral.integral_const_mul] at hi
  have hc : 0≤((Real.pi-(-Real.pi))^2+1)/2 := by positivity
  have hb := hloop.trans (mul_le_mul_of_nonneg_left hi hc)
  calc
    _ = (∫ θ in (-Real.pi)..Real.pi, stdOmega n (circleTrace u r θ) (deriv (circleTrace u r) θ)) := by
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only
      rw [circleTrace_deriv hu]
      rfl
    _ ≤ _ := hb
    _ = _ := by ring


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

lemma integrable_polar_pullback {f : Plane → ℝ} (hf : Integrable f) :
    IntegrableOn (fun p : Plane => p.1*f (polarCoord.symm p)) polarCoord.target := by
  have hi : IntegrableOn f (polarCoord.symm '' polarCoord.target) := hf.integrableOn
  have hp := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    polarCoord.open_target.measurableSet
    (fun p _ => (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)
    polarCoord.symm.injOn f).mp hi
  apply hp.congr_fun _ polarCoord.open_target.measurableSet
  intro p hp
  dsimp only
  rw [det_fderivPolarCoordSymm,abs_of_pos hp.1,smul_eq_mul]

lemma integral_polar_slices {f : Plane → ℝ} (hf : Integrable f) :
    (∫ z, f z)=∫ r in Ioi (0:ℝ), r*(∫ θ in (-Real.pi)..Real.pi, f (circlePlane r θ)) := by
  rw [←integral_comp_polarCoord_symm]
  have hp := integrable_polar_pullback hf
  rw [polarCoord_target,Measure.volume_eq_prod] at hp ⊢
  simp only [smul_eq_mul]
  rw [setIntegral_prod _ hp]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r _
  dsimp only [Prod.fst]
  rw [integral_const_mul,intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi),
    integral_Ioc_eq_integral_Ioo]
  rfl

lemma integrable_polar_slices {f : Plane → ℝ} (hf : Integrable f) :
    IntegrableOn (fun r => r*(∫ θ in (-Real.pi)..Real.pi, f (circlePlane r θ))) (Ioi (0:ℝ)) := by
  have hp := integrable_polar_pullback hf
  rw [polarCoord_target,Measure.volume_eq_prod,IntegrableOn,←Measure.prod_restrict] at hp
  have hi := hp.integral_prod_left
  unfold IntegrableOn
  convert hi using 1
  funext r
  dsimp only [Prod.fst]
  rw [integral_const_mul,intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi),
    integral_Ioc_eq_integral_Ioo]
  rfl


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

def angularCurveFlux (u : ℂ → Phase n) (z : Plane) : ℝ :=
  planarPullback (realCurve u) (stdOmega n) z (planeRotation z)

lemma angularCurveFlux_continuous {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    Continuous (angularCurveFlux u) :=
  (planarPullback_smooth (realCurve_smooth hu) (stdOmega n).contDiff).continuous.clm_apply
    (continuous_snd.neg.prodMk continuous_fst)

lemma radiusSq_circlePlane (r θ : ℝ) : radiusSq (circlePlane r θ)=r^2 := by
  have htr := Real.cos_sq_add_sin_sq θ
  dsimp [radiusSq,circlePlane]
  nlinarith [sq_nonneg r]

lemma integral_radial_angularFlux_le {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {k : ℝ → ℝ} (hk : Continuous k) (hkc : HasCompactSupport k)
    (hkn : ∀ s : ℝ, 0 ≤ s → 0 ≤ k s) :
    (∫ z : Plane, k (radiusSq z)*angularCurveFlux u z)≤
      ((2*Real.pi)^2+1)/2*(∫ z : Plane, k (radiusSq z)*radiusSq z*dirichletEnergy u z) := by
  have hkpc := hk.comp radiusSq_smooth.continuous
  have hkps := HasCompactSupport.comp_radiusSq hkc
  have hf : Integrable (fun z : Plane => k (radiusSq z)*angularCurveFlux u z) :=
    (hkpc.mul (angularCurveFlux_continuous hu)).integrable_of_hasCompactSupport hkps.mul_right
  have hg : Integrable (fun z : Plane => k (radiusSq z)*radiusSq z*dirichletEnergy u z) :=
    ((hkpc.mul radiusSq_smooth.continuous).mul (dirichletEnergy_continuous hu)).integrable_of_hasCompactSupport
      (hkps.mul_right.mul_right)
  rw [integral_polar_slices hf,integral_polar_slices hg,←integral_const_mul]
  apply setIntegral_mono_on (integrable_polar_slices hf)
    ((integrable_polar_slices hg).const_mul _) measurableSet_Ioi
  intro r hr
  simp_rw [radiusSq_circlePlane,intervalIntegral.integral_const_mul]
  have hn : 0≤r*k (r^2) := mul_nonneg (le_of_lt hr) (hkn _ (sq_nonneg _))
  have hb := mul_le_mul_of_nonneg_left (circle_pullback_flux_le hu r) hn
  change r*(k (r^2)*(∫ θ in (-Real.pi)..Real.pi, angularCurveFlux u (circlePlane r θ)))≤_
  dsimp only [angularCurveFlux]
  nlinarith only [hb]

lemma curveAreaDensity_continuous {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) :
    Continuous (curveAreaDensity u) := by
  have hd := ((realCurve_smooth hu).fderiv_right (m := ∞) (by simp)).continuous
  exact ((stdOmega n).continuous.comp (hd.clm_apply continuous_const)).clm_apply
    (hd.clm_apply continuous_const)

lemma standard_primitive_curl_area {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (z : Plane) :
    planarCurl (planarPullback (realCurve u) (stdOmega n)) z=2*curveAreaDensity u z := by
  rw [standard_primitive_curl hu,dirichletEnergy_eq_residual_add_area hu]
  ring

lemma radial_stokes_area_eq_flux {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    (∫ z : Plane, g (radiusSq z)*curveAreaDensity u z)=
      ∫ z : Plane, (-deriv g (radiusSq z))*angularCurveFlux u z := by
  have hβ := planarPullback_smooth (realCurve_smooth hu) (stdOmega n).contDiff
  have he : (∫ z, cutoffWedge (fun y => g (radiusSq y))
      (planarPullback (realCurve u) (stdOmega n)) z)=
      -(∫ z, g (radiusSq z)*planarCurl (planarPullback (realCurve u) (stdOmega n)) z) :=
    integral_cutoffWedge (hg.comp radiusSq_smooth) (HasCompactSupport.comp_radiusSq hgc) hβ
  simp_rw [cutoffWedge_radial_rotation hg,standard_primitive_curl_area hu] at he
  have hleft (z : Plane) : 2*deriv g (radiusSq z)*
      planarPullback (realCurve u) (stdOmega n) z (planeRotation z)=
      -2*((-deriv g (radiusSq z))*angularCurveFlux u z) := by unfold angularCurveFlux; ring
  have hright (z : Plane) : g (radiusSq z)*(2*curveAreaDensity u z)=
      2*(g (radiusSq z)*curveAreaDensity u z) := by ring
  simp_rw [hleft,hright] at he
  rw [integral_const_mul,integral_const_mul] at he
  linarith

theorem calibrated_radial_energy_bound {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {C : ℝ} (hC : 0≤C) (hcal : ∀ z, dirichletEnergy u z≤C*curveAreaDensity u z)
    {A : ℝ} (hA : 0<A) :
    (∫ z : Plane, sourceRadialCutoff A z*dirichletEnergy u z)≤
      C*(((2*Real.pi)^2+1)/2)*
        (∫ z : Plane, (-deriv (outerProfile A) (radiusSq z))*radiusSq z*dirichletEnergy u z) := by
  have hi := integral_mono (smooth_cutoff_integrable_mul hA (dirichletEnergy_continuous hu))
    ((smooth_cutoff_integrable_mul hA (curveAreaDensity_continuous hu)).const_mul C)
    (fun z => by
      have h := mul_le_mul_of_nonneg_left (hcal z) (sourceRadialCutoff_nonneg A z)
      nlinarith only [h])
  rw [integral_const_mul] at hi
  change (∫ z, sourceRadialCutoff A z*dirichletEnergy u z)≤
    C*(∫ z, outerProfile A (radiusSq z)*curveAreaDensity u z) at hi
  rw [radial_stokes_area_eq_flux hu (outerProfile_smooth A) (outerProfile_compact hA)] at hi
  have hb := integral_radial_angularFlux_le hu
    ((outerProfile_smooth A).continuous_deriv (by simp)).neg (outerProfile_compact hA).deriv.neg
    (fun s hs => neg_nonneg.mpr (outerProfile_deriv_nonpos hA hs))
  exact hi.trans (by simpa only [mul_assoc,Pi.neg_apply] using mul_le_mul_of_nonneg_left hb hC)


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian

lemma smoothTransition_deriv_zero_outside {t : ℝ} (ht : t∉Icc (0:ℝ) 1) :
    deriv Real.smoothTransition t=0 := by
  rcases (show t<0 ∨ 1<t by simpa only [mem_Icc,not_and_or,not_le] using ht) with ht | ht
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    rw [he.deriv_eq,deriv_const]
  · have he : Real.smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
      exact Real.smoothTransition.one_of_one_le hs.le
    rw [he.deriv_eq,deriv_const]

lemma smoothTransition_deriv_le_bound :
    ∃ M : ℝ, 0<M ∧ ∀ t : ℝ, deriv Real.smoothTransition t≤M := by
  have hc : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.intro isCompact_Icc (fun t ht => smoothTransition_deriv_zero_outside ht)
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv (by simp))
  refine ⟨|B|+1,by positivity,fun t => ?_⟩
  have h := hB t
  rw [Real.norm_eq_abs] at h
  linarith [le_abs_self (deriv Real.smoothTransition t),le_abs_self B]

lemma outerProfile_deriv_zero_after {A t : ℝ} (hA : 0<A) (ht : 2*A<t) :
    deriv (outerProfile A) t=0 := by
  have he : outerProfile A =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    change 2*A<s at hs
    have h : 1≤(s-A)/A := (le_div_iff₀ hA).mpr (by linarith)
    simp only [outerProfile,Real.smoothTransition.one_of_one_le h,sub_self,mul_zero]
  rw [he.deriv_eq,deriv_const]

lemma outerProfile_weight_uniform_bound :
    ∃ B : ℝ, 0<B ∧ ∀ A : ℝ, 0<A → ∀ t : ℝ, 0≤t →
      0≤(-deriv (outerProfile A) t)*t ∧ (-deriv (outerProfile A) t)*t≤B := by
  obtain ⟨M,hM,hbound⟩ := smoothTransition_deriv_le_bound
  refine ⟨2*M,by positivity,?_⟩
  intro A hA t ht
  refine ⟨mul_nonneg (neg_nonneg.mpr (outerProfile_deriv_nonpos hA ht)) ht,?_⟩
  by_cases htA : t≤2*A
  · rw [outerProfile_deriv ht,neg_neg]
    have hd : 0≤deriv Real.smoothTransition ((t-A)/A) := Real.smoothTransition.monotone.deriv_nonneg
    have h1 := mul_le_mul_of_nonneg_right (hbound ((t-A)/A)) (div_nonneg ht hA.le)
    have h2 : t/A≤2 := (div_le_iff₀ hA).mpr (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 hM.le
    calc
      deriv Real.smoothTransition ((t-A)/A)/A*t=deriv Real.smoothTransition ((t-A)/A)*(t/A) := by ring
      _≤M*(t/A) := h1
      _≤2*M := by linarith only [h3]
  · rw [outerProfile_deriv_zero_after hA (lt_of_not_ge htA)]
    simpa using (le_of_lt (show 0<2*M by positivity))

lemma outerProfile_weight_tendsto_zero (t : ℝ) (ht : 0≤t) :
    Tendsto (fun A : ℝ => (-deriv (outerProfile A) t)*t) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (max t 0)] with A hA
  have h0 : 0<A := lt_of_le_of_lt (le_max_right _ _) hA
  have htA : t<A := lt_of_le_of_lt (le_max_left _ _) hA
  simp only [outerProfile_deriv_zero_before h0 ht htA,neg_zero,zero_mul]

lemma radial_boundary_integral_tendsto_zero {e : Plane → ℝ} (he : Continuous e)
    (hn : ∀ z, 0≤e z) (hei : Integrable e) :
    Tendsto (fun A : ℝ => ∫ z : Plane, (-deriv (outerProfile A) (radiusSq z))*radiusSq z*e z)
      atTop (𝓝 0) := by
  obtain ⟨B,hB,hbound⟩ := outerProfile_weight_uniform_bound
  have hi : Integrable (fun z => B*e z) := hei.const_mul B
  have hh := tendsto_integral_filter_of_dominated_convergence
    (F := fun A z => (-deriv (outerProfile A) (radiusSq z))*radiusSq z*e z)
    (fun z => B*e z)
    (Eventually.of_forall fun A : ℝ =>
      (((((outerProfile_smooth A).continuous_deriv (by simp)).comp radiusSq_smooth.continuous).neg.mul
        radiusSq_smooth.continuous).mul he).aestronglyMeasurable)
    (by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with A hA
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (hbound A hA _ (radiusSq_nonneg z)).1 (hn z))]
        exact mul_le_mul_of_nonneg_right (hbound A hA _ (radiusSq_nonneg z)).2 (hn z)) hi
    (ae_of_all _ fun z => by
      simpa only [zero_mul] using (outerProfile_weight_tendsto_zero (radiusSq z) (radiusSq_nonneg z)).mul_const (e z))
  simpa only [integral_zero] using hh

lemma radial_energy_integral_tendsto {e : Plane → ℝ} (he : Continuous e)
    (hn : ∀ z, 0≤e z) (hei : Integrable e) :
    Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z*e z) atTop (𝓝 (∫ z,e z)) := by
  exact tendsto_integral_filter_of_dominated_convergence
    (F := fun A z => sourceRadialCutoff A z * e z) e
    (Eventually.of_forall fun A : ℝ =>
      ((sourceRadialCutoff_smooth A).continuous.mul he).aestronglyMeasurable)
    (Eventually.of_forall fun A : ℝ => ae_of_all _ fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (sourceRadialCutoff_nonneg _ _) (hn z))]
      exact mul_le_of_le_one_left (hn z) (sourceRadialCutoff_le_one A z)) hei
    (ae_of_all _ fun z => by simpa only [one_mul] using (sourceRadialCutoff_tendsto z).mul_const (e z))


end
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
open SymplecticBallPacking.Hamiltonian
variable {n : ℕ}

lemma dirichletEnergy_zero_fderiv {u : ℂ → Phase n} {z : Plane}
    (he : dirichletEnergy u z=0) : fderiv ℝ (realCurve u) z=0 := by
  have hx : fderiv ℝ (realCurve u) z (1,0)=0 := by
    by_contra hn
    have hp := stdDot_pos hn
    have hy := stdDot_nonneg (fderiv ℝ (realCurve u) z (0,1))
    unfold dirichletEnergy at he
    linarith
  have hy : fderiv ℝ (realCurve u) z (0,1)=0 := by
    by_contra hn
    have hp := stdDot_pos hn
    have hx := stdDot_nonneg (fderiv ℝ (realCurve u) z (1,0))
    unfold dirichletEnergy at he
    linarith
  apply ContinuousLinearMap.ext
  intro v
  have hv : v=v.1 • ((1,0) : Plane)+v.2 • (0,1) := by ext <;> simp
  rw [hv,map_add,map_smul,map_smul,hx,hy]
  simp

theorem finite_energy_calibrated_curve_constant {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) {C : ℝ} (hC : 0≤C)
    (hcal : ∀ z, dirichletEnergy u z≤C*curveAreaDensity u z)
    (hei : Integrable (dirichletEnergy u)) : ∀ z w : ℂ, u z=u w := by
  have hleft := radial_energy_integral_tendsto (dirichletEnergy_continuous hu)
    (dirichletEnergy_nonneg u) hei
  have hright := (radial_boundary_integral_tendsto_zero (dirichletEnergy_continuous hu)
    (dirichletEnergy_nonneg u) hei).const_mul (C*(((2*Real.pi)^2+1)/2))
  have hle : (∫ z, dirichletEnergy u z)≤0 := by
    have h := le_of_tendsto_of_tendsto hleft hright (by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with A hA
      exact calibrated_radial_energy_bound hu hC hcal hA)
    simpa only [mul_zero] using h
  have he : (∫ z, dirichletEnergy u z)=0 := le_antisymm hle
    (integral_nonneg (dirichletEnergy_nonneg u))
  have hae := (integral_eq_zero_iff_of_nonneg (dirichletEnergy_nonneg u) hei).mp he
  have heq : dirichletEnergy u=0 :=
    ((dirichletEnergy_continuous hu).ae_eq_iff_eq (volume : Measure Plane) continuous_zero).mp hae
  have hd (z : Plane) : fderiv ℝ (realCurve u) z=0 :=
    dirichletEnergy_zero_fderiv (congrFun heq z)
  intro z w
  exact is_const_of_fderiv_eq_zero ((realCurve_smooth hu).differentiable (by simp)) hd
    (Complex.equivRealProdCLM z) (Complex.equivRealProdCLM w)

theorem exact_homotopy_no_finite_energy_bubbles {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) {S : ℝ}
    (hout : ∀ x, S<capacity x → J x=standardJ n)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (hcr : ∀ z, PseudoHolomorphicAt (lineHomotopy J t) u z)
    (hei : Integrable (dirichletEnergy u)) : ∀ z w : ℂ, u z=u w := by
  obtain ⟨C,hC,hcal⟩ := uniform_homotopy_pointwise_calibration hJs hJ hout
  exact finite_energy_calibrated_curve_constant hu hC.le (hcal t ht u hu hcr) hei


lemma outerProfile_mono_parameter {A B t : ℝ} (hA : 0<A) (hAB : A≤B) (ht : 0≤t) :
    outerProfile A t≤outerProfile B t := by
  have hB : 0<B := hA.trans_le hAB
  have harg : (t-B)/B≤(t-A)/A := by
    rw [sub_div,sub_div,div_self hA.ne',div_self hB.ne']
    exact sub_le_sub_right (div_le_div_of_nonneg_left ht hA hAB) 1
  exact mul_le_mul_of_nonneg_left
    (sub_le_sub_left (Real.smoothTransition.monotone harg) 1)
    (Real.smoothTransition.nonneg _)

lemma outerProfile_zero_after {A t : ℝ} (hA : 0<A) (ht : 2*A≤t) :
    outerProfile A t=0 := by
  have ha : 1≤(t-A)/A := (le_div_iff₀ hA).mpr (by linarith)
  simp only [outerProfile,Real.smoothTransition.one_of_one_le ha,sub_self,mul_zero]

lemma cutoff_weight_annulus_bound {B : ℝ} (hB : 0≤B)
    (hbound : ∀ A : ℝ, 0<A → ∀ t : ℝ, 0≤t → (-deriv (outerProfile A) t)*t≤B)
    {A : ℝ} (hA : 0<A) (z : Plane) :
    (-deriv (outerProfile A) (radiusSq z))*radiusSq z≤
      B*(sourceRadialCutoff (4*A) z-sourceRadialCutoff (A/4) z) := by
  have hmono : 0 ≤ sourceRadialCutoff (4*A) z-sourceRadialCutoff (A/4) z :=
    sub_nonneg.mpr (outerProfile_mono_parameter (A := A/4) (B := 4*A) (by positivity) (by linarith) (radiusSq_nonneg z))
  by_cases hd : deriv (outerProfile A) (radiusSq z)=0
  · rw [hd,neg_zero,zero_mul]
    exact mul_nonneg hB hmono
  have hlo : A≤radiusSq z := by
    by_contra! h
    exact hd (outerProfile_deriv_zero_before hA (radiusSq_nonneg z) h)
  have hhi : radiusSq z≤2*A := by
    by_contra! h
    exact hd (outerProfile_deriv_zero_after hA h)
  have h4 : sourceRadialCutoff (4*A) z=1 :=
    outerProfile_one_before (radiusSq_nonneg z) (by linarith) (by positivity)
  have hq : sourceRadialCutoff (A/4) z=0 :=
    outerProfile_zero_after (by positivity) (by linarith)
  rw [h4,hq,sub_zero,mul_one]
  exact hbound A hA _ (radiusSq_nonneg z)

def radialCurveEnergy (u : ℂ → Phase n) (A : ℝ) : ℝ :=
  ∫ z : Plane, sourceRadialCutoff A z*dirichletEnergy u z

lemma radialCurveEnergy_nonneg (u : ℂ → Phase n) (A : ℝ) : 0≤radialCurveEnergy u A :=
  integral_nonneg (fun z => mul_nonneg (sourceRadialCutoff_nonneg A z) (dirichletEnergy_nonneg u z))

lemma radialCurveEnergy_mono {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    {A B : ℝ} (hA : 0<A) (hAB : A≤B) : radialCurveEnergy u A≤radialCurveEnergy u B :=
  integral_mono (smooth_cutoff_integrable_mul hA (dirichletEnergy_continuous hu))
    (smooth_cutoff_integrable_mul (hA.trans_le hAB) (dirichletEnergy_continuous hu))
    (fun z => mul_le_mul_of_nonneg_right (outerProfile_mono_parameter hA hAB (radiusSq_nonneg z))
      (dirichletEnergy_nonneg u z))

theorem calibrated_energy_hole_filling {C : ℝ} (hC : 0<C) :
    ∃ θ : ℝ, 0<θ ∧ θ<1 ∧ ∀ (u : ℂ → Phase n), ContDiff ℝ ∞ u →
      (∀ z, dirichletEnergy u z≤C*curveAreaDensity u z) →
      ∀ A : ℝ, 0<A → radialCurveEnergy u A≤θ*radialCurveEnergy u (16*A) := by
  obtain ⟨B,hB,hbound⟩ := outerProfile_weight_uniform_bound
  let K := C*(((2*Real.pi)^2+1)/2)*B
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨K/(K+1),div_pos hK (by linarith), (div_lt_one (by linarith)).mpr (by linarith),?_⟩
  intro u hu hcal A hA
  have hfour : 0<4*A := by positivity
  have he := calibrated_radial_energy_bound hu hC.le hcal hfour
  have hdi : Integrable (fun z : Plane => (-deriv (outerProfile (4*A)) (radiusSq z))*radiusSq z*dirichletEnergy u z) := by
    exact (((((outerProfile_smooth (4*A)).continuous_deriv (by simp)).comp radiusSq_smooth.continuous).neg.mul
      radiusSq_smooth.continuous).mul (dirichletEnergy_continuous hu)).integrable_of_hasCompactSupport
      (((HasCompactSupport.comp_radiusSq (outerProfile_compact hfour).deriv).neg.mul_right).mul_right)
  have hfi := smooth_cutoff_integrable_mul (show 0<16*A by positivity) (dirichletEnergy_continuous hu)
  have hgi := smooth_cutoff_integrable_mul hA (dirichletEnergy_continuous hu)
  have hpoint (z : Plane) := mul_le_mul_of_nonneg_right
    (cutoff_weight_annulus_bound hB.le (fun A hA t ht => (hbound A hA t ht).2) hfour z)
    (dirichletEnergy_nonneg u z)
  have hid := integral_mono hdi ((hfi.sub hgi).const_mul B) (fun z => by
    have h44 : 4*(4*A)=16*A := by ring
    have h4q : 4*A/4=A := by ring
    simpa only [h44,h4q,sub_mul,mul_assoc,Pi.sub_apply] using hpoint z)
  simp only [Pi.sub_apply] at hid
  rw [integral_const_mul,integral_sub hfi hgi] at hid
  have hm := radialCurveEnergy_mono hu hA (show A≤4*A by linarith)
  have hc : 0≤C*(((2*Real.pi)^2+1)/2) := by positivity
  have hh := he.trans (mul_le_mul_of_nonneg_left hid hc)
  change radialCurveEnergy u (4*A)≤C*(((2*Real.pi)^2+1)/2)*
    (B*(radialCurveEnergy u (16*A)-radialCurveEnergy u A)) at hh
  have hfin : (K+1)*radialCurveEnergy u A≤K*radialCurveEnergy u (16*A) := by
    dsimp [K]
    nlinarith only [hm,hh]
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (by linarith : 0<K+1)).mpr (by nlinarith only [hfin])


lemma radialCurveEnergy_geometric_bound {u : ℂ → Phase n} {θ : ℝ} (hθ : 0≤θ)
    (hstep : ∀ A : ℝ, 0<A → radialCurveEnergy u A≤θ*radialCurveEnergy u (16*A))
    {A : ℝ} (hA : 0<A) (k : ℕ) :
    radialCurveEnergy u (A/16^k)≤θ^k*radialCurveEnergy u A := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := hstep (A/16^(k+1)) (by positivity)
    have he : 16*(A/16^(k+1))=A/16^k := by
      rw [pow_succ]
      field_simp
    rw [he] at hs
    refine hs.trans ((mul_le_mul_of_nonneg_left ih hθ).trans_eq ?_)
    rw [pow_succ]
    ring

theorem exact_homotopy_geometric_energy_decay {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x)) {S : ℝ}
    (hout : ∀ x, S<capacity x → J x=standardJ n) :
    ∃ θ : ℝ, 0<θ ∧ θ<1 ∧ ∀ t∈Icc (0:ℝ) 1, ∀ (u : ℂ → Phase n),
      ContDiff ℝ ∞ u → (∀ z, PseudoHolomorphicAt (lineHomotopy J t) u z) →
      ∀ A : ℝ, 0<A → ∀ k : ℕ,
        radialCurveEnergy u (A/16^k)≤θ^k*radialCurveEnergy u A := by
  obtain ⟨C,hC,hcal⟩ := uniform_homotopy_pointwise_calibration hJs hJ hout
  obtain ⟨θ,hθ,hθ1,hdec⟩ := calibrated_energy_hole_filling (n := n) hC
  refine ⟨θ,hθ,hθ1,?_⟩
  intro t ht u hu hcr A hA k
  exact radialCurveEnergy_geometric_bound hθ.le (hdec u hu (hcal t ht u hu hcr)) hA k


def centeredCurve (u : ℂ → Phase n) (c : ℂ) (z : ℂ) : Phase n := u (z+c)

lemma centeredCurve_smooth {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) :
    ContDiff ℝ ∞ (centeredCurve u c) := hu.comp (contDiff_id.add contDiff_const)

lemma realCurve_centered (u : ℂ → Phase n) (c : ℂ) :
    realCurve (centeredCurve u c)=fun z => realCurve u (z+Complex.equivRealProdCLM c) := by
  funext z
  simp only [realCurve,centeredCurve,Function.comp_def,map_add,ContinuousLinearEquiv.symm_apply_apply]

lemma centeredCurve_fderiv {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (z : Plane) :
    fderiv ℝ (realCurve (centeredCurve u c)) z=
      fderiv ℝ (realCurve u) (z+Complex.equivRealProdCLM c) := by
  rw [realCurve_centered]
  have hh := ((realCurve_smooth hu).differentiable (by simp) (z+Complex.equivRealProdCLM c)).hasFDerivAt.comp z
    ((hasFDerivAt_id (𝕜 := ℝ) z).add_const (Complex.equivRealProdCLM c))
  change HasFDerivAt (fun z => realCurve u (z+Complex.equivRealProdCLM c)) _ z at hh
  simpa only [ContinuousLinearMap.comp_id] using hh.fderiv

lemma dirichletEnergy_centered {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (z : Plane) :
    dirichletEnergy (centeredCurve u c) z=dirichletEnergy u (z+Complex.equivRealProdCLM c) := by
  simp only [dirichletEnergy,centeredCurve_fderiv hu]

lemma curveAreaDensity_centered {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u) (c : ℂ) (z : Plane) :
    curveAreaDensity (centeredCurve u c) z=curveAreaDensity u (z+Complex.equivRealProdCLM c) := by
  simp only [curveAreaDensity,centeredCurve_fderiv hu]

lemma stdDot_add_self_le (v w : Phase n) :
    stdDot n (v+w) (v+w)≤2*stdDot n v v+2*stdDot n w w := by
  have hh := stdDot_nonneg (v-w)
  rw [stdDot_sub_self] at hh
  simp only [map_add,add_apply]
  rw [stdDot_symm w v]
  linarith

lemma stdDot_standardJ_self (v : Phase n) :
    stdDot n (standardJ n v) (standardJ n v)=stdDot n v v := by
  rw [stdDot_J_right,standardForm_skew (standardJ n v),standardForm_J_right,neg_neg]

lemma dirichletEnergy_add_le {u v : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (z : Plane) :
    dirichletEnergy (u+v) z≤2*dirichletEnergy u z+2*dirichletEnergy v z := by
  have hd : fderiv ℝ (realCurve (u+v)) z=fderiv ℝ (realCurve u) z+fderiv ℝ (realCurve v) z :=
    (((realCurve_smooth hu).differentiable (by simp) z).hasFDerivAt.add
      ((realCurve_smooth hv).differentiable (by simp) z).hasFDerivAt).fderiv
  have hx := stdDot_add_self_le (fderiv ℝ (realCurve u) z (1,0)) (fderiv ℝ (realCurve v) z (1,0))
  have hy := stdDot_add_self_le (fderiv ℝ (realCurve u) z (0,1)) (fderiv ℝ (realCurve v) z (0,1))
  simp only [dirichletEnergy,hd,add_apply]
  nlinarith only [hx,hy]

lemma dirichletEnergy_linear (a : Phase n) (z : Plane) :
    dirichletEnergy (fun w : ℂ => w • a) z=2*stdDot n a a := by
  have hu : ContDiff ℝ ∞ (fun w : ℂ => w • a) := contDiff_id.smul contDiff_const
  have hd := (hasFDerivAt_id (𝕜 := ℝ) (Complex.equivRealProdCLM.symm z)).smul_const a
  change HasFDerivAt (fun w : ℂ => w • a) _ (Complex.equivRealProdCLM.symm z) at hd
  simp only [dirichletEnergy,realCurve_fderiv (hu.differentiable (by simp) _), hd.fderiv,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply]
  simp only [show Complex.equivRealProdCLM.symm (1,0)=(1:ℂ) from rfl,
    show Complex.equivRealProdCLM.symm (0,1)=Complex.I from rfl,one_smul]
  change stdDot n a a+stdDot n (standardJ n a) (standardJ n a)=_
  rw [stdDot_standardJ_self]
  ring

lemma dirichletEnergy_le_affineCorrection {u : ℂ → Phase n}
    (hu : ContDiff ℝ ∞ u) (a : Phase n) (z : Plane) :
    dirichletEnergy u z≤2*dirichletEnergy (affineCorrection u a) z+4*stdDot n a a := by
  have he : u=affineCorrection u a+(fun w : ℂ => w • a) := by
    funext w
    simp only [Pi.add_apply,affineCorrection,sub_add_cancel]
  have hh := dirichletEnergy_add_le (affineCorrection_smooth hu a)
    (contDiff_id.smul (contDiff_const (c := a))) z
  change dirichletEnergy (affineCorrection u a+(fun w : ℂ => w • a)) z≤
    2*dirichletEnergy (affineCorrection u a) z+2*dirichletEnergy (fun w : ℂ => w • a) z at hh
  rw [←he,dirichletEnergy_linear] at hh
  linarith only [hh]

lemma centered_unit_energy_bound {u : ℂ → Phase n} (hu : ContDiff ℝ ∞ u)
    (a : Phase n) (hei : Integrable (dirichletEnergy (affineCorrection u a))) (c : ℂ) :
    radialCurveEnergy (centeredCurve u c) 1≤
      2*(∫ z, dirichletEnergy (affineCorrection u a) z)+
        4*stdDot n a a*(∫ z : Plane, sourceRadialCutoff 1 z) := by
  have hec := (dirichletEnergy_continuous (affineCorrection_smooth hu a)).comp
    (continuous_id.add (continuous_const (y := Complex.equivRealProdCLM c)))
  have hei' : Integrable (fun z => dirichletEnergy (affineCorrection u a) (z+Complex.equivRealProdCLM c)) :=
    (measurePreserving_add_right volume (Complex.equivRealProdCLM c)).integrable_comp_of_integrable hei
  have hcuti : Integrable (sourceRadialCutoff 1) :=
    (sourceRadialCutoff_smooth 1).continuous.integrable_of_hasCompactSupport (sourceRadialCutoff_compact (by norm_num))
  have hci := smooth_cutoff_integrable_mul (by norm_num : (0:ℝ)<1) hec
  have hu1 := smooth_cutoff_integrable_mul (by norm_num : (0:ℝ)<1)
    (dirichletEnergy_continuous (centeredCurve_smooth hu c))
  have hpoint (z : Plane) : sourceRadialCutoff 1 z*dirichletEnergy (centeredCurve u c) z≤
      2*dirichletEnergy (affineCorrection u a) (z+Complex.equivRealProdCLM c)+
        (4*stdDot n a a)*sourceRadialCutoff 1 z := by
    rw [dirichletEnergy_centered hu]
    have hh := mul_le_mul_of_nonneg_left (dirichletEnergy_le_affineCorrection hu a
      (z+Complex.equivRealProdCLM c)) (sourceRadialCutoff_nonneg 1 z)
    have hb := mul_le_of_le_one_left (dirichletEnergy_nonneg (affineCorrection u a) (z+Complex.equivRealProdCLM c))
      (sourceRadialCutoff_le_one 1 z)
    nlinarith only [hh,hb]
  have hle := integral_mono hu1 ((hei'.const_mul 2).add (hcuti.const_mul (4*stdDot n a a))) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add (hei'.const_mul 2) (hcuti.const_mul _),integral_const_mul,integral_const_mul,
    integral_add_right_eq_self] at hle
  exact hle


theorem AffineLineCurve.affine_correction_energy_of_slope {J : Phase n → End n}
    {p q : Phase n} {u : ℂ → Phase n} (hu : AffineLineCurve J p q u)
    (hJc : HasCompactSupport (fun x => J x-standardJ n)) {a : Phase n}
    (ha : Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a)) :
    Integrable (dirichletEnergy (affineCorrection u a)) ∧
      (∫ z, dirichletEnergy (affineCorrection u a) z)=∫ z, lineResidualEnergy u z := by
  have hh := analyticAt_dslope_zero (infinityGerm_analyticAt (hu.holomorphic_at_infinity hJc) ha)
  have he := fun z hz => infinityGerm_affine_reconstruction u a (z := z) hz
  have hv := affineCorrection_smooth hu.1 a
  have hβ := planarPullback_smooth (realCurve_smooth hv) (stdOmega n).contDiff
  have hlim := radial_curl_integral_tendsto hβ (affineCorrection_real_flux_zero hu.1 hh he)
  simp only [mul_zero] at hlim
  have hfl : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z * lineResidualEnergy u z)
      atTop (𝓝 (∫ z, lineResidualEnergy u z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [compact_integral_cutoff_eventually (lineResidualEnergy_compact hu hJc)] with A hA
    rw [hA]
  have helim : Tendsto (fun A : ℝ => ∫ z, sourceRadialCutoff A z *
      dirichletEnergy (affineCorrection u a) z) atTop (𝓝 (∫ z, lineResidualEnergy u z)) := by
    have hl := hlim.add hfl
    simp only [zero_add] at hl
    apply hl.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with A hA
    rw [←integral_add
      (smooth_cutoff_integrable_mul hA ((planarCurl_contDiff hβ).continuous))
      (smooth_cutoff_integrable_mul hA (lineResidualEnergy_continuous hu.1))]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [standard_primitive_curl hv,affineCorrection_residual_energy hu.1]
    ring
  exact integrable_of_radial_exhaustion_limit (dirichletEnergy_continuous hv)
    (dirichletEnergy_nonneg _) helim


theorem exact_line_uniform_local_energy {J : Phase n → End n}
    (hJs : ContDiff ℝ ∞ J) (hJ : ∀ x, Compatible (J x))
    (hJc : HasCompactSupport (fun x => J x-standardJ n))
    {S T : ℝ} (hST : S<T) (hT : T<1)
    (hout : ∀ x, S<capacity x → J x=standardJ n) :
    ∃ C M θ : ℝ, 0<C ∧ 0≤M ∧ 0<θ ∧ θ<1 ∧
      ∀ t∈Icc (0:ℝ) 1, ∀ (p q : Phase n) (u : ℂ → Phase n),
        AffineLineCurve (lineHomotopy J t) p q u →
        ∃ a : Phase n, a≠0 ∧
          Tendsto (fun z : ℂ => z⁻¹ • u z) (cocompact ℂ) (𝓝 a) ∧
          ∀ (c : ℂ) (k : ℕ), radialCurveEnergy (centeredCurve u c) (1/16^k)≤
            θ^k*(C+M*stdDot n a a) := by
  obtain ⟨D,hD,hres⟩ := exact_line_homotopy_residual_energy_bound hJs hJ hJc hST hT hout
  obtain ⟨L,hL,hcal⟩ := uniform_homotopy_pointwise_calibration hJs hJ hout
  obtain ⟨θ,hθ,hθ1,hstep⟩ := calibrated_energy_hole_filling (n := n) hL
  let M : ℝ := 4*(∫ z : Plane,sourceRadialCutoff 1 z)
  have hM : 0≤M := mul_nonneg (by norm_num) (integral_nonneg (sourceRadialCutoff_nonneg 1))
  refine ⟨2*D,M,θ,by positivity,hM,hθ,hθ1,?_⟩
  intro t ht p q u hu
  obtain ⟨a,ha,hlim⟩ := hu.2.2.2.2
  obtain ⟨hei,heiVal⟩ := hu.affine_correction_energy_of_slope (lineHomotopy_compact hJc ht) hlim
  refine ⟨a,ha,hlim,?_⟩
  intro c k
  have hcalC (z : Plane) : dirichletEnergy (centeredCurve u c) z≤L*curveAreaDensity (centeredCurve u c) z := by
    rw [dirichletEnergy_centered hu.1,curveAreaDensity_centered hu.1]
    exact hcal t ht u hu.1 hu.2.1 _
  have hgeom := radialCurveEnergy_geometric_bound hθ.le
    (hstep (centeredCurve u c) (centeredCurve_smooth hu.1 c) hcalC) (by norm_num : (0:ℝ)<1) k
  have hunit := centered_unit_energy_bound hu.1 a hei c
  rw [heiVal] at hunit
  have hres' := hres t ht p q u hu
  have hupp : radialCurveEnergy (centeredCurve u c) 1≤2*D+M*stdDot n a a := by
    dsimp [M]
    nlinarith only [hunit,hres']
  exact hgeom.trans (mul_le_mul_of_nonneg_left hupp (pow_nonneg hθ.le _))



end HigherDimensionalBallPacking.Rigidity
end

end OAI
