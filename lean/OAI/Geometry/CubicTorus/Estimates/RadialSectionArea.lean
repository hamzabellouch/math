import Mathlib
import OAI.Geometry.CubicTorus.Estimates.PlanarRadialArea

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def centeredPlaneSection (E : Set Torus) (c : Cover) (t : ℝ) : Set ℂ :=
  {z | complexSquareGauge z<1/2 ∧ quotientMap (coordinateSectionPoint c t z)∈E}

lemma norm_smul_unitAngle_arg (z : ℂ) : ‖z‖ • unitAngle (z.arg/(2*Real.pi))=z := by
  rw [unitAngle]
  have he : 2*Real.pi*(z.arg/(2*Real.pi))=z.arg := by field_simp
  rw [he,Complex.real_smul]
  exact Complex.norm_mul_exp_arg_mul_I z

lemma radius_le_squareScale_of_gauge {z : ℂ} (hz : complexSquareGauge z≤1/2) :
    ‖z‖≤unitSquareScale (z.arg/(2*Real.pi)) := by
  let a := z.arg/(2*Real.pi)
  have hh : ‖z‖*complexSquareGauge (unitAngle a)≤1/2 := by
    rw [← complexSquareGauge_smul (norm_nonneg z),norm_smul_unitAngle_arg]
    exact hz
  rw [unitSquareScale,le_div_iff₀ (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero a)))]
  nlinarith

lemma planarRadialRegion_eq_actual_section {E : Set Torus} {c : Cover} {t : ℝ} {r : ℝ → ℝ}
    (hr0 : ∀ a,0<r a) (hrb : ∀ a,r a<unitSquareScale a)
    (hphase : ∀ a u,0≤u → u≤unitSquareScale a →
      (quotientMap (coordinateSectionPoint c t (u • unitAngle a))∈E ↔ u<r a)) :
    planarRadialRegion r=centeredPlaneSection E c t := by
  ext z
  let a := z.arg/(2*Real.pi)
  have hg : 0<complexSquareGauge (unitAngle a) := complexSquareGauge_pos (unitAngle_ne_zero a)
  have hgs : unitSquareScale a*complexSquareGauge (unitAngle a)=1/2 := by
    dsimp [unitSquareScale]
    field_simp [hg.ne']
  change ‖z‖<r a ↔ complexSquareGauge z<1/2 ∧ quotientMap (coordinateSectionPoint c t z)∈E
  constructor
  · intro hz
    have hb : ‖z‖≤unitSquareScale a := (hz.trans (hrb a)).le
    refine ⟨?_,?_⟩
    · rw [← norm_smul_unitAngle_arg z,complexSquareGauge_smul (norm_nonneg z)]
      exact (mul_lt_mul_of_pos_right (hz.trans (hrb a)) hg).trans_eq hgs
    · have he := (hphase a ‖z‖ (norm_nonneg z) hb).mpr hz
      rwa [norm_smul_unitAngle_arg] at he
  · rintro ⟨hz,hE⟩
    rcases (norm_nonneg z).eq_or_lt with hzero | hpos
    · rw [← hzero]
      exact hr0 a
    · apply (hphase a ‖z‖ hpos.le (radius_le_squareScale_of_gauge hz.le)).mp
      rwa [norm_smul_unitAngle_arg]

theorem isMinimizerAt_actual_radial_section_area {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E))
    {t : ℝ} (ht : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2))
    (htE : quotientMap (coordinateSectionPoint (chamberCorner s) t 0)∈openRepresentative E) :
    ∃ r : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧ Function.Periodic r 1 ∧ (∀ a,0<r a) ∧
      centeredPlaneSection (openRepresentative E) (chamberCorner s) t=planarRadialRegion r ∧
      (∀ a,quotientMap (coordinateSectionPoint (chamberCorner s) t (r a • unitAngle a))∈frontier (openRepresentative E)) ∧
      volume.real (centeredPlaneSection (openRepresentative E) (chamberCorner s) t)=
        Real.pi*(∫ a in (0 : ℝ)..1,(r a)^2) ∧
      4*Real.pi*volume.real (centeredPlaneSection (openRepresentative E) (chamberCorner s) t)≤
        (∫ a in (0 : ℝ)..1,Real.sqrt ((deriv r a)^2+(2*Real.pi*r a)^2))^2 := by
  obtain ⟨r,hr,hrp,hrb,hbd,hphase,hcl⟩ := isMinimizerAt_smooth_radial_section
    hV hE hm hμ hN hp ha hs hsg hv1 hv2 ht htE
  have hpos := fun a => (hrb a).1
  have he := (planarRadialRegion_eq_actual_section hpos (fun a => (hrb a).2) hphase).symm
  refine ⟨r,hr,hrp,hpos,he,hbd,?_,?_⟩
  · rw [he]
    exact real_volume_planarRadialRegion hr.continuous hrp hpos
  · rw [he]
    exact planar_radial_area_length (fun a => (hr.differentiable (by simp) a).hasDerivAt)
      (hr.continuous_deriv (by simp)) hrp hpos

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialNormalCalibration_eq_of_unit_axis_zero {N : Cover → Cover} {x : Cover}
    (hn : ‖N x‖=1) (ha : N x 0=0) : axialNormalCalibration N 0 x=N x := by
  have he : axialTangentPart 0 (N x)=N x := by simp [axialTangentPart,ha]
  rw [axialNormalCalibration,regularizedNormal_eq (by rw [he,hn]; norm_num),he,hn,inv_one,one_smul]

lemma isMinimizerAt_normal_corner_section_zero {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : coordinateReflection 0 ⁻¹' E =ᵐ[torusVolume] E)
    (s : Fin 3 → Bool) (z : ℂ)
    (hb : quotientMap (coordinateSectionPoint (chamberCorner s) (chamberCorner s 0) z)∈frontier (openRepresentative E)) :
    N (coordinateSectionPoint (chamberCorner s) (chamberCorner s 0) z) 0=0 := by
  let x := coordinateSectionPoint (chamberCorner s) (chamberCorner s 0) z
  have hz : coordinateSine 0 (representative (quotientMap x))=0 := by
    rw [periodic_representative (coordinateSine_periodic 0)]
    simp only [coordinateSine,x,coordinateSectionPoint_apply,ite_true,chamberCorner]
    cases s 0 <;> simp
    ring_nf
    simp
  have hh := isMinimizerAt_normal_coordinate_seam_zero hV hE hm hμ hN hp ha 0 hs hb hz
  rwa [periodic_representative hp] at hh

theorem isMinimizerAt_endpoint_radial_calibration_density {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {r dr : ℝ → ℝ} (hr : ∀ a,HasDerivAt r (dr a) a)
    (hrb : ∀ a,0<r a ∧ r a<unitSquareScale a)
    (hb : ∀ a,quotientMap (coordinateSectionPoint (chamberCorner s) (chamberCorner s 0) (radialCurve r a))∈frontier (openRepresentative E))
    (a : ℝ) :
    complexDet (coordinatePlaneField (axialNormalCalibration N 0) (chamberCorner s) (chamberCorner s 0) (radialCurve r a))
      (radialVelocity r dr a)=Real.sqrt ((dr a)^2+(2*Real.pi*r a)^2) := by
  let x := coordinateSectionPoint (chamberCorner s) (chamberCorner s 0) (radialCurve r a)
  have hunit := isMinimizerAt_normal_unit_boundary hV hE hm hμ hN.continuous hp ha x (hb a)
  have hzero := isMinimizerAt_normal_corner_section_zero hV hE hm hμ hN hp ha (hs 0) s (radialCurve r a) (hb a)
  have hperp := isMinimizerAt_radial_curve_tangent hV hE hm hμ hN hp ha hr hb a
  rw [coordinatePlaneProjection_inner] at hperp
  have hg : complexSquareGauge (radialCurve r a)<1/2 := by
    have he : radialCurve r a=r a • unitAngle a := Complex.real_smul.symm
    rw [he,complexSquareGauge_smul (hrb a).1.le]
    have hh := (hrb a).2
    rw [unitSquareScale,lt_div_iff₀ (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero a)))] at hh
    nlinarith
  have hnz : radialCurve r a≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (hrb a).1.ne') (unitAngle_ne_zero a)
  have htrans := isMinimizerAt_coordinate_plane_transverse hV hE hm hμ hN hp ha hs hsg hnz hg (hb a)
  rw [coordinatePlaneProjection_inner] at htrans
  have hdet : 0<complexDet (radialCurve r a) (radialVelocity r dr a) := by
    rw [complexDet_eq_im,radialCurve_area_integrand]
    have hpos := (hrb a).1
    positivity
  change complexDet (coordinatePlaneProjection (axialNormalCalibration N 0 x)) (radialVelocity r dr a)=_
  rw [axialNormalCalibration_eq_of_unit_axis_zero hunit hzero,
    complexDet_unit_positive (coordinatePlaneProjection_unit hunit hzero) hperp htrans hdet]
  rw [← radialVelocity_norm_sq,Real.sqrt_sq (norm_nonneg _)]

theorem isMinimizerAt_endpoint_radial_green {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {r dr : ℝ → ℝ} (hr : ∀ a,HasDerivAt r (dr a) a) (hdc : Continuous dr)
    (hrp : Function.Periodic r 1) (hrb : ∀ a,0<r a ∧ r a<unitSquareScale a)
    (hb : ∀ a,quotientMap (coordinateSectionPoint (chamberCorner s) (chamberCorner s 0) (radialCurve r a))∈frontier (openRepresentative E)) :
    (∫ z in planarRadialRegion r,divergence (axialNormalCalibration N 0)
      (coordinateSectionPoint (chamberCorner s) (chamberCorner s 0) z))=
      ∫ a in (0 : ℝ)..1,Real.sqrt ((dr a)^2+(2*Real.pi*r a)^2) := by
  have hF := (axialNormalCalibration_admissible hN hp 0).1
  have hCF := coordinatePlaneField_contDiff hF (chamberCorner s) (chamberCorner s 0)
  have hg := green_planarRadialRegion hr hdc hrp (fun a => (hrb a).1) (hCF.of_le (by simp))
  simp_rw [coordinatePlaneField_divergence (hF.differentiable (by simp)) (axialNormalCalibration_axis N 0)] at hg
  rw [hg]
  apply intervalIntegral.integral_congr
  intro a ha'
  exact isMinimizerAt_endpoint_radial_calibration_density hV hE hm hμ hN hp ha hs hsg hr hrb hb a

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma coordinatePlaneProjection_axialTangent (u : Cover) :
    coordinatePlaneProjection (axialTangentPart 0 u)=coordinatePlaneProjection u := by
  apply Complex.ext <;> simp [axialTangentPart]

lemma coordinatePlaneProjection_norm_le (u : Cover) : ‖coordinatePlaneProjection u‖≤‖u‖ := by
  have hh := coordinatePlaneProjection_norm_sq u
  nlinarith [sq_nonneg (u 0),norm_nonneg (coordinatePlaneProjection u),norm_nonneg u]

lemma coordinatePlaneProjection_norm_tangent (u : Cover) :
    ‖coordinatePlaneProjection u‖=‖axialTangentPart 0 u‖ := by
  have h1 := coordinatePlaneProjection_norm_sq u
  have h2 := axialTangentPart_norm_sq 0 u
  nlinarith [norm_nonneg (coordinatePlaneProjection u),norm_nonneg (axialTangentPart 0 u)]

lemma axialTangentPart_smul (i : Fin 3) (k : ℝ) (u : Cover) :
    axialTangentPart i (k • u)=k • axialTangentPart i u := by
  simp only [axialTangentPart,PiLp.smul_apply,smul_sub,smul_smul,smul_eq_mul]

lemma regularizedNormal_unit_of_large {R : Cover → Cover} {x : Cover}
    (h : 1/4≤‖R x‖^2) : ‖regularizedNormal R x‖=1 := by
  have hpos : 0<‖R x‖ := by nlinarith [norm_nonneg (R x)]
  rw [regularizedNormal_eq h,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos),inv_mul_cancel₀ hpos.ne']

lemma scaled_axialCalibration_density {N : Cover → Cover} {k : ℝ} (hk : 0<k)
    {x : Cover} (hlarge : 1/4≤‖axialTangentPart 0 (k • N x)‖^2)
    {z w : ℂ} (hperp : ⟪N x,coordinatePlaneLift w⟫=0)
    (htrans : 0<⟪N x,coordinatePlaneLift z⟫) (hdet : 0<complexDet z w) :
    complexDet (coordinatePlaneProjection (axialNormalCalibration (fun a => k • N a) 0 x)) w=‖w‖ := by
  let R : Cover → Cover := fun a => axialTangentPart 0 (k • N a)
  have hp : 0<‖R x‖ := by change 1/4≤‖R x‖^2 at hlarge; nlinarith [norm_nonneg (R x)]
  have he : coordinatePlaneProjection (axialNormalCalibration (fun a => k • N a) 0 x)=
      (‖R x‖⁻¹*k) • coordinatePlaneProjection (N x) := by
    change coordinatePlaneProjection (regularizedNormal R x)=_
    rw [regularizedNormal_eq (R := R) (x := x) hlarge]
    simp only [R,map_smul,coordinatePlaneProjection_axialTangent,smul_smul]
  apply complexDet_unit_positive (z := z)
  · apply coordinatePlaneProjection_unit
    · exact regularizedNormal_unit_of_large (R := R) (x := x) hlarge
    · exact axialNormalCalibration_axis _ _ _
  · rw [he]
    simp only [Complex.smul_re,Complex.smul_im,smul_eq_mul]
    rw [coordinatePlaneProjection_inner] at hperp
    calc
      _=(‖R x‖⁻¹*k)*((coordinatePlaneProjection (N x)).re*w.re+(coordinatePlaneProjection (N x)).im*w.im) := by ring
      _=0 := by rw [hperp,mul_zero]
  · rw [he]
    simp only [Complex.smul_re,Complex.smul_im,smul_eq_mul]
    rw [coordinatePlaneProjection_inner] at htrans
    have hh : 0 < ‖R x‖⁻¹*k := mul_pos (inv_pos.mpr hp) hk
    calc
      0 < (‖R x‖⁻¹*k)*((coordinatePlaneProjection (N x)).re*z.re+(coordinatePlaneProjection (N x)).im*z.im) := mul_pos hh htrans
      _ = _ := by ring
  · exact hdet

lemma compact_positive_scale {q : ℝ → ℝ} (hq : ContinuousOn q (Icc (0 : ℝ) 1))
    (hp : ∀ a∈Icc (0 : ℝ) 1,0<q a) :
    ∃ k : ℝ,0<k ∧ ∀ a∈Icc (0 : ℝ) 1,1/4≤(k*q a)^2 := by
  obtain ⟨a,ha,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr (by norm_num)) hq
  have hqa := hp a ha
  refine ⟨(q a)⁻¹,inv_pos.mpr hqa,?_⟩
  intro b hb
  have hle : 1≤(q a)⁻¹*q b := by
    calc
      1=(q a)⁻¹*q a := (inv_mul_cancel₀ hqa.ne').symm
      _≤(q a)⁻¹*q b := mul_le_mul_of_nonneg_left (hmin hb) (inv_nonneg.mpr hqa.le)
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_integral_unit_translate {f : ℝ → ℝ} (hp : Function.Periodic f 1) (a c : ℝ) :
    (∫ x in Ioo a (a+1),f (x+c))=∫ x in Ico (0 : ℝ) 1,f x := by
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by linarith : a≤a+1),
    intervalIntegral.integral_comp_add_right,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
  convert hp.intervalIntegral_add_eq (a+c) 0 using 1 <;> congr 1 <;> ring

lemma bounded_integrable_rectangle {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z,‖f z‖≤M) (a b c d : ℝ) :
    IntegrableOn f (Ioo a b ×ˢ Ioo c d) := by
  apply IntegrableOn.of_bound (by
    rw [Measure.volume_eq_prod]
    simp only [Measure.prod_prod,Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hf.aestronglyMeasurable M
  exact Eventually.of_forall hb

lemma bounded_integrable_unit_square {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z,‖f z‖≤M) : IntegrableOn f (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1) := by
  apply IntegrableOn.of_bound (by rw [Measure.volume_eq_prod]; simp) hf.aestronglyMeasurable M
  exact Eventually.of_forall hb

lemma periodic_plane_integral_translate {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ z,‖f z‖≤M)
    (hx : ∀ y,Function.Periodic (fun x => f (x,y)) 1)
    (hy : ∀ x,Function.Periodic (fun y => f (x,y)) 1) (a b c d : ℝ) :
    (∫ z in Ioo a (a+1) ×ˢ Ioo b (b+1),f (z.1+c,z.2+d))=
      ∫ z in Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1,f z := by
  have hmeas : Measurable (fun z : ℝ × ℝ => f (z.1+c,z.2+d)) :=
    hf.comp ((measurable_fst.add_const c).prodMk (measurable_snd.add_const d))
  have hi := bounded_integrable_rectangle hmeas (fun z => hb (z.1+c,z.2+d)) a (a+1) b (b+1)
  have hj := bounded_integrable_unit_square hf hb
  rw [Measure.volume_eq_prod] at hi hj ⊢
  rw [setIntegral_prod _ hi,setIntegral_prod _ hj]
  simp_rw [periodic_integral_unit_translate (hy _) b d]
  apply periodic_integral_unit_translate (f := fun x => ∫ y in Ico (0 : ℝ) 1,f (x,y))
  intro x
  apply setIntegral_congr_fun measurableSet_Ico
  intro y _
  exact hx y x

lemma axialSplit_zero_symm (t : ℝ) (y : Plane) :
    (axialSplit 0).symm (t,y)=UpperComparison.tubeSplit.symm (t,y) := by
  ext i
  simp [axialSplit,coverCoordinatePermute,LinearIsometryEquiv.piLpCongrLeft_apply]

@[simp] lemma tubeSplit_symm_one (p : ℝ × Plane) : UpperComparison.tubeSplit.symm p 1=p.2 0 :=
  UpperComparison.tubeSplit_symm_succ p 0

@[simp] lemma tubeSplit_symm_two (p : ℝ × Plane) : UpperComparison.tubeSplit.symm p 2=p.2 1 :=
  UpperComparison.tubeSplit_symm_succ p 1

lemma coordinateSectionPoint_coordinates (c : Cover) (t : ℝ) (z : ℂ) :
    coordinateSectionPoint c t z=(axialSplit 0).symm
      (t,planeProductCoordinates.symm (z.re+c 1,z.im+c 2)) := by
  rw [axialSplit_zero_symm]
  ext i
  fin_cases i <;> simp [planeProductCoordinates_symm_apply] <;> ring

lemma centered_complex_integral_periodic {f : Cover → ℝ} (hf : Measurable f)
    (hp : ∀ m x,f (x+latticeVector m)=f x) {M : ℝ} (hb : ∀ x,‖f x‖≤M)
    (c : Cover) (t : ℝ) :
    (∫ z in {z : ℂ | complexSquareGauge z<1/2},f (coordinateSectionPoint c t z))=
      ∫ y in transverseSquare,f ((axialSplit 0).symm (t,y)) := by
  let g : ℝ × ℝ → ℝ := fun z => f ((axialSplit 0).symm (t,planeProductCoordinates.symm z))
  have hg : Measurable g := hf.comp ((axialSplit 0).symm.measurable.comp
    (measurable_const.prodMk planeProductCoordinates.symm.continuous.measurable))
  have hpre : Complex.measurableEquivRealProd ⁻¹'
      (Ioo (-(1/2) : ℝ) (1/2) ×ˢ Ioo (-(1/2) : ℝ) (1/2))=
      {z : ℂ | complexSquareGauge z<1/2} := by
    ext z
    simp [complexSquareGauge,abs_lt,max_lt_iff,Complex.measurableEquivRealProd]
  have hc := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun z : ℝ × ℝ => g (z.1+c 1,z.2+c 2))
    (Ioo (-(1/2) : ℝ) (1/2) ×ˢ Ioo (-(1/2) : ℝ) (1/2))
  rw [hpre] at hc
  have hfun : (fun z : ℂ => g ((Complex.measurableEquivRealProd z).1+c 1,
      (Complex.measurableEquivRealProd z).2+c 2))=(fun z => f (coordinateSectionPoint c t z)) := by
    funext z
    dsimp [g]
    rw [coordinateSectionPoint_coordinates]
  rw [hfun] at hc
  rw [hc]
  have hpp : planeProductCoordinates ⁻¹' (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)=transverseSquare := by
    ext y
    simp only [mem_preimage,planeProductCoordinates_apply,mem_prod,mem_Ico,transverseSquare,mem_ofPred_eq]
    constructor
    · intro h j
      fin_cases j <;> tauto
    · intro h
      exact ⟨h 0,h 1⟩
  have he := planeProductCoordinates_measurePreserving.setIntegral_preimage_emb
    planeProductCoordinates.toHomeomorph.measurableEmbedding g (Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1)
  rw [hpp] at he
  have he' : (∫ y in transverseSquare,f ((axialSplit 0).symm (t,y)))=
      ∫ z in Ico (0 : ℝ) 1 ×ˢ Ico (0 : ℝ) 1,g z := by simpa only [g,ContinuousLinearEquiv.symm_apply_apply] using he
  rw [he']
  have hperiod (j : Fin 2) (z : ℝ × ℝ) :
      g (if j=0 then z.1+1 else z.1,if j=1 then z.2+1 else z.2)=g z := by
    have hh := hp (Pi.single j.succ (1 : ℤ)) ((axialSplit 0).symm (t,planeProductCoordinates.symm z))
    have hv : (axialSplit 0).symm (t,planeProductCoordinates.symm
        (if j=0 then z.1+1 else z.1,if j=1 then z.2+1 else z.2))=
        (axialSplit 0).symm (t,planeProductCoordinates.symm z)+latticeVector (Pi.single j.succ (1 : ℤ)) := by
      rw [axialSplit_zero_symm,axialSplit_zero_symm]
      ext i
      fin_cases i <;> fin_cases j <;> simp [planeProductCoordinates_symm_apply,latticeVector,Pi.single_apply]
    dsimp only [g]
    rw [hv]
    exact hh
  have hx : ∀ y,Function.Periodic (fun x => g (x,y)) 1 := by
    intro y x
    simpa using hperiod 0 (x,y)
  have hy : ∀ x,Function.Periodic (fun y => g (x,y)) 1 := by
    intro x y
    simpa using hperiod 1 (x,y)
  convert periodic_plane_integral_translate hg (fun z => hb _) hx hy (-(1/2)) (-(1/2)) (c 1) (c 2) using 1; norm_num

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma centeredPlaneSection_integral {E : Set Torus} (hE : MeasurableSet E)
    {g : Cover → ℝ} (hg : Continuous g) (hp : ∀ m x,g (x+latticeVector m)=g x)
    (c : Cover) (t : ℝ) :
    (∫ z in centeredPlaneSection E c t,g (coordinateSectionPoint c t z))=
      axialSectionIntegral E 0 g t := by
  let f : Cover → ℝ := fun x => characteristic E (quotientMap x)*g x
  have hf : Measurable f := ((measurable_characteristic hE).comp measurable_quotientMap).mul hg.measurable
  have hfp : ∀ m x,f (x+latticeVector m)=f x := by
    intro m x
    simp [f,quotientMap_add,quotientMap_latticeVector,hp]
  obtain ⟨M,hM0,hM⟩ := periodic_bounded hg hp
  have hb : ∀ x,‖f x‖≤M := by
    intro x
    change ‖characteristic E (quotientMap x)*g x‖≤M
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (characteristic_bound E _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hM x)
  have he := centered_complex_integral_periodic hf hfp hb c t
  have hfun : (fun z => f (coordinateSectionPoint c t z))=
      ((fun z => quotientMap (coordinateSectionPoint c t z)) ⁻¹' E).indicator
        (fun z => g (coordinateSectionPoint c t z)) := by
    funext z
    by_cases hz : quotientMap (coordinateSectionPoint c t z)∈E <;> simp [f,characteristic,hz]
  have hms : MeasurableSet ((fun z : ℂ => quotientMap (coordinateSectionPoint c t z)) ⁻¹' E) :=
    hE.preimage (measurable_quotientMap.comp (coordinateSectionPoint_contDiff c t).continuous.measurable)
  rw [hfun] at he
  rw [setIntegral_indicator hms] at he
  exact he

lemma axialSectionIntegral_one {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3) (t : ℝ) :
    axialSectionIntegral E i (fun _ => 1) t=axialSectionArea E i t := by
  have hfun : (fun y : Plane => characteristic E (quotientMap ((axialSplit i).symm (t,y)))*(1 : ℝ))=
      ((fun y => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
    funext y
    by_cases hy : quotientMap ((axialSplit i).symm (t,y))∈E <;> simp [characteristic,hy]
  have hms : MeasurableSet ((fun y : Plane => quotientMap ((axialSplit i).symm (t,y))) ⁻¹' E) :=
    hE.preimage (measurable_quotientMap.comp ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))
  rw [axialSectionIntegral,hfun,setIntegral_indicator hms]
  simp [axialSectionArea,axialSection,integral_const,Measure.real]

lemma centeredPlaneSection_real_volume {E : Set Torus} (hE : MeasurableSet E) (c : Cover) (t : ℝ) :
    volume.real (centeredPlaneSection E c t)=axialSectionArea E 0 t := by
  have he := centeredPlaneSection_integral hE (g := fun _ => 1) continuous_const (fun _ _ => rfl) c t
  rw [axialSectionIntegral_one hE] at he
  simpa [integral_const,Measure.real] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma complexDet_le_norm_mul (u v : ℂ) : complexDet u v≤‖u‖*‖v‖ := by
  rw [complexDet_eq_im]
  exact (Complex.im_le_norm _).trans_eq (by simp)

lemma radialVelocity_continuous {r dr : ℝ → ℝ} (hr : Continuous r) (hd : Continuous dr) :
    Continuous (radialVelocity r dr) :=
  ((Complex.continuous_ofReal.comp hd).add
    ((Complex.continuous_ofReal.comp (continuous_const.mul hr)).mul continuous_const)).mul unitAngle_continuous

lemma radialVelocity_norm (r dr : ℝ → ℝ) (a : ℝ) :
    ‖radialVelocity r dr a‖=Real.sqrt ((dr a)^2+(2*Real.pi*r a)^2) := by
  rw [← radialVelocity_norm_sq,Real.sqrt_sq (norm_nonneg _)]

lemma axialSectionIntegral_radial_green {E : Set Torus} (hE : MeasurableSet E)
    {c : Cover} {t : ℝ} {r dr : ℝ → ℝ} (hr : ∀ a,HasDerivAt r (dr a) a)
    (hdc : Continuous dr) (hrp : Function.Periodic r 1) (hpos : ∀ a,0<r a)
    (he : centeredPlaneSection E c t=planarRadialRegion r)
    {F : Cover → Cover} (hF : AdmissibleField F) (ha : ∀ x,F x 0=0) :
    axialSectionIntegral E 0 (divergence F) t=
      ∫ a in (0 : ℝ)..1,complexDet (coordinatePlaneField F c t (radialCurve r a)) (radialVelocity r dr a) := by
  have hCF := coordinatePlaneField_contDiff hF.1 c t
  have hg := green_planarRadialRegion hr hdc hrp hpos (hCF.of_le (by simp))
  simp_rw [coordinatePlaneField_divergence (hF.1.differentiable (by simp)) ha] at hg
  rw [← he,centeredPlaneSection_integral hE (continuous_divergence hF.1) (divergence_periodic hF.2.1)] at hg
  exact hg

lemma axialSlicePerimeter_radial_le {E : Set Torus} (hE : MeasurableSet E)
    {c : Cover} {t : ℝ} {r dr : ℝ → ℝ} (hr : ∀ a,HasDerivAt r (dr a) a)
    (hdc : Continuous dr) (hrp : Function.Periodic r 1) (hpos : ∀ a,0<r a)
    (he : centeredPlaneSection E c t=planarRadialRegion r) :
    axialSlicePerimeter E 0 t≤ENNReal.ofReal (∫ a in (0 : ℝ)..1,Real.sqrt ((dr a)^2+(2*Real.pi*r a)^2)) := by
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun a => (hr a).continuousAt
  have hvc := radialVelocity_continuous hrc hdc
  have hcurve : Continuous (radialCurve r) := (Complex.continuous_ofReal.comp hrc).mul unitAngle_continuous
  apply axialSlicePerimeter_le
  intro F hF ha
  rw [axialSectionIntegral_radial_green hE hr hdc hrp hpos he hF ha]
  have hCF := (coordinatePlaneField_contDiff hF.1 c t).continuous.comp hcurve
  have hdet : Continuous (fun a => complexDet (coordinatePlaneField F c t (radialCurve r a)) (radialVelocity r dr a)) := by
    exact ((Complex.continuous_re.comp hCF).mul (Complex.continuous_im.comp hvc)).sub
      ((Complex.continuous_im.comp hCF).mul (Complex.continuous_re.comp hvc))
  have hspeed : Continuous (fun a => Real.sqrt ((dr a)^2+(2*Real.pi*r a)^2)) := by
    exact (hdc.pow 2 |>.add ((continuous_const.mul hrc).pow 2)).sqrt
  apply intervalIntegral.integral_mono_on (by norm_num) (hdet.intervalIntegrable _ _) (hspeed.intervalIntegrable _ _)
  intro a _
  rw [← radialVelocity_norm]
  apply (complexDet_le_norm_mul _ _).trans
  have hb : ‖coordinatePlaneField F c t (radialCurve r a)‖≤1 :=
    (coordinatePlaneProjection_norm_le _).trans (hF.2.2 _)
  simpa using mul_le_mul_of_nonneg_right hb (norm_nonneg (radialVelocity r dr a))

lemma axialSlicePerimeter_radial_eq_of_calibration {E : Set Torus} (hE : MeasurableSet E)
    {c : Cover} {t : ℝ} {r dr : ℝ → ℝ} (hr : ∀ a,HasDerivAt r (dr a) a)
    (hdc : Continuous dr) (hrp : Function.Periodic r 1) (hpos : ∀ a,0<r a)
    (he : centeredPlaneSection E c t=planarRadialRegion r)
    {F : Cover → Cover} (hF : AdmissibleField F) (ha : ∀ x,F x 0=0)
    (hflux : ∀ a∈Icc (0 : ℝ) 1,
      complexDet (coordinatePlaneField F c t (radialCurve r a)) (radialVelocity r dr a)=
        Real.sqrt ((dr a)^2+(2*Real.pi*r a)^2)) :
    axialSlicePerimeter E 0 t=ENNReal.ofReal (∫ a in (0 : ℝ)..1,Real.sqrt ((dr a)^2+(2*Real.pi*r a)^2)) := by
  apply le_antisymm (axialSlicePerimeter_radial_le hE hr hdc hrp hpos he)
  have hg := axialSectionIntegral_radial_green hE hr hdc hrp hpos he hF ha
  have hh : (∫ a in (0 : ℝ)..1,complexDet (coordinatePlaneField F c t (radialCurve r a)) (radialVelocity r dr a))=
      ∫ a in (0 : ℝ)..1,Real.sqrt ((dr a)^2+(2*Real.pi*r a)^2) := by
    apply intervalIntegral.integral_congr
    intro a ha'
    apply hflux a
    simpa using ha'
  rw [hh] at hg
  rw [← hg]
  exact axialSlicePerimeter_ge hF ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_radial_normal_positive {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {r : ℝ → ℝ} (hrb : ∀ a,0<r a ∧ r a<unitSquareScale a) {t : ℝ}
    (hb : ∀ a,quotientMap (coordinateSectionPoint (chamberCorner s) t (radialCurve r a))∈frontier (openRepresentative E))
    (a : ℝ) :
    0<⟪N (coordinateSectionPoint (chamberCorner s) t (radialCurve r a)),coordinatePlaneLift (radialCurve r a)⟫ := by
  have hg : complexSquareGauge (radialCurve r a)<1/2 := by
    have he : radialCurve r a=r a • unitAngle a := Complex.real_smul.symm
    rw [he,complexSquareGauge_smul (hrb a).1.le]
    have hh := (hrb a).2
    rw [unitSquareScale,lt_div_iff₀ (mul_pos (by norm_num) (complexSquareGauge_pos (unitAngle_ne_zero a)))] at hh
    nlinarith
  have hnz : radialCurve r a≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (hrb a).1.ne') (unitAngle_ne_zero a)
  exact isMinimizerAt_coordinate_plane_transverse hV hE hm hμ hN hp ha hs hsg hnz hg (hb a)

theorem isMinimizerAt_radial_slice_calibration {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {r dr : ℝ → ℝ} (hr : ∀ a,HasDerivAt r (dr a) a)
    (hrb : ∀ a,0<r a ∧ r a<unitSquareScale a) {t : ℝ}
    (hb : ∀ a,quotientMap (coordinateSectionPoint (chamberCorner s) t (radialCurve r a))∈frontier (openRepresentative E)) :
    ∃ F : Cover → Cover,AdmissibleField F ∧ (∀ x,F x 0=0) ∧
      ∀ a∈Icc (0 : ℝ) 1,
        complexDet (coordinatePlaneField F (chamberCorner s) t (radialCurve r a)) (radialVelocity r dr a)=
          Real.sqrt ((dr a)^2+(2*Real.pi*r a)^2) := by
  let x : ℝ → Cover := fun a => coordinateSectionPoint (chamberCorner s) t (radialCurve r a)
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun a => (hr a).continuousAt
  have hcurve : Continuous (radialCurve r) := (Complex.continuous_ofReal.comp hrc).mul unitAngle_continuous
  have hxc : Continuous x := (coordinateSectionPoint_contDiff _ _).continuous.comp hcurve
  let q : ℝ → ℝ := fun a => ‖coordinatePlaneProjection (N (x a))‖
  have hqc : Continuous q := (coordinatePlaneProjection.continuous.comp (hN.continuous.comp hxc)).norm
  have htrans (a) : 0<⟪N (x a),coordinatePlaneLift (radialCurve r a)⟫ :=
    isMinimizerAt_radial_normal_positive hV hE hm hμ hN hp ha hs hsg hrb hb a
  have hpos (a) : 0<q a := by
    apply norm_pos_iff.mpr
    intro hz
    have ht := htrans a
    rw [coordinatePlaneProjection_inner,hz] at ht
    simp at ht
  obtain ⟨k,hk,hlarge⟩ := compact_positive_scale hqc.continuousOn (fun a _ => hpos a)
  let F := axialNormalCalibration (fun y => k • N y) 0
  have hks : ContDiff ℝ (⊤ : ℕ∞) (fun y => k • N y) := hN.const_smul k
  have hkp : ∀ m y,k • N (y+latticeVector m)=k • N y := fun m y => congrArg (k • ·) (hp m y)
  refine ⟨F,axialNormalCalibration_admissible hks hkp 0,axialNormalCalibration_axis _ _,?_⟩
  intro a hac
  have hl : 1/4≤‖axialTangentPart 0 (k • N (x a))‖^2 := by
    rw [axialTangentPart_smul,norm_smul,Real.norm_eq_abs,abs_of_pos hk,← coordinatePlaneProjection_norm_tangent]
    exact hlarge a hac
  have hperp := isMinimizerAt_radial_curve_tangent hV hE hm hμ hN hp ha hr hb a
  have hdet : 0<complexDet (radialCurve r a) (radialVelocity r dr a) := by
    rw [complexDet_eq_im,radialCurve_area_integrand]
    have hpos := (hrb a).1
    positivity
  change complexDet (coordinatePlaneProjection (F (x a))) (radialVelocity r dr a)=_
  rw [scaled_axialCalibration_density hk hl hperp (htrans a) hdet,radialVelocity_norm]

theorem isMinimizerAt_radial_slice_length {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E))
    {t : ℝ} (ht : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2))
    (htE : quotientMap (coordinateSectionPoint (chamberCorner s) t 0)∈openRepresentative E) :
    ∃ r : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧ Function.Periodic r 1 ∧ (∀ a,0<r a) ∧
      axialSectionArea (openRepresentative E) 0 t=Real.pi*(∫ a in (0 : ℝ)..1,(r a)^2) ∧
      axialSlicePerimeter (openRepresentative E) 0 t=
        ENNReal.ofReal (∫ a in (0 : ℝ)..1,Real.sqrt ((deriv r a)^2+(2*Real.pi*r a)^2)) := by
  obtain ⟨r,hr,hrp,hrb,hbd,hphase,hcl⟩ := isMinimizerAt_smooth_radial_section
    hV hE hm hμ hN hp ha hs hsg hv1 hv2 ht htE
  have hpos := fun a => (hrb a).1
  have he := (planarRadialRegion_eq_actual_section hpos (fun a => (hrb a).2) hphase).symm
  have harea : axialSectionArea (openRepresentative E) 0 t=Real.pi*(∫ a in (0 : ℝ)..1,(r a)^2) := by
    rw [← centeredPlaneSection_real_volume (isOpen_openRepresentative E).measurableSet (chamberCorner s),he]
    exact real_volume_planarRadialRegion hr.continuous hrp hpos
  refine ⟨r,hr,hrp,hpos,harea,?_⟩
  have hb : ∀ a,quotientMap (coordinateSectionPoint (chamberCorner s) t (radialCurve r a))∈frontier (openRepresentative E) := by
    intro a
    simpa only [radialCurve,Complex.real_smul] using hbd a
  have hdr := fun a => (hr.differentiable (by simp) a).hasDerivAt
  obtain ⟨F,hF,hFa,hflux⟩ := isMinimizerAt_radial_slice_calibration hV hE hm hμ hN hp ha hs hsg hdr hrb hb
  exact axialSlicePerimeter_radial_eq_of_calibration (isOpen_openRepresentative E).measurableSet
    hdr (hr.continuous_deriv (by simp)) hrp hpos he hF hFa hflux

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_centered_section_empty {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {t : ℝ} (ht : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2))
    (htE : quotientMap (coordinateSectionPoint (chamberCorner s) t 0)∉openRepresentative E) :
    centeredPlaneSection (openRepresentative E) (chamberCorner s) t=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hsgc : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i := by
    intro x hx i
    exact (hsg x i ⟨hx.1,mem_iInter.mp hx.2 i⟩).le
  have hz1 : |z.re|≤1/2 := ((le_max_left |z.re| |z.im|).trans_lt hz.1).le
  have hz2 : |z.im|≤1/2 := ((le_max_right |z.re| |z.im|).trans_lt hz.1).le
  have hx : coordinateSectionPoint (chamberCorner s) t 0∈closedHalfBox (chamberCorner s) :=
    coordinateSectionPoint_mem_box ht (by norm_num)
  have hy : coordinateSectionPoint (chamberCorner s) t (complexFold z)∈closedHalfBox (chamberCorner s) :=
    coordinateSectionPoint_mem_box ht ⟨abs_nonneg _,abs_nonneg _,hz1,hz2⟩
  have hxy : ∀ i : Fin 3,coordinateSectionPoint (chamberCorner s) t 0 i≤
      coordinateSectionPoint (chamberCorner s) t (complexFold z) i := by
    intro i
    fin_cases i <;> simp [complexFold]
  have hyE : quotientMap (coordinateSectionPoint (chamberCorner s) t (complexFold z))∈openRepresentative E := by
    rw [← coordinateSectionPoint_fold]
    apply localChamberFold_preserves (fun i => openRepresentative_reflection_invariant hE i (hs i))
    exact hz.2
  exact htE (isMinimizerAt_chamber_open_downset hV hE hm hμ ha hsgc hs hx hy hxy hyE)

theorem isMinimizerAt_slice_isoperimetric {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E))
    {t : ℝ} (ht : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2)) :
    4*Real.pi*axialSectionArea (openRepresentative E) 0 t≤
      ((axialSlicePerimeter (openRepresentative E) 0 t).toReal)^2 := by
  by_cases htE : quotientMap (coordinateSectionPoint (chamberCorner s) t 0)∈openRepresentative E
  · obtain ⟨r,hr,hrp,hr0,harea,hper⟩ := isMinimizerAt_radial_slice_length
      hV hE hm hμ hN hp ha hs hsg hv1 hv2 ht htE
    have hi := radial_curve_isoperimetric (fun a => (hr.differentiable (by simp) a).hasDerivAt)
      (hr.continuous_deriv (by simp)) hrp hr0
    have hn : 0≤∫ a in (0 : ℝ)..1,Real.sqrt ((deriv r a)^2+(2*Real.pi*r a)^2) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun a _ => Real.sqrt_nonneg _)
    rw [harea,hper,ENNReal.toReal_ofReal hn]
    convert hi using 1; ring
  · have he := isMinimizerAt_centered_section_empty hV hE hm hμ ha hs hsg ht htE
    rw [← centeredPlaneSection_real_volume (isOpen_openRepresentative E).measurableSet (chamberCorner s),he]
    simp [Measure.real]

theorem isMinimizerAt_slice_sqrt_isoperimetric {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E))
    {t : ℝ} (ht : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2)) :
    ENNReal.ofReal (2*Real.sqrt (Real.pi*axialSectionArea (openRepresentative E) 0 t))≤
      axialSlicePerimeter (openRepresentative E) 0 t := by
  have hi := isMinimizerAt_slice_isoperimetric hV hE hm hμ hN hp ha hs hsg hv1 hv2 ht
  have h0 := mul_nonneg Real.pi_pos.le (axialSectionArea_nonneg (openRepresentative E) 0 t)
  have hsqrt := Real.sq_sqrt h0
  have hb : 2*Real.sqrt (Real.pi*axialSectionArea (openRepresentative E) 0 t)≤
      (axialSlicePerimeter (openRepresentative E) 0 t).toReal := by
    nlinarith [Real.sqrt_nonneg (Real.pi*axialSectionArea (openRepresentative E) 0 t),
      ENNReal.toReal_nonneg (a := axialSlicePerimeter (openRepresentative E) 0 t)]
  exact (ENNReal.ofReal_le_ofReal hb).trans ENNReal.ofReal_toReal_le

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_smooth_radial_section_of_level_vertices {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {t : ℝ} (ht : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2))
    (hv1 : quotientMap (coordinateSectionPoint (chamberCorner s) t (1/2 : ℂ))∉closure (openRepresentative E))
    (hv2 : quotientMap (coordinateSectionPoint (chamberCorner s) t ((1/2 : ℂ)*Complex.I))∉closure (openRepresentative E))
    (htE : quotientMap (coordinateSectionPoint (chamberCorner s) t 0)∈openRepresentative E) :
    ∃ r : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧ Function.Periodic r 1 ∧
      (∀ a,0<r a ∧ r a<unitSquareScale a) ∧
      (∀ a,quotientMap (coordinateSectionPoint (chamberCorner s) t (r a • unitAngle a))∈frontier (openRepresentative E)) ∧
      (∀ a u,0≤u → u≤unitSquareScale a →
        (quotientMap (coordinateSectionPoint (chamberCorner s) t (u • unitAngle a))∈openRepresentative E ↔ u<r a)) ∧
      (∀ a u,0≤u → u≤unitSquareScale a →
        (quotientMap (coordinateSectionPoint (chamberCorner s) t (u • unitAngle a))∈closure (openRepresentative E) ↔ u≤r a)) := by
  let c := chamberCorner s
  let x := coordinateSectionPoint c t 0
  let y : ℝ → Cover := fun a => coordinateSectionPoint c t (unitSquareEnd a)
  have hx : x∈closedHalfBox c := coordinateSectionPoint_mem_box ht (by norm_num)
  have hy (a) : y a∈closedHalfBox c := by
    have hh := unitSquareEnd_coordinates a
    exact coordinateSectionPoint_mem_box ht ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
  have hxy (a) (i : Fin 3) : x i≤y a i := by
    have hh := unitSquareEnd_coordinates a
    fin_cases i <;> simp [x,y] <;> first | exact hh.1 | exact hh.2.1
  have hsgc : ∀ z : Cover,quotientMap z∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N z i := by
    intro z hz i
    exact (hsg z i ⟨hz.1,mem_iInter.mp hz.2 i⟩).le
  have hv1box : coordinateSectionPoint c t (1/2 : ℂ)∈closedHalfBox c :=
    coordinateSectionPoint_mem_box ht (by norm_num)
  have hv2box : coordinateSectionPoint c t ((1/2 : ℂ)*Complex.I)∈closedHalfBox c :=
    coordinateSectionPoint_mem_box ht (by norm_num)
  have hyE (a) : quotientMap (y a)∉closure (openRepresentative E) := by
    intro hya
    have hh := unitSquareEnd_coordinates a
    rcases hh.2.2.2.2 with he|he
    · apply hv1
      apply isMinimizerAt_chamber_closed_downset hV hE hm hμ ha hsgc hs hv1box (hy a) _ hya
      intro i
      fin_cases i <;> simp [y,c,he]
      exact hh.2.1
    · apply hv2
      apply isMinimizerAt_chamber_closed_downset hV hE hm hμ ha hsgc hs hv2box (hy a) _ hya
      intro i
      fin_cases i <;> simp [y,c,he]
      exact hh.1
  obtain ⟨q,hqc,hq,hb,ho,hcl,hf⟩ := isMinimizerAt_chamber_continuous_exit
    hV hE hm hμ hN hp ha hs hsg (continuous_const (y := x))
      (show Continuous y from (coordinateSectionPoint_contDiff c t).continuous.comp unitSquareEnd_continuous)
      (fun _ => hx) hy hxy (fun _ => htE) hyE
  have hqp : Function.Periodic q 1 := by
    intro a
    apply (hf a (q (a+1)) ⟨(hq _).1.le,(hq _).2.le⟩).mp
    simpa only [y,Function.comp_def,unitSquareEnd_periodic a] using hb (a+1)
  let r : ℝ → ℝ := fun a => q a*unitSquareScale a
  have hrc : Continuous r := hqc.mul unitSquareScale_continuous
  have hr (a) : 0<r a ∧ r a<unitSquareScale a := by
    exact ⟨mul_pos (hq a).1 (unitSquareScale_pos a),
      by simpa using mul_lt_mul_of_pos_right (hq a).2 (unitSquareScale_pos a)⟩
  have hsame (a u : ℝ) : chamberSegment x (y a) (u/unitSquareScale a)=
      coordinateSectionPoint c t (u • complexFold (unitAngle a)) := by
    rw [coordinateSectionPoint_segment]
    simp only [unitSquareEnd,smul_smul]
    rw [div_mul_cancel₀ _ (unitSquareScale_pos a).ne']
  have hreflect (F : Set Torus) (hF : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F) (a u : ℝ) (hu : 0≤u) :
      quotientMap (coordinateSectionPoint c t (u • complexFold (unitAngle a)))∈F ↔
        quotientMap (coordinateSectionPoint c t (u • unitAngle a))∈F := by
    rw [← complexFold_smul hu]
    rw [← coordinateSectionPoint_fold s t (u • unitAngle a)]
    exact localChamberFold_mem_iff hF s x _
  have hsO := fun i => openRepresentative_reflection_invariant hE i (hs i)
  have hsC := reflection_invariant_closure hsO
  have hsB := fun i => frontier_reflection_invariant hE i (hs i)
  have hbr (a) : quotientMap (coordinateSectionPoint c t (r a • unitAngle a))∈frontier (openRepresentative E) := by
    apply (hreflect _ hsB a (r a) (hr a).1.le).mp
    rw [← hsame]
    have hh : r a/unitSquareScale a=q a := by dsimp [r]; rw [mul_div_cancel_right₀ _ (unitSquareScale_pos a).ne']
    rw [hh]
    exact hb a
  refine ⟨r,?_,fun a => by simp only [r,hqp a,unitSquareScale_periodic a],hr,hbr,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro a
    let γ : ℝ × ℝ → Cover := fun p => coordinateSectionPoint c t (p.2 • unitAngle p.1)
    have hγ : ContDiff ℝ (⊤ : ℕ∞) γ := (coordinateSectionPoint_contDiff c t).comp
      (contDiff_snd.smul (unitAngle_contDiff.comp contDiff_fst))
    have hder : HasDerivAt (fun u => γ (a,u)) (coordinatePlaneLift (unitAngle a)) (r a) := by
      have hh := coordinatePlaneLift.hasFDerivAt.comp_hasDerivAt (r a)
        ((hasDerivAt_id (r a)).smul_const (unitAngle a))
      simpa only [γ,coordinateSectionPoint,Function.comp_def,one_smul,id_eq] using hh.const_add (c+(t-c 0) • EuclideanSpace.single 0 1)
    have hz : r a • unitAngle a≠0 := smul_ne_zero (hr a).1.ne' (unitAngle_ne_zero a)
    have hgauge : complexSquareGauge (r a • unitAngle a)<1/2 := by
      rw [complexSquareGauge_smul (hr a).1.le]
      have hscl : unitSquareScale a*complexSquareGauge (unitAngle a)=1/2 := by
        dsimp [unitSquareScale]
        field_simp [(complexSquareGauge_pos (unitAngle_ne_zero a)).ne']
      calc
        r a*complexSquareGauge (unitAngle a)<unitSquareScale a*complexSquareGauge (unitAngle a) :=
          mul_lt_mul_of_pos_right (hr a).2 (complexSquareGauge_pos (unitAngle_ne_zero a))
        _=1/2 := hscl
    have hpos := isMinimizerAt_coordinate_plane_transverse hV hE hm hμ hN hp ha hs hsg hz hgauge (hbr a)
    have hne : ⟪N (γ (a,r a)),coordinatePlaneLift (unitAngle a)⟫≠0 := by
      intro he
      rw [map_smul,real_inner_smul_right] at hpos
      change 0<r a*⟪N (γ (a,r a)),coordinatePlaneLift (unitAngle a)⟫ at hpos
      rw [he,mul_zero] at hpos
      exact lt_irrefl _ hpos
    exact isMinimizerAt_smooth_boundary_exit hV hE hm hμ hN hp ha hγ.contDiffAt
      hrc.continuousAt (Filter.Eventually.of_forall hbr) hder hne
  · intro a u hu hule
    rw [← hreflect _ hsO a u hu,← hsame]
    rw [ho a (u/unitSquareScale a) ⟨div_nonneg hu (unitSquareScale_pos a).le,
      (div_le_one (unitSquareScale_pos a)).mpr hule⟩]
    exact div_lt_iff₀ (unitSquareScale_pos a)
  · intro a u hu hule
    rw [← hreflect _ hsC a u hu,← hsame]
    rw [hcl a (u/unitSquareScale a) ⟨div_nonneg hu (unitSquareScale_pos a).le,
      (div_le_one (unitSquareScale_pos a)).mpr hule⟩]
    exact div_le_iff₀ (unitSquareScale_pos a)

end CubicTorus

end
end

end OAI
