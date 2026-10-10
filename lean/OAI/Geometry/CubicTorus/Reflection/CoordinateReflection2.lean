import Mathlib
import OAI.Geometry.CubicTorus.Curvature.SurfaceJacobiLocalization

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_jensen_projection {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    (49/50 : ℝ)*(μ.mass : ℝ)*axialFluxWeight μ i+(14/25 : ℝ)*
      (axialSectionArea (openRepresentative E) i (chamberCorner s i)-
        axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2))≤(μ.mass : ℝ) := by
  have hQ := isMinimizerAt_axial_flux_nonneg hV hE hm hH i
    (isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i)
  have hg : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioo (0 : ℝ) 1),
      (7/25 : ℝ)≤ sliceJensenG (axialJensenFlux (openRepresentative E) μ H V i t/
        (axialCirclePerimeter (openRepresentative E) i t).toReal) := by
    apply Eventually.of_forall
    intro t
    apply (sliceJensenG_bounds _).1
    apply div_nonneg _ ENNReal.toReal_nonneg
    simpa only [axialJensenFlux,axialCircleArea_coe] using hQ t
  have hJ := (isMinimizerAt_area_coordinate_jensen hV hE hm hμ hN hp ha hs hsg hH i
    (γ := fun _ => 7/25) measurable_const (fun _ => by norm_num) hg).2
  have hanti := isMinimizerAt_antitoneOn_axialSectionArea hV hE hm hμ hN hp ha hs hsg i
  have hends := hanti (show chamberCorner s i∈Icc (chamberCorner s i) (chamberCorner s i+1/2) from
      ⟨le_rfl,by linarith⟩)
    (show chamberCorner s i+1/2∈Icc (chamberCorner s i) (chamberCorner s i+1/2) from ⟨by linarith,le_rfl⟩)
    (by linarith)
  rw [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hends),smul_eq_mul] at hJ
  linarith

theorem isMinimizerAt_missing_axis_area_jensen {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (hv : quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E))
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγ0 : ∀ v,0≤γ v)
    (hγJ : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      γ (axialSectionArea (openRepresentative E) i t)≤
        sliceJensenG ((H/2)*axialSectionArea (openRepresentative E) i t/
          ((axialCirclePerimeter (openRepresentative E) i t).toReal/2))) :
    0<H ∧ IntegrableOn γ (Ioo 0 (axialSectionArea (openRepresentative E) i (chamberCorner s i))) ∧
      (49/50 : ℝ)*(H/2)*V+
        (∫ v in Ioo 0 (axialSectionArea (openRepresentative E) i (chamberCorner s i)),γ v)≤
          (μ.mass : ℝ)/2 := by
  obtain ⟨hHpos,hflux,htop,hbottom,hQ⟩ :=
    isMinimizerAt_missing_axis_flux hV hE hm hμ hN hp ha hs hsg hH i hv
  have hγJ' : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      γ (axialSectionArea (openRepresentative E) i t)≤
        sliceJensenG (axialJensenFlux (openRepresentative E) μ H V i t/
          (axialCirclePerimeter (openRepresentative E) i t).toReal) := by
    filter_upwards [hγJ] with t ht
    rw [hQ,axialCircleArea_coe]
    convert ht using 1
    congr 1
    ring
  obtain ⟨hi,hJ⟩ := isMinimizerAt_area_coordinate_jensen hV hE hm hμ hN hp ha hs hsg hH i hγ hγ0 hγJ'
  rw [htop] at hi hJ
  refine ⟨hHpos,hi,?_⟩
  have hf : (49/50 : ℝ)*(μ.mass : ℝ)*axialFluxWeight μ i=(49/50 : ℝ)*(H*V) := by
    rw [mul_assoc,hflux]
  rw [hf] at hJ
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_chamber_smooth_exit {A : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
    {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {x y : A → Cover} (hxc : ContDiff ℝ (⊤ : ℕ∞) x) (hyc : ContDiff ℝ (⊤ : ℕ∞) y)
    (hx : ∀ a,x a∈closedHalfBox (chamberCorner s))
    (hy : ∀ a,y a∈closedHalfBox (chamberCorner s))
    (hxy : ∀ a i,x a i≤y a i)
    (hxE : ∀ a,quotientMap (x a)∈openRepresentative E)
    (hyE : ∀ a,quotientMap (y a)∉closure (openRepresentative E)) :
    ∃ r : A → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧ (∀ a,r a∈Ioo (0 : ℝ) 1) ∧
      (∀ a,quotientMap (chamberSegment (x a) (y a) (r a))∈frontier (openRepresentative E)) ∧
      (∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈openRepresentative E ↔ t<r a)) ∧
      (∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈closure (openRepresentative E) ↔ t≤r a)) ∧
      ∀ a t,t∈Icc (0 : ℝ) 1 → (quotientMap (chamberSegment (x a) (y a) t)∈frontier (openRepresentative E) ↔ t=r a) := by
  obtain ⟨r,hrc,hr,hb,ho,hcl,hf⟩ := isMinimizerAt_chamber_continuous_exit
    hV hE hm hμ hN hp ha hs hsg hxc.continuous hyc.continuous hx hy hxy hxE hyE
  refine ⟨r,?_,hr,hb,ho,hcl,hf⟩
  rw [contDiff_iff_contDiffAt]
  intro a
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (fun p : A × ℝ => chamberSegment (x p.1) (y p.1) p.2) :=
    (hxc.comp contDiff_fst).add (contDiff_snd.smul
      ((hyc.comp contDiff_fst).sub (hxc.comp contDiff_fst)))
  have hd : HasDerivAt (fun t => chamberSegment (x a) (y a) t) (y a-x a) (r a) := by
    simpa only [chamberSegment,one_smul,id_eq] using
      ((hasDerivAt_id (r a)).smul_const (y a-x a)).const_add (x a)
  have hne : x a≠y a := by
    intro he
    exact hyE a (he ▸ subset_closure (hxE a))
  exact isMinimizerAt_smooth_boundary_exit hV hE hm hμ hN hp ha hγ.contDiffAt (hrc.continuousAt)
    (Filter.Eventually.of_forall hb) hd
    (chamberSegment_normal_positive hsg (hx a) (hy a) (hxy a) hne (hr a) (hb a)).ne'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_endpoint_slice_length {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E))
    (hc : quotientMap (chamberCorner s)∈openRepresentative E) :
    ∃ r : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧ Function.Periodic r 1 ∧ (∀ a,0<r a) ∧
      axialSectionArea (openRepresentative E) 0 (chamberCorner s 0)=Real.pi*(∫ a in (0 : ℝ)..1,(r a)^2) ∧
      axialSlicePerimeter (openRepresentative E) 0 (chamberCorner s 0)=
        ENNReal.ofReal (∫ a in (0 : ℝ)..1,Real.sqrt ((deriv r a)^2+(2*Real.pi*r a)^2)) := by
  have ht : chamberCorner s 0∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2) := ⟨le_rfl,by linarith⟩
  have htE : quotientMap (coordinateSectionPoint (chamberCorner s) (chamberCorner s 0) 0)∈openRepresentative E := by
    simpa [coordinateSectionPoint] using hc
  obtain ⟨r,hr,hrp,hrb,hbd,hphase,hcl⟩ := isMinimizerAt_smooth_radial_section
    hV hE hm hμ hN hp ha hs hsg hv1 hv2 ht htE
  have hpos := fun a => (hrb a).1
  have he := (planarRadialRegion_eq_actual_section hpos (fun a => (hrb a).2) hphase).symm
  have harea : axialSectionArea (openRepresentative E) 0 (chamberCorner s 0)=
      Real.pi*(∫ a in (0 : ℝ)..1,(r a)^2) := by
    rw [← centeredPlaneSection_real_volume (isOpen_openRepresentative E).measurableSet (chamberCorner s),he]
    exact real_volume_planarRadialRegion hr.continuous hrp hpos
  refine ⟨r,hr,hrp,hpos,harea,?_⟩
  have hb : ∀ a,quotientMap (coordinateSectionPoint (chamberCorner s) (chamberCorner s 0) (radialCurve r a))∈frontier (openRepresentative E) := by
    intro a
    simpa only [radialCurve,Complex.real_smul] using hbd a
  have hg := isMinimizerAt_endpoint_radial_green hV hE hm hμ hN hp ha hs hsg
    (fun a => (hr.differentiable (by simp) a).hasDerivAt) (hr.continuous_deriv (by simp)) hrp hrb hb
  have hF := axialNormalCalibration_admissible hN hp 0
  rw [← he,centeredPlaneSection_integral (isOpen_openRepresentative E).measurableSet
    (continuous_divergence hF.1) (divergence_periodic hF.2.1)] at hg
  have hcal := isMinimizerAt_axial_endpoint_calibration hV hE hm hμ hN hp ha hs hsg hH 0 (s 0)
  have hper := isMinimizerAt_axial_endpoint_perimeter hV hE hm hμ hN hp ha hs hsg hH 0 (s 0)
  change axialSectionIntegral (openRepresentative E) 0 (divergence (axialNormalCalibration N 0))
    (chamberCorner s 0)=_ at hcal
  change axialSlicePerimeter (openRepresentative E) 0 (chamberCorner s 0)=_ at hper
  rw [hper,← hcal,hg]

theorem isMinimizerAt_endpoint_slice_isoperimetric {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∉closure (openRepresentative E))
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∉closure (openRepresentative E))
    (hc : quotientMap (chamberCorner s)∈openRepresentative E) :
    4*Real.pi*axialSectionArea (openRepresentative E) 0 (chamberCorner s 0)≤
      ((axialSlicePerimeter (openRepresentative E) 0 (chamberCorner s 0)).toReal)^2 := by
  obtain ⟨r,hr,hrp,hr0,harea,hper⟩ := isMinimizerAt_endpoint_slice_length
    hV hE hm hμ hN hp ha hs hsg hH hv1 hv2 hc
  have hi := radial_curve_isoperimetric (fun a => (hr.differentiable (by simp) a).hasDerivAt)
    (hr.continuous_deriv (by simp)) hrp hr0
  have hn : 0≤∫ a in (0 : ℝ)..1,Real.sqrt ((deriv r a)^2+(2*Real.pi*r a)^2) :=
    intervalIntegral.integral_nonneg (by norm_num) (fun a _ => Real.sqrt_nonneg _)
  rw [harea,hper,ENNReal.toReal_ofReal hn]
  convert hi using 1
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma fourCorner_zero_curvature_impossible {A b top bottom : ℝ}
    (hA0 : 0≤A) (hA : A≤1) (hb0 : 0<b) (hb : b≤1)
    (ht0 : 0≤top) (hs1 : bottom≤1)
    (ht : Real.sqrt (Real.pi*top)≤A*b)
    (hs : Real.sqrt (Real.pi*(1-bottom))≤A*b)
    (hdiff : bottom-top≤A*Real.sqrt (1-b)) : False := by
  let d := Real.sqrt (1-b)
  have hd0 : 0≤d := Real.sqrt_nonneg _
  have hd2 : d^2=1-b := Real.sq_sqrt (by linarith)
  have hd1 : d<1 := by nlinarith
  have hsqt : Real.pi*top≤(A*b)^2 := by
    have hh := sq_le_sq₀ (Real.sqrt_nonneg (Real.pi*top)) (mul_nonneg hA0 hb0.le) |>.mpr ht
    rwa [Real.sq_sqrt (mul_nonneg Real.pi_pos.le ht0)] at hh
  have hsqs : Real.pi*(1-bottom)≤(A*b)^2 := by
    have hh := sq_le_sq₀ (Real.sqrt_nonneg (Real.pi*(1-bottom))) (mul_nonneg hA0 hb0.le) |>.mpr hs
    rwa [Real.sq_sqrt (mul_nonneg Real.pi_pos.le (by linarith))] at hh
  have hAd : A*d≤d := by nlinarith
  have hAb : (A*b)^2≤b^2 := by
    apply (sq_le_sq₀ (mul_nonneg hA0 hb0.le) hb0.le).mpr
    nlinarith
  have hnec : Real.pi≤Real.pi*d+2*b^2 := by
    have hdrop : bottom-top≤d := le_trans hdiff hAd
    have hp := mul_le_mul_of_nonneg_left hdrop Real.pi_pos.le
    nlinarith only [hsqt,hsqs,hAb,hp]
  have hf : (1-d)*(1+d)^2≤5/4 := by
    have hd3 : 0≤d^3 := pow_nonneg hd0 3
    nlinarith [sq_nonneg (d-1/2)]
  have hbr : 0<3-2*((1-d)*(1+d)^2) := by linarith
  have hprod := mul_pos (sub_pos.mpr hd1) hbr
  have hid : (1-d)*(3-2*((1-d)*(1+d)^2))=3*(1-d)-2*(1-d^2)^2 := by ring
  rw [hid,show 1-d^2=b by linarith] at hprod
  have hpi : 3<Real.pi := Real.pi_gt_three
  have hpi' := mul_lt_mul_of_pos_right hpi (sub_pos.mpr hd1)
  nlinarith only [hprod,hpi',hnec]

theorem isMinimizerAt_four_corner_multiplier_ne_zero {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {c : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if c i then 0 else 1/2) →0<N x i)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (hw : ∀ i : Fin 3,axialFluxWeight μ i<1)
    (ht1 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (ht2 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E)
    (hb1 : quotientMap (chamberVertex c (fun j => decide (j=1)))∈openRepresentative E)
    (hb2 : quotientMap (chamberVertex c (fun j => decide (j=2)))∈openRepresentative E) : H≠0 := by
  intro hHz
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  obtain ⟨hA,_,hA1⟩ := isMinimizerAt_halfMass_competitor_bounds hV hm hμ
  have hr0 := axialSectionArea_nonneg (openRepresentative E) 0 (chamberCorner c 0+1/2)
  have hs1 := axialSectionArea_le_one (openRepresentative E) 0 (chamberCorner c 0)
  have ht := isMinimizerAt_two_missing_vertices_top_flux hV' hE hm hμ hN hp ha hs hsg hH ht1 ht2
  have hb := isMinimizerAt_two_occupied_vertices_bottom_flux hV' hE hm hμ hN hp ha hs hsg hH hb1 hb2
  simp only [hHz,zero_div,zero_mul,add_zero] at ht hb
  have hmass : 0<(μ.mass : ℝ) := by linarith
  have hsum := sum_axialFluxWeight μ hmass.ne'
  rw [Fin.sum_univ_three] at hsum
  have hb0 : 0<axialFluxWeight μ 0 := by linarith [hw 1,hw 2]
  have hproj := axialProjection_bound μ 0
  rw [isMinimizerAt_axial_endFlux hV' hE hm hμ hN hp ha hs hsg hH 0] at hproj
  apply fourCorner_zero_curvature_impossible hA.le hA1 hb0 (hw 0).le hr0 hs1 ht hb
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nonstandard_toroidal_or_corner
    {V : ℝ} (hV : V∈Ioo 0 (1/2)) {E : Set Torus}
    (hmE : IsMinimizerAt V E) (hnstd : ¬SmallStandardRegion V E) :
    ∃ G : Set Torus,MeasurableSet G ∧ IsMinimizerAt V G ∧ ¬SmallStandardRegion V G ∧
      ((∃ (c : Cover) (r : ℝ × ℝ → ℝ),TrueRadialTube G c r ∧
        Nonempty ((AddCircle (1 : ℝ) × AddCircle (1 : ℝ)) ≃ₜ
          ↥(frontier (openRepresentative G)))) ∨
      ∃ (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
        (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x)
        (c : Fin 3 → Bool) (H : ℝ) (k : Fin 3),
        IsPreconnected (frontier (openRepresentative G)) ∧ IsNormalMeasure G μ ∧
        (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
        (∀ j : Fin 3,coordinateReflection j ⁻¹' G =ᵐ[torusVolume] G) ∧
        (∀ (x : Cover) (j : Fin 3),
          quotientMap x∈frontier (openRepresentative G)∩coordinateHalf j (if c j then 0 else 1/2) → 0<N x j) ∧
        (∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
          H*directionalFlux G D.coordinate D.function) ∧
        (∑ j : Fin 3,axialFluxWeight μ j)=2 ∧
        (∀ j : Fin 3,0≤axialFluxWeight μ j ∧ axialFluxWeight μ j<1) ∧
        (∀ j : Fin 3,j≠k → quotientMap (chamberVertex c (fun l => decide (l=j)))∈openRepresentative G) ∧
        (∀ j : Fin 3,quotientMap (chamberVertex c (fun l => decide (l≠j)))∉closure (openRepresentative G))) := by
  classical
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  obtain ⟨v,F,μ,N,hN,hp,c,H,hF,he,hm,hcon,hμ,ha,hs,hsg,hH,_,hws,hw,hvi,_⟩ :=
    isMinimizerAt_nonstandard_section_system ⟨hV.1,hV.2.le⟩ hmE hnstd
  have hnF : ¬SmallStandardRegion V F := fun h => hnstd (smallStandardRegion_of_translated he h)
  obtain ⟨i,hi⟩ := hvi
  have hiO : quotientMap (chamberVertex c (fun j => decide (j=i)))∈openRepresentative F :=
    mem_open_of_mem_closure_not_frontier (isOpen_openRepresentative F) hi
      (isMinimizerAt_reflection_vertex_excluded hV' hF hm hμ hN hp ha hs
        (chamberVertex_sine_zero c _))
  by_cases hu : ∀ j : Fin 3,
      quotientMap (chamberVertex c (fun l => decide (l=j)))∈openRepresentative F → j=i
  · obtain ⟨hzero,_,hdown⟩ := isMinimizerAt_chamber_vertex_order hV' hF hm hμ ha
      (fun x hx j => (hsg x j ⟨hx.1,mem_iInter.mp hx.2 j⟩).le) hs
    have hv := bool_vertex_two_point_ideal hzero hdown i hiO hu
    obtain ⟨e,r,hr⟩ := isMinimizerAt_two_vertices_smooth_tube hV' hF hm hμ hN hp ha hs hsg i hv
    refine ⟨torusCoordinatePermute e ⁻¹' F,(torusCoordinatePermute e).continuous.measurable hF,
      isMinimizerAt_coordinatePermute hm e,?_,Or.inl ⟨chamberCorner (c ∘ e.symm),r,hr,hr.homeomorphic_torus⟩⟩
    exact fun h => hnF (smallStandardRegion_of_coordinatePermute e h)
  · push Not at hu
    obtain ⟨j,hj,hji⟩ := hu
    obtain ⟨k,hki,hkj⟩ : ∃ k : Fin 3,k≠i ∧ k≠j := by
      fin_cases i <;> fin_cases j <;> try contradiction
      all_goals first | exact ⟨0,by decide,by decide⟩ | exact ⟨1,by decide,by decide⟩ | exact ⟨2,by decide,by decide⟩
    refine ⟨F,hF,hm,hnF,Or.inr ⟨μ,N,hN,hp,c,H,k,hcon,hμ,ha,hs,hsg,hH,hws,hw,?_,?_⟩⟩
    · intro l hl
      have hli : l=i ∨ l=j := by omega
      rcases hli with rfl|rfl
      · exact hiO
      · exact hj
    · exact isMinimizerAt_smaller_side_double_vertices_vacant hV hF hm hμ hN hp ha hs hsg hH

end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus

theorem secondEndpoint_missing_curvature_scalar_witness :
    ∃ A h r s b : ℝ,
      0 < A  ∧  A ≤ Real.sqrt (Real.pi*(1/Real.pi))  ∧  A ≤ 1  ∧  0 < h  ∧
      0 < r  ∧  r ≤ 1/Real.pi  ∧  1/Real.pi ≤ s  ∧  s ≤ 1  ∧  2/3 ≤ b  ∧  b < 1  ∧
      Real.sqrt (Real.pi*r) ≤ A*b-h*(1/Real.pi-r)  ∧
      Real.sqrt (Real.pi*(1-s)) ≤ A*b+h*(s-1/Real.pi)  ∧
      s-r ≤ A*Real.sqrt (1-b)  ∧  Real.pi < h^2*A := by
  have hp0 := Real.pi_pos
  have hpl : (31/10 : ℝ) < Real.pi := by linarith only [Real.pi_gt_d2]
  have hpu : Real.pi < (22/7 : ℝ) := by linarith only [Real.pi_lt_d4]
  have hpf : Real.pi < 4 := Real.pi_lt_four
  have hv0 : 0 < (1 : ℝ)/Real.pi := by positivity
  have hvu : (1 : ℝ)/Real.pi < 10/31 := by
    apply (div_lt_iff₀ hp0).mpr
    nlinarith only [hpl]
  have hvl : (1/10000 : ℝ) < 1/Real.pi := by
    apply (lt_div_iff₀ hp0).mpr
    nlinarith only [hpf]
  have htop : Real.sqrt (Real.pi*(1/10000)) ≤ (1/50 : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith only [hpf]
  have hbot : Real.sqrt (Real.pi*(1-(4/7 : ℝ))) ≤ (758/651 : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith only [hpu]
  have hdrop : (4/7 : ℝ)-(1/10000) ≤ Real.sqrt (1-(2/3 : ℝ)) := by
    apply (Real.le_sqrt (by norm_num) (by norm_num)).2
    norm_num
  refine ⟨1,2,1/10000,4/7,2/3,by norm_num,?_,by norm_num,by norm_num,
    by norm_num,hvl.le,by linarith only [hvu],by norm_num,le_rfl,by norm_num,?_,?_,?_,?_⟩
  · rw [mul_one_div_cancel hp0.ne',Real.sqrt_one]
  · nlinarith only [htop,hvu]
  · nlinarith only [hbot,hvu]
  · simpa only [one_mul] using hdrop
  · simpa only [one_mul, mul_one, show (2 : ℝ)^2=4 by norm_num] using hpf

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def firstReflection : Cover ≃ₗᵢ[ℝ] Cover :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i : Fin 3 ↦
    if i=0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] lemma firstReflection_apply (x : Cover) (i : Fin 3) :
    firstReflection x i=if i=0 then -x i else x i := by
  simp only [firstReflection,LinearIsometryEquiv.piLpCongrRight_apply,WithLp.ofLp_toLp]
  split_ifs <;> rfl

@[simp] lemma firstReflection_involutive (x : Cover) :
    firstReflection (firstReflection x)=x := by
  ext i
  simp only [firstReflection_apply]
  split_ifs <;> simp

lemma firstReflection_symm : firstReflection.symm=firstReflection := by
  apply LinearIsometryEquiv.ext
  intro x
  apply firstReflection.injective
  rw [LinearIsometryEquiv.apply_symm_apply,firstReflection_involutive]

def torusFirstReflection : Torus ≃ᵢ Torus where
  toFun x := WithLp.toLp 2 (fun i ↦ if i=0 then -x i else x i)
  invFun x := WithLp.toLp 2 (fun i ↦ if i=0 then -x i else x i)
  left_inv x := by ext i; dsimp; split_ifs <;> simp
  right_inv x := by ext i; dsimp; split_ifs <;> simp
  isometry_toFun x y := by
    rw [PiLp.edist_eq_of_L2,PiLp.edist_eq_of_L2]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp
    split_ifs <;> simp

@[simp] lemma torusFirstReflection_apply (x : Torus) (i : Fin 3) :
    torusFirstReflection x i=if i=0 then -x i else x i := rfl

@[simp] lemma torusFirstReflection_involutive (x : Torus) :
    torusFirstReflection (torusFirstReflection x)=x := by
  exact torusFirstReflection.symm_apply_apply x

lemma firstReflection_quotient (x : Cover) :
    quotientMap (firstReflection x)=torusFirstReflection (quotientMap x) := by
  ext i
  simp only [quotientMap,WithLp.ofLp_toLp,firstReflection_apply,torusFirstReflection_apply]
  split_ifs <;> simp

lemma torusFirstReflection_measurePreserving :
    MeasurePreserving torusFirstReflection torusVolume torusVolume := by
  let f : ProductTorus → ProductTorus := fun x i ↦ if i=0 then -x i else x i
  have hf : MeasurePreserving f volume volume := by
    rw [volume_pi]
    apply measurePreserving_pi (fun _ : Fin 3 ↦ (volume : Measure (AddCircle (1 : ℝ)) ))
      (fun _ : Fin 3 ↦ (volume : Measure (AddCircle (1 : ℝ))))
      (f := fun i x ↦ if i=0 then -x else x)
    intro i
    by_cases hi : i=0
    · simp only [hi,ite_true]
      exact Measure.measurePreserving_neg (volume : Measure (AddCircle (1 : ℝ)))
    · simp only [hi,ite_false]
      exact MeasurePreserving.id _
  exact product_to_torus_measurePreserving.comp (hf.comp torus_to_product_measurePreserving)

lemma firstReflection_lattice (n : Fin 3 → ℤ) :
    firstReflection (latticeVector n)=
      latticeVector (fun i ↦ if i=0 then -n i else n i) := by
  ext i
  simp only [firstReflection_apply,latticeVector,WithLp.ofLp_toLp]
  split_ifs <;> simp

def reflectionPullback (F : Cover → Cover) : Cover → Cover :=
  fun x ↦ firstReflection (F (firstReflection x))

lemma reflectionPullback_contDiff {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    ContDiff ℝ (⊤ : ℕ∞) (reflectionPullback F) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ firstReflection (F (firstReflection x)))
  simpa only [reflectionPullback,firstReflection_symm] using isometry_pullback_contDiff firstReflection hF

lemma reflectionPullback_periodic {F : Cover → Cover}
    (hp : ∀ n x,F (x+latticeVector n)=F x) :
    ∀ n x,reflectionPullback F (x+latticeVector n)=reflectionPullback F x := by
  intro n x
  simp only [reflectionPullback,map_add,firstReflection_lattice,hp]

lemma reflectionPullback_admissible {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (reflectionPullback F) :=
  ⟨reflectionPullback_contDiff hF.1,reflectionPullback_periodic hF.2.1,
    fun x ↦ by simpa only [reflectionPullback,LinearIsometryEquiv.norm_map] using hF.2.2 (firstReflection x)⟩

lemma divergence_reflectionPullback {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (reflectionPullback F) x=divergence F (firstReflection x) := by
  change divergence (fun y ↦ firstReflection (F (firstReflection y))) x=_
  simpa only [reflectionPullback,firstReflection_symm] using
    divergence_isometry_pullback firstReflection (hF.differentiable (by simp)) x

lemma reflectionPullback_involutive (F : Cover → Cover) :
    reflectionPullback (reflectionPullback F)=F := by
  funext x
  simp only [reflectionPullback,firstReflection_involutive]

lemma flux_firstReflection {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' (torusFirstReflection ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence (reflectionPullback F) x := by
  have hG := reflectionPullback_admissible hF
  rw [← setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1)
    (hE.preimage torusFirstReflection.continuous.measurable),
    ← setIntegral_lift (continuous_divergence hG.1) (divergence_periodic hG.2.1) hE]
  have he : (fun z : Torus ↦ divergence F (representative z))=
      fun z ↦ divergence (reflectionPullback F) (representative (torusFirstReflection z)) := by
    funext z
    rw [divergence_reflectionPullback hF.1]
    have hq : quotientMap (firstReflection (representative (torusFirstReflection z)))=
        quotientMap (representative z) := by
      rw [firstReflection_quotient,quotientMap_representative,
        torusFirstReflection_involutive,quotientMap_representative]
    obtain ⟨n,hn⟩ := same_quotient_lattice hq
    rw [hn,divergence_periodic hF.2.1]
  rw [he]
  exact torusFirstReflection_measurePreserving.setIntegral_preimage_emb
    torusFirstReflection.toHomeomorph.measurableEmbedding
      (fun z ↦ divergence (reflectionPullback F) (representative z)) E

lemma perimeter_firstReflection {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (torusFirstReflection ⁻¹' E)=perimeter E := by
  have hle {A : Set Torus} (hA : MeasurableSet A) :
      perimeter (torusFirstReflection ⁻¹' A)≤perimeter A := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    rw [flux_firstReflection hF hA]
    exact le_iSup₂_of_le (reflectionPullback F) (reflectionPullback_admissible hF) le_rfl
  apply le_antisymm (hle hE)
  have hh := hle (hE.preimage torusFirstReflection.continuous.measurable)
  simpa only [preimage_preimage,Function.comp_def,torusFirstReflection_involutive,preimage_id'] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

structure LatticeIsometry where
  cover : Cover ≃ₗᵢ[ℝ] Cover
  torus : Torus ≃ᵢ Torus
  commute : ∀ x,quotientMap (cover x)=torus (quotientMap x)

namespace LatticeIsometry

def symm (e : LatticeIsometry) : LatticeIsometry where
  cover := e.cover.symm
  torus := e.torus.symm
  commute x := by
    apply e.torus.injective
    rw [←e.commute,e.cover.apply_symm_apply,e.torus.apply_symm_apply]

lemma map_zero (e : LatticeIsometry) : e.torus 0=0 := by
  have hz : quotientMap (0 : Cover) = 0 := by ext j; simp [quotientMap]
  simpa only [LinearIsometryEquiv.map_zero,hz] using (e.commute 0).symm

lemma map_add (e : LatticeIsometry) (x y : Torus) : e.torus (x+y)=e.torus x+e.torus y := by
  obtain ⟨a,rfl⟩ := quotientMap_surjective x
  obtain ⟨b,rfl⟩ := quotientMap_surjective y
  rw [←quotientMap_add,←e.commute,LinearIsometryEquiv.map_add,quotientMap_add,e.commute,e.commute]

def addHom (e : LatticeIsometry) : Torus →+ Torus where
  toFun := e.torus
  map_zero' := e.map_zero
  map_add' := e.map_add

lemma measurePreserving (e : LatticeIsometry) : MeasurePreserving e.torus torusVolume torusVolume :=
  (e.addHom).measurePreserving e.torus.continuous e.torus.surjective rfl

lemma lattice (e : LatticeIsometry) (m : Fin 3 → ℤ) :
    ∃ n : Fin 3 → ℤ,e.cover (latticeVector m)=latticeVector n := by
  have he : quotientMap (e.cover (latticeVector m))=quotientMap (0 : Cover) := by
    rw [e.commute,quotientMap_latticeVector,e.map_zero]
    ext j; simp [quotientMap]
  obtain ⟨n,hn⟩ := same_quotient_lattice he
  exact ⟨n,by simpa only [zero_add] using hn⟩

def pullback (e : LatticeIsometry) (F : Cover → Cover) : Cover → Cover :=
  fun x ↦ e.cover.symm (F (e.cover x))

lemma pullback_contDiff (e : LatticeIsometry) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (e.pullback F) :=
  isometry_pullback_contDiff e.cover hF

lemma pullback_periodic (e : LatticeIsometry) {F : Cover → Cover}
    (hp : ∀ m x,F (x+latticeVector m)=F x) :
    ∀ m x,e.pullback F (x+latticeVector m)=e.pullback F x := by
  intro m x
  obtain ⟨n,hn⟩ := e.lattice m
  simp only [pullback,LinearIsometryEquiv.map_add,hn,hp]

lemma pullback_admissible (e : LatticeIsometry) {F : Cover → Cover} (hF : AdmissibleField F) :
    AdmissibleField (e.pullback F) := by
  refine ⟨e.pullback_contDiff hF.1,e.pullback_periodic hF.2.1,fun x ↦ ?_⟩
  simpa only [pullback,LinearIsometryEquiv.norm_map] using hF.2.2 (e.cover x)

lemma divergence_pullback (e : LatticeIsometry) {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Cover) :
    divergence (e.pullback F) x=divergence F (e.cover x) :=
  divergence_isometry_pullback e.cover (hF.differentiable (by simp)) x

lemma flux (e : LatticeIsometry) {F : Cover → Cover} (hF : AdmissibleField F)
    {E : Set Torus} (hE : MeasurableSet E) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' (e.torus ⁻¹' E),divergence F x)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence (e.symm.pullback F) x := by
  have hG := e.symm.pullback_admissible hF
  rw [←setIntegral_lift (continuous_divergence hF.1) (divergence_periodic hF.2.1)
    (hE.preimage e.torus.continuous.measurable),
    ←setIntegral_lift (continuous_divergence hG.1) (divergence_periodic hG.2.1) hE]
  have he : (fun z : Torus ↦ divergence F (representative z))=
      fun z ↦ divergence (e.symm.pullback F) (representative (e.torus z)) := by
    funext z
    rw [e.symm.divergence_pullback hF.1]
    have hq : quotientMap (e.cover.symm (representative (e.torus z)))=quotientMap (representative z) := by
      change quotientMap (e.symm.cover (representative (e.torus z)))=quotientMap (representative z)
      rw [e.symm.commute,quotientMap_representative,quotientMap_representative]
      exact e.torus.symm_apply_apply z
    obtain ⟨n,hn⟩ := same_quotient_lattice hq
    change divergence F (representative z)=divergence F (e.cover.symm (representative (e.torus z)))
    rw [hn,divergence_periodic hF.2.1]
  rw [he]
  exact e.measurePreserving.setIntegral_preimage_emb e.torus.toHomeomorph.measurableEmbedding
    (fun z ↦ divergence (e.symm.pullback F) (representative z)) E

lemma perimeter_measurable (e : LatticeIsometry) {E : Set Torus} (hE : MeasurableSet E) :
    perimeter (e.torus ⁻¹' E)=perimeter E := by
  have hle (a : LatticeIsometry) {A : Set Torus} (hA : MeasurableSet A) :
      perimeter (a.torus ⁻¹' A)≤perimeter A := by
    apply iSup_le; intro F
    apply iSup_le; intro hF
    rw [a.flux hF hA]
    exact le_iSup₂_of_le (a.symm.pullback F) (a.symm.pullback_admissible hF) le_rfl
  apply le_antisymm (hle e hE)
  have hh := hle e.symm (hE.preimage e.torus.continuous.measurable)
  have hset : e.symm.torus ⁻¹' (e.torus ⁻¹' E)=E := by
    ext x
    change e.torus (e.torus.symm x)∈E ↔ x∈E
    rw [e.torus.apply_symm_apply]
  rwa [hset] at hh

theorem perimeter_eq (e : LatticeIsometry) {E : Set Torus} (hE : NullMeasurableSet E torusVolume) :
    perimeter (e.torus ⁻¹' E)=perimeter E := by
  have he := hE.toMeasurable_ae_eq
  have hp := e.measurePreserving.quasiMeasurePreserving.preimage_ae_eq he
  rw [←perimeter_congr_ae hp,←perimeter_congr_ae he]
  exact e.perimeter_measurable (measurableSet_toMeasurable _ _)

lemma finitePerimeter (e : LatticeIsometry) {E : Set Torus} (hE : FinitePerimeter E) :
    FinitePerimeter (e.torus ⁻¹' E) :=
  ⟨hE.1.preimage e.measurePreserving.quasiMeasurePreserving,by rw [e.perimeter_eq hE.1]; exact hE.2⟩

theorem isMinimizerAt (e : LatticeIsometry) {V : ℝ} {E : Set Torus} (hE : IsMinimizerAt V E) :
    IsMinimizerAt V (e.torus ⁻¹' E) := by
  refine ⟨e.finitePerimeter hE.1,?_,?_⟩
  · rw [e.measurePreserving.measure_preimage hE.1.1,hE.2.1]
  · intro F hF hv
    rw [e.perimeter_eq hE.1.1]
    exact hE.2.2 F hF hv

end LatticeIsometry

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def centeredIsometryLift (φ : Torus ≃ᵢ Torus) (x : Cover) : Cover :=
  shortestLift (φ (quotientMap x) - φ 0)

lemma norm_quotientMap_of_small {x : Cover} (hx : ‖x‖ < 1/2) :
    ‖quotientMap x‖ = ‖x‖ := by
  rw [←norm_shortestLift,shortestLift_quotientMap hx]

lemma centeredIsometryLift_norm (φ : Torus ≃ᵢ Torus) {x : Cover} (hx : ‖x‖ < 1/2) :
    ‖centeredIsometryLift φ x‖ = ‖x‖ := by
  rw [centeredIsometryLift,norm_shortestLift,←dist_eq_norm,φ.dist_eq,
    dist_zero_right,norm_quotientMap_of_small hx]

lemma centeredIsometryLift_dist (φ : Torus ≃ᵢ Torus) {x y : Cover}
    (hx : ‖x‖ < 1/4) (hy : ‖y‖ < 1/4) :
    dist (centeredIsometryLift φ x) (centeredIsometryLift φ y) = dist x y := by
  have hh : dist (φ (quotientMap x)) (φ 0) + dist (φ (quotientMap y)) (φ 0) < 1/2 := by
    rw [φ.dist_eq,φ.dist_eq,dist_zero_right,dist_zero_right]
    exact lt_of_le_of_lt (add_le_add (norm_quotientMap_le _) (norm_quotientMap_le _)) (by linarith)
  rw [centeredIsometryLift,centeredIsometryLift,dist_shortestLift_sub_local hh,
    φ.dist_eq,dist_eq_norm,←quotientMap_sub,norm_quotientMap_of_small,
    ←dist_eq_norm]
  exact (norm_sub_le _ _).trans_lt (by linarith)

lemma centeredIsometryLift_inner (φ : Torus ≃ᵢ Torus) {x y : Cover}
    (hx : ‖x‖ < 1/4) (hy : ‖y‖ < 1/4) :
    ⟪centeredIsometryLift φ x,centeredIsometryLift φ y⟫ = ⟪x,y⟫ := by
  have hd := centeredIsometryLift_dist φ hx hy
  rw [dist_eq_norm,dist_eq_norm] at hd
  have hn := norm_sub_sq_real (centeredIsometryLift φ x) (centeredIsometryLift φ y)
  rw [centeredIsometryLift_norm φ (by linarith),
    centeredIsometryLift_norm φ (by linarith),hd,norm_sub_sq_real] at hn
  linarith

theorem torusIsometry_local_linear (φ : Torus ≃ᵢ Torus) :
    ∃ L : Cover ≃ₗᵢ[ℝ] Cover, ∀ x, ‖x‖ < 1/4 → centeredIsometryLift φ x = L x := by
  let b := EuclideanSpace.basisFun (Fin 3) ℝ
  let v : Fin 3 → Cover := fun i ↦ (8 : ℝ) • centeredIsometryLift φ ((1/8 : ℝ) • b i)
  have hb (i : Fin 3) : ‖(1/8 : ℝ) • b i‖ < 1/4 := by
    rw [norm_smul,b.norm_eq_one,Real.norm_eq_abs]
    norm_num
  have ho : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    dsimp only [v]
    rw [real_inner_smul_left,real_inner_smul_right,
      centeredIsometryLift_inner φ (hb i) (hb j),
      real_inner_smul_left,real_inner_smul_right,b.inner_eq_ite]
    split_ifs <;> norm_num
  have hspan : ⊤ ≤ Submodule.span ℝ (range v) := by
    rw [ho.linearIndependent.span_eq_top_of_card_eq_finrank' (by simp [Cover])]
  let B : OrthonormalBasis (Fin 3) ℝ Cover := OrthonormalBasis.mk ho hspan
  let L : Cover ≃ₗᵢ[ℝ] Cover := b.equiv B (Equiv.refl _)
  refine ⟨L,fun x hx ↦ ?_⟩
  apply B.repr.injective
  ext i
  simp only [OrthonormalBasis.repr_apply_apply]
  have hBi : B i = v i := by simp [B]
  have hLi : L (b i) = B i := by simp [L]
  nth_rw 2 [←hLi]
  rw [L.inner_map_map,hBi]
  dsimp only [v]
  rw [real_inner_smul_left,centeredIsometryLift_inner φ (hb i) hx,
    real_inner_smul_left]
  ring

end CubicTorus

end
end

end OAI
