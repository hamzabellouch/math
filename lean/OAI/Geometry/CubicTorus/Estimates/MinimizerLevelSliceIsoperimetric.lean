import Mathlib
import OAI.Geometry.CubicTorus.Estimates.RadialSectionArea

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_radial_slice_length_of_level_vertices {V : ℝ} (hV : V∈Ioo 0 1)
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
    ∃ r : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) r ∧ Function.Periodic r 1 ∧ (∀ a,0<r a) ∧
      axialSectionArea (openRepresentative E) 0 t=Real.pi*(∫ a in (0 : ℝ)..1,(r a)^2) ∧
      axialSlicePerimeter (openRepresentative E) 0 t=
        ENNReal.ofReal (∫ a in (0 : ℝ)..1,Real.sqrt ((deriv r a)^2+(2*Real.pi*r a)^2)) := by
  obtain ⟨r,hr,hrp,hrb,hbd,hphase,hcl⟩ := isMinimizerAt_smooth_radial_section_of_level_vertices
    hV hE hm hμ hN hp ha hs hsg ht hv1 hv2 htE
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

theorem isMinimizerAt_slice_isoperimetric_of_level_vertices {V : ℝ} (hV : V∈Ioo 0 1)
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
    (hv2 : quotientMap (coordinateSectionPoint (chamberCorner s) t ((1/2 : ℂ)*Complex.I))∉closure (openRepresentative E)) :
    4*Real.pi*axialSectionArea (openRepresentative E) 0 t≤
      ((axialSlicePerimeter (openRepresentative E) 0 t).toReal)^2 := by
  by_cases htE : quotientMap (coordinateSectionPoint (chamberCorner s) t 0)∈openRepresentative E
  · obtain ⟨r,hr,hrp,hr0,harea,hper⟩ := isMinimizerAt_radial_slice_length_of_level_vertices
      hV hE hm hμ hN hp ha hs hsg ht hv1 hv2 htE
    have hi := radial_curve_isoperimetric (fun a => (hr.differentiable (by simp) a).hasDerivAt)
      (hr.continuous_deriv (by simp)) hrp hr0
    have hn : 0≤∫ a in (0 : ℝ)..1,Real.sqrt ((deriv r a)^2+(2*Real.pi*r a)^2) :=
      intervalIntegral.integral_nonneg (by norm_num) (fun a _ => Real.sqrt_nonneg _)
    rw [harea,hper,ENNReal.toReal_ofReal hn]
    convert hi using 1; ring
  · have he := isMinimizerAt_centered_section_empty hV hE hm hμ ha hs hsg ht htE
    rw [← centeredPlaneSection_real_volume (isOpen_openRepresentative E).measurableSet (chamberCorner s),he]
    simp [Measure.real]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_axial_flux_nonneg {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) (hc : Continuous (axialSectionArea (openRepresentative E) i)) :
    ∀ t : ℝ,0≤(μ.mass : ℝ)*axialFluxWeight μ i+
      H*(axialSectionArea (openRepresentative E) i t-V) := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hm
  have hvol : torusVolume.real (openRepresentative E)=V := by
    rw [Measure.real,measure_congr hae,hm.2.1,ENNReal.toReal_ofReal hV.1.le]
  exact (axialWeightedHeight_density (isOpen_openRepresentative E).measurableSet hvol
    (fun D => by rw [directionalFlux_congr_ae hae,hH]) i hc).1

lemma isMinimizerAt_axialFluxWeight_pos {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) → 0<N x i)
    (i : Fin 3) : 0<axialFluxWeight μ i := by
  have hmass : 0<(μ.mass : ℝ) := by
    rw [hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hm.1.1 hm.2.1).ne' hm.1.2.ne
  have hpos := isMinimizerAt_axialNormalWeight_pos_ae hV hE hm hμ hN hp ha hs hsg i
  have hsupport : Function.support (axialNormalWeight i) =ᵐ[(μ : Measure NormalBundle)] univ :=
    hpos.mono fun z hz => by
      apply propext
      change axialNormalWeight i z≠0 ↔ True
      exact iff_true_intro hz.ne'
  have hint : 0<(∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle)) := by
    rw [integral_pos_iff_support_of_nonneg (axialNormalWeight_nonneg i) (integrable_axialNormalWeight μ i),
      measure_congr hsupport,← FiniteMeasure.ennreal_mass]
    exact_mod_cast hmass
  exact div_pos hint hmass

theorem isMinimizerAt_missing_axis_flux {V : ℝ} (hV : V∈Ioo 0 1)
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
    (hv : quotientMap (chamberVertex s (fun j => decide (j=i)))∉closure (openRepresentative E)) :
    0<H ∧ (μ.mass : ℝ)*axialFluxWeight μ i=H*V ∧
    axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2)=0 ∧
    axialSlicePerimeter (openRepresentative E) i (chamberCorner s i)=
      ENNReal.ofReal (H*axialSectionArea (openRepresentative E) i (chamberCorner s i)) ∧
    ∀ t : AddCircle (1 : ℝ),axialJensenFlux (openRepresentative E) μ H V i t=
      H*axialCircleArea (openRepresentative E) i t := by
  have hsgc : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ j : Fin 3,0≤N x j := fun x hx j => (hsg x j ⟨hx.1,mem_iInter.mp hx.2 j⟩).le
  have hnone := isMinimizerAt_vacant_axial_section hV hE hm hμ ha hs hsgc i hv
  have hempty : ∀ x : Cover,x i=chamberCorner s i+1/2 → quotientMap x∉openRepresentative E :=
    fun x hx he => hnone x hx (subset_closure he)
  have harea := axialSectionArea_eq_zero_of_empty hempty
  have hperim := axialSlicePerimeter_eq_zero_of_empty hempty
  have htop : axialSlicePerimeter (openRepresentative E) i (chamberCorner s i+1/2)=
      ENNReal.ofReal ((μ.mass : ℝ)*axialFluxWeight μ i+
        H*(axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2)-V)) := by
    have ht := isMinimizerAt_axial_endpoint_perimeter hV hE hm hμ hN hp ha hs hsg hH i (!(s i))
    cases hsi : s i
    · simpa [chamberCorner,hsi] using ht
    · simp only [hsi,Bool.not_true,Bool.false_eq_true,ite_false] at ht
      have hc : chamberCorner s i=(1/2 : ℝ) := by simp [chamberCorner,hsi]
      rw [hc,show (1/2 : ℝ)+1/2=0+1 by norm_num,
        axialSlicePerimeter_periodic (openRepresentative E) i 0,
        axialSectionArea_periodic (openRepresentative E) i 0]
      exact ht
  have hpos := isMinimizerAt_axial_flux_nonneg hV hE hm hH i
    (isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i) (chamberCorner s i+1/2)
  have htR := congrArg ENNReal.toReal htop
  rw [hperim,ENNReal.toReal_zero,ENNReal.toReal_ofReal hpos,harea] at htR
  have hflux : (μ.mass : ℝ)*axialFluxWeight μ i=H*V := by linarith
  have hmass : 0<(μ.mass : ℝ) := by
    rw [hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hm.1.1 hm.2.1).ne' hm.1.2.ne
  have hHpos : 0<H := by
    have hh := mul_pos hmass (isMinimizerAt_axialFluxWeight_pos hV hE hm hμ hN hp ha hs hsg i)
    rw [hflux] at hh
    exact (mul_pos_iff.mp hh).resolve_right (fun hn => (not_lt_of_ge hV.1.le hn.2)) |>.1
  refine ⟨hHpos,hflux,harea,?_,?_⟩
  · have hh := isMinimizerAt_axial_endpoint_perimeter hV hE hm hμ hN hp ha hs hsg hH i (s i)
    have he : chamberCorner s i=(if s i then (1/2 : ℝ) else 0) := rfl
    rw [he,hh,hflux]
    congr 1
    ring
  · intro t
    dsimp only [axialJensenFlux]
    rw [hflux]
    ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_axial_chamberTop_perimeter {V : ℝ} (hV : V∈Ioo 0 1)
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
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    axialSlicePerimeter (openRepresentative E) i (chamberCorner s i+1/2)=
      ENNReal.ofReal ((μ.mass : ℝ)*axialFluxWeight μ i+
        H*(axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2)-V)) := by
  have hh := isMinimizerAt_axial_endpoint_perimeter hV hE hm hμ hN hp ha hs hsg hH i (!(s i))
  cases hb : s i
  · simpa [chamberCorner,hb] using hh
  · have hp1 : axialSlicePerimeter (openRepresentative E) i 1=axialSlicePerimeter (openRepresentative E) i 0 := by
      simpa using axialSlicePerimeter_periodic (openRepresentative E) i 0
    have hp2 : axialSectionArea (openRepresentative E) i 1=axialSectionArea (openRepresentative E) i 0 := by
      simpa using axialSectionArea_periodic (openRepresentative E) i 0
    norm_num [chamberCorner,hb] at hh ⊢
    simpa [hp1,hp2] using hh

theorem isMinimizerAt_corner_endpoint_flux {V : ℝ} (hV : V∈Ioo 0 1)
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
    {t : ℝ} (ht : t=chamberCorner s 0 ∨ t=chamberCorner s 0+1/2)
    (hv1 : quotientMap (coordinateSectionPoint (chamberCorner s) t (1/2 : ℂ))∉closure (openRepresentative E))
    (hv2 : quotientMap (coordinateSectionPoint (chamberCorner s) t ((1/2 : ℂ)*Complex.I))∉closure (openRepresentative E)) :
    Real.sqrt (Real.pi*axialSectionArea (openRepresentative E) 0 t)≤
      ((μ.mass : ℝ)/2)*axialFluxWeight μ 0+(H/2)*(axialSectionArea (openRepresentative E) 0 t-V) := by
  have htI : t∈Icc (chamberCorner s 0) (chamberCorner s 0+1/2) := by
    rcases ht with rfl|rfl <;> constructor <;> linarith
  have hi := isMinimizerAt_slice_isoperimetric_of_level_vertices hV hE hm hμ hN hp ha hs hsg htI hv1 hv2
  have hq := isMinimizerAt_axial_flux_nonneg hV hE hm hH 0
    (isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg 0) t
  have he : axialSlicePerimeter (openRepresentative E) 0 t=
      ENNReal.ofReal ((μ.mass : ℝ)*axialFluxWeight μ 0+H*(axialSectionArea (openRepresentative E) 0 t-V)) := by
    rcases ht with rfl|rfl
    · exact isMinimizerAt_axial_endpoint_perimeter hV hE hm hμ hN hp ha hs hsg hH 0 (s 0)
    · exact isMinimizerAt_axial_chamberTop_perimeter hV hE hm hμ hN hp ha hs hsg hH 0
  rw [he,ENNReal.toReal_ofReal hq] at hi
  have h0 := mul_nonneg Real.pi_pos.le (axialSectionArea_nonneg (openRepresentative E) 0 t)
  have hsqrt := Real.sq_sqrt h0
  nlinarith [Real.sqrt_nonneg (Real.pi*axialSectionArea (openRepresentative E) 0 t)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_vertex_vacant_of_not_occupied {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (s b : Fin 3 → Bool)
    (hv : quotientMap (chamberVertex s b)∉openRepresentative E) :
    quotientMap (chamberVertex s b)∉closure (openRepresentative E) := by
  intro hc
  exact hv (mem_open_of_mem_closure_not_frontier (isOpen_openRepresentative E) hc
    (isMinimizerAt_reflection_vertex_excluded hV hE hm hμ hN hp ha hs
      (chamberVertex_sine_zero s b)))

lemma chamberVertex_top_section_real (s : Fin 3 → Bool) :
    chamberVertex s (fun j => decide (j=0 ∨ j=1))=
      coordinateSectionPoint (chamberCorner s) (chamberCorner s 0+1/2) (1/2 : ℂ) := by
  ext i
  fin_cases i <;> simp [chamberVertex,coordinateSectionPoint]

lemma chamberVertex_top_section_imag (s : Fin 3 → Bool) :
    chamberVertex s (fun j => decide (j=0 ∨ j=2))=
      coordinateSectionPoint (chamberCorner s) (chamberCorner s 0+1/2) ((1/2 : ℂ)*Complex.I) := by
  ext i
  fin_cases i <;> simp [chamberVertex,coordinateSectionPoint]

theorem isMinimizerAt_two_missing_vertices_top_flux {V : ℝ} (hV : V∈Ioo 0 1)
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
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E) :
    Real.sqrt (Real.pi*axialSectionArea (openRepresentative E) 0 (chamberCorner s 0+1/2))≤
      ((μ.mass : ℝ)/2)*axialFluxWeight μ 0+
        (H/2)*(axialSectionArea (openRepresentative E) 0 (chamberCorner s 0+1/2)-V) := by
  have hv1' := isMinimizerAt_vertex_vacant_of_not_occupied hV hE hm hμ hN hp ha hs s _ hv1
  have hv2' := isMinimizerAt_vertex_vacant_of_not_occupied hV hE hm hμ hN hp ha hs s _ hv2
  rw [chamberVertex_top_section_real] at hv1'
  rw [chamberVertex_top_section_imag] at hv2'
  exact isMinimizerAt_corner_endpoint_flux hV hE hm hμ hN hp ha hs hsg hH (Or.inr rfl) hv1' hv2'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_complement_frontier {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E) :
    frontier (openRepresentative Eᶜ)=frontier (openRepresentative E) := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hm
  rw [isMinimizerAt_frontier_openRepresentative hVc hE.compl hmc,
    isMinimizerAt_frontier_openRepresentative hV hE hm,compl_compl,inter_comm]

lemma coordinateHalf_not_reflected (b : Bool) (i : Fin 3) {a : Torus}
    (ha : a∈coordinateHalf i (if !b then 0 else 1/2)) :
    coordinateReflection i a∈coordinateHalf i (if b then 0 else 1/2) := by
  cases b
  · simp only [Bool.not_false,ite_true,Bool.false_eq_true,ite_false] at ha ⊢
    rw [← coordinateReflection_preimage_half]
    change coordinateReflection i (coordinateReflection i a)∈coordinateHalf i 0
    simpa only [coordinateReflection_involutive] using ha
  · simp only [Bool.not_true,ite_true,Bool.false_eq_true,ite_false] at ha ⊢
    change a∈coordinateReflection i ⁻¹' coordinateHalf i 0
    rwa [coordinateReflection_preimage_half]

theorem isMinimizerAt_complement_chamber_sign {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i) :
    ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative Eᶜ)∩coordinateHalf i (if !(s i) then 0 else 1/2) →0<(-N x) i := by
  intro x i hx
  rw [isMinimizerAt_complement_frontier hV hE hm] at hx
  have hry : quotientMap (coverCoordinateReflection i x)∈frontier (openRepresentative E) := by
    rw [quotientMap_coordinateReflection]
    change quotientMap x∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
    rw [frontier_reflection_invariant hE i (hs i)]
    exact hx.1
  have hrh : quotientMap (coverCoordinateReflection i x)∈coordinateHalf i (if s i then 0 else 1/2) := by
    rw [quotientMap_coordinateReflection]
    exact coordinateHalf_not_reflected (s i) i hx.2
  have hn := hsg _ i ⟨hry,hrh⟩
  have he := congrArg (fun v : Cover => v i)
    (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hx.1)
  simp only [coverCoordinateReflection_apply,ite_true] at he
  change 0 < -(N x i)
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_reverse_mass (μ : FiniteMeasure NormalBundle) :
    ((μ.map reverseNormal).mass : ℝ)=(μ.mass : ℝ) := by
  have hh := congrArg ENNReal.toReal
    (Measure.map_apply continuous_reverseNormal.measurable MeasurableSet.univ
      (μ := (μ : Measure NormalBundle)))
  simpa only [preimage_univ,FiniteMeasure.mass,FiniteMeasure.coeFn_def,
    FiniteMeasure.toMeasure_map,Measure.real,ENNReal.toReal] using hh

lemma axialFluxWeight_reverse (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    axialFluxWeight (μ.map reverseNormal) i=axialFluxWeight μ i := by
  unfold axialFluxWeight
  rw [normal_reverse_mass]
  congr 1
  change (∫ z,axialNormalWeight i z ∂Measure.map reverseNormal (μ : Measure NormalBundle))=_
  rw [integral_map continuous_reverseNormal.measurable.aemeasurable
    (continuous_axialNormalWeight i).aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by simp [axialNormalWeight,reverseNormal]

lemma directionalFlux_reverse {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (D : Periodic.Variation) :
    directionalFlux Eᶜ D.coordinate D.function= -directionalFlux E D.coordinate D.function := by
  let F : Cover → Cover := fun x => D.function x • EuclideanSpace.single D.coordinate 1
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := D.smooth.smul contDiff_const
  have hp : ∀ m x,F (x+latticeVector m)=F x := fun m x => by simp only [F,D.periodic]
  have hd : divergence F=fun x => fderiv ℝ D.function x (EuclideanSpace.single D.coordinate 1) := by
    funext x
    exact divergence_smul_const (D.smooth.differentiable (by simp)).differentiableAt _
  have hf := periodic_normal_flux hμ hF hp
  have hfc := periodic_normal_flux (isNormalMeasure_compl hE hμ) hF hp
  rw [hd] at hf hfc
  change (∫ z,⟪(z.2 : Cover),F z.1⟫ ∂Measure.map reverseNormal (μ : Measure NormalBundle))=_ at hfc
  have hci : Continuous (fun z : NormalBundle => ⟪(z.2 : Cover),F z.1⟫) :=
    continuous_normalUnit.inner (hF.continuous.comp (continuous_subtype_val.comp continuous_fst))
  rw [integral_map continuous_reverseNormal.measurable.aemeasurable hci.aestronglyMeasurable] at hfc
  change (∫ z,⟪-(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))=_ at hfc
  simp_rw [inner_neg_left,integral_neg] at hfc
  rw [hf] at hfc
  exact hfc.symm

lemma periodicNormalFirstVariation_reverse (μ : FiniteMeasure NormalBundle)
    (D : Periodic.Variation) :
    Periodic.normalFirstVariation (μ.map reverseNormal) D=Periodic.normalFirstVariation μ D := by
  unfold Periodic.normalFirstVariation
  change (∫ z,⟪(z.2 : Cover),coordinateNormalVelocity D.coordinate D.function z.1 z.2⟫
    ∂Measure.map reverseNormal (μ : Measure NormalBundle))=_
  rw [integral_map continuous_reverseNormal.measurable.aemeasurable
    (continuous_normalUnit.inner (𝕜 := ℝ) (continuous_coordinateNormalVelocity D.coordinate D.smooth)).aestronglyMeasurable]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change ⟪-(z.2 : Cover),coordinateNormalVelocity D.coordinate D.function z.1 (-(z.2 : Cover))⟫=_
    have he : coordinateNormalVelocity D.coordinate D.function z.1 (-(z.2 : Cover))=
        -coordinateNormalVelocity D.coordinate D.function z.1 (z.2 : Cover) := by
      simp only [coordinateNormalVelocity,inner_neg_left]
      module
    rw [he,inner_neg_neg]

theorem complement_firstVariation_same_multiplier {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) :
    ∀ D : Periodic.Variation,Periodic.normalFirstVariation (μ.map reverseNormal) D=
      (-H)*directionalFlux Eᶜ D.coordinate D.function := by
  intro D
  rw [periodicNormalFirstVariation_reverse,hH,directionalFlux_reverse hE hμ]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSectionArea_compl {F : Set Torus} (hF : MeasurableSet F) (i : Fin 3) (t : ℝ) :
    axialSectionArea Fᶜ i t=1-axialSectionArea F i t := by
  have he : axialSection Fᶜ i t=transverseSquare\axialSection F i t := by
    ext y
    simp only [axialSection,mem_inter_iff,mem_preimage,mem_compl_iff,Set.mem_sdiff]
    tauto
  unfold axialSectionArea
  rw [he]
  rw [measureReal_sdiff (show axialSection F i t ⊆ transverseSquare from inter_subset_left)
    (measurableSet_axialSection hF i t) volume_transverseSquare_lt_top.ne]
  simp only [Measure.real,volume_axialSquare,ENNReal.toReal_one]

lemma isMinimizerAt_openRepresentative_compl {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E) :
    openRepresentative Eᶜ=(closure (openRepresentative E))ᶜ := by
  rw [isMinimizerAt_closure_openRepresentative hV hE hm]
  simp only [openRepresentative,compl_compl]

theorem isMinimizerAt_axial_complement_area {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (i : Fin 3) (t : ℝ) :
    axialSectionArea (openRepresentative Eᶜ) i t=1-axialSectionArea (openRepresentative E) i t := by
  have hz := isMinimizerAt_axial_boundary_null hV hE hm hμ hN hp ha hs hsg i t
  have hn : ∀ᵐ y : Plane,quotientMap ((axialSplit i).symm (t,y))∉frontier (openRepresentative E) := by
    rw [ae_iff]
    simpa only [not_not] using hz
  have he : axialSection (openRepresentative Eᶜ) i t=ᵐ[volume]
      axialSection (openRepresentative E)ᶜ i t := by
    filter_upwards [hn] with y hy
    apply propext
    simp only [axialSection,mem_inter_iff,mem_preimage,mem_compl_iff,
      isMinimizerAt_openRepresentative_compl hV hE hm]
    apply and_congr_right
    intro _
    apply not_congr
    constructor
    · intro hc
      exact mem_open_of_mem_closure_not_frontier (isOpen_openRepresentative E) hc hy
    · intro hm
      exact (subset_closure : openRepresentative E ⊆ closure (openRepresentative E)) hm
  calc
    axialSectionArea (openRepresentative Eᶜ) i t=axialSectionArea (openRepresentative E)ᶜ i t :=
      congrArg ENNReal.toReal (measure_congr he)
    _=1-axialSectionArea (openRepresentative E) i t :=
      axialSectionArea_compl (isOpen_openRepresentative E).measurableSet i t

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotientMap_chamberVertex_complement (s b : Fin 3 → Bool) :
    quotientMap (chamberVertex (fun i => !(s i)) b)=
      quotientMap (chamberVertex s (fun i => !(b i))) := by
  let m : Fin 3 → ℤ := fun i => if s i then (if b i then 0 else -1) else (if b i then 1 else 0)
  have he : chamberVertex (fun i => !(s i)) b=
      chamberVertex s (fun i => !(b i))+latticeVector m := by
    ext i
    cases hs : s i <;> cases hb : b i <;>
      norm_num [chamberVertex,chamberCorner,latticeVector,m,hs,hb]
  rw [he,quotientMap_add,quotientMap_latticeVector,add_zero]

lemma axialSectionArea_complementary_corner (F : Set Torus) (s : Fin 3 → Bool) (i : Fin 3) :
    axialSectionArea F i (chamberCorner (fun j => !(s j)) i+1/2)=
      axialSectionArea F i (chamberCorner s i) := by
  cases hs : s i
  · have hh := axialSectionArea_periodic F i 0
    norm_num [chamberCorner,hs] at hh ⊢
    exact hh
  · norm_num [chamberCorner,hs]

lemma reflection_symmetry_compl {E : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    ∀ i : Fin 3,coordinateReflection i ⁻¹' Eᶜ =ᵐ[torusVolume] Eᶜ := by
  intro i
  filter_upwards [hs i] with a ha
  apply propext
  change (coordinateReflection i a∉E) ↔ (a∉E)
  exact not_congr (Iff.of_eq ha)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_two_occupied_vertices_bottom_flux {V : ℝ} (hV : V∈Ioo 0 1)
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
    (hv1 : quotientMap (chamberVertex s (fun j => decide (j=1)))∈openRepresentative E)
    (hv2 : quotientMap (chamberVertex s (fun j => decide (j=2)))∈openRepresentative E) :
    Real.sqrt (Real.pi*(1-axialSectionArea (openRepresentative E) 0 (chamberCorner s 0)))≤
      ((μ.mass : ℝ)/2)*axialFluxWeight μ 0+
        (H/2)*(axialSectionArea (openRepresentative E) 0 (chamberCorner s 0)-V) := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hm
  have hpc : ∀ m x,(-N) (x+latticeVector m)=(-N) x := fun m x => by simp only [Pi.neg_apply,hp]
  have hscc := reflection_symmetry_compl hs
  have hsc := isMinimizerAt_complement_chamber_sign hV hE hm hμ hN hp ha hs hsg
  have hHc := complement_firstVariation_same_multiplier hE hμ hH
  have hv1c : quotientMap (chamberVertex (fun j => !(s j)) (fun j => decide (j=0 ∨ j=1)))∉openRepresentative Eᶜ := by
    rw [quotientMap_chamberVertex_complement,isMinimizerAt_openRepresentative_compl hV hE hm]
    have hb : (fun j : Fin 3 => !(decide (j=0 ∨ j=1)))=(fun j => decide (j=2)) := by
      funext j; fin_cases j <;> decide
    rw [hb]
    exact fun h => h (subset_closure hv2)
  have hv2c : quotientMap (chamberVertex (fun j => !(s j)) (fun j => decide (j=0 ∨ j=2)))∉openRepresentative Eᶜ := by
    rw [quotientMap_chamberVertex_complement,isMinimizerAt_openRepresentative_compl hV hE hm]
    have hb : (fun j : Fin 3 => !(decide (j=0 ∨ j=2)))=(fun j => decide (j=1)) := by
      funext j; fin_cases j <;> decide
    rw [hb]
    exact fun h => h (subset_closure hv1)
  have hh := isMinimizerAt_two_missing_vertices_top_flux hVc hE.compl hmc
    (isNormalMeasure_compl hE hμ) hN.neg hpc (normal_reverse_ae hN.continuous hp ha)
    hscc hsc hHc hv1c hv2c
  rw [normal_reverse_mass,axialFluxWeight_reverse,
    axialSectionArea_complementary_corner,
    isMinimizerAt_axial_complement_area hV hE hm hμ hN hp ha hs hsg] at hh
  convert hh using 1; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSplit_symm_neg_axis (i : Fin 3) (t : ℝ) (y : Plane) :
    (axialSplit i).symm (-t,y)=coverCoordinateReflection i ((axialSplit i).symm (t,y)) := by
  rw [axialSplit_symm_axis_line i (-t) t y]
  ext j
  by_cases hj : j=i
  · subst j
    simp [coverCoordinateReflection_apply,axialSplit_symm_axis]
  · simp [coverCoordinateReflection_apply,hj]

lemma axialSection_reflection {F : Set Torus} (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' F=F) (t : ℝ) :
    axialSection F i (-t)=axialSection F i t := by
  ext y
  simp only [axialSection,mem_inter_iff,mem_preimage,axialSplit_symm_neg_axis,
    quotientMap_coordinateReflection]
  exact and_congr_right (fun _ => Set.ext_iff.mp hs _)

lemma axialSectionArea_reflection {F : Set Torus} (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' F=F) (t : ℝ) :
    axialSectionArea F i (-t)=axialSectionArea F i t := by
  exact congrArg (fun A : Set Plane => volume.real A) (axialSection_reflection i hs t)

lemma axialSectionArea_reflection_one_sub {F : Set Torus} (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' F=F) (t : ℝ) :
    axialSectionArea F i (1-t)=axialSectionArea F i t := by
  rw [show 1-t=-t+1 by ring,axialSectionArea_periodic F i (-t),axialSectionArea_reflection i hs]

lemma axialSectionArea_bounds_Icc {F : Set Torus} {s : Fin 3 → Bool} (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' F=F)
    (hm : AntitoneOn (axialSectionArea F i) (Icc (chamberCorner s i) (chamberCorner s i+1/2)))
    {t : ℝ} (ht : t∈Icc 0 1) :
    axialSectionArea F i (chamberCorner s i+1/2)≤axialSectionArea F i t ∧
      axialSectionArea F i t≤axialSectionArea F i (chamberCorner s i) := by
  have he (u : ℝ) (hu : u∈Icc (chamberCorner s i) (chamberCorner s i+1/2)) :
      axialSectionArea F i (chamberCorner s i+1/2)≤axialSectionArea F i u ∧
      axialSectionArea F i u≤axialSectionArea F i (chamberCorner s i) :=
    ⟨hm hu ⟨by linarith,le_rfl⟩ hu.2,hm ⟨le_rfl,by linarith⟩ hu hu.1⟩
  cases hb : s i
  · have hc : chamberCorner s i=0 := by simp [chamberCorner,hb]
    by_cases hu : t≤1/2
    · exact he t (by rw [hc]; exact ⟨ht.1,by linarith⟩)
    · have hh := he (1-t) (by rw [hc]; constructor <;> linarith [ht.2])
      rwa [axialSectionArea_reflection_one_sub i hs] at hh
  · have hc : chamberCorner s i=(1/2 : ℝ) := by simp [chamberCorner,hb]
    by_cases hu : 1/2≤t
    · exact he t (by rw [hc]; exact ⟨hu,by linarith [ht.2]⟩)
    · have hh := he (1-t) (by rw [hc]; constructor <;> linarith [ht.1])
      rwa [axialSectionArea_reflection_one_sub i hs] at hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_endpoint_volume_bounds {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {s : Fin 3 → Bool}
    (hsg : ∀ (x : Cover) (i : Fin 3),
      quotientMap x∈frontier (openRepresentative E)∩coordinateHalf i (if s i then 0 else 1/2) →0<N x i)
    (i : Fin 3) :
    axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2)≤V ∧
      V≤axialSectionArea (openRepresentative E) i (chamberCorner s i) := by
  have hF := (isOpen_openRepresentative E).measurableSet
  have hint := integrable_axialSectionArea hF i
  have hvol := integral_axialSectionArea hF i
  have hvol' : torusVolume.real (openRepresentative E)=V := by
    rw [Measure.real,measure_congr (isMinimizerAt_openRepresentative_ae hV hE hm),hm.2.1,
      ENNReal.toReal_ofReal hV.1.le]
  rw [hvol'] at hvol
  have hbounds (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) := axialSectionArea_bounds_Icc i
    (openRepresentative_reflection_invariant hE i (hs i))
    (isMinimizerAt_antitoneOn_axialSectionArea hV hE hm hμ hN hp ha hs hsg i) ht
  have hlo := setIntegral_mono_on
    (integrableOn_const (C := axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2))
      (by simp : volume (Ico (0 : ℝ) 1)≠⊤)) hint measurableSet_Ico
    (fun t ht => (hbounds t ⟨ht.1,ht.2.le⟩).1)
  have hhi := setIntegral_mono_on hint
    (integrableOn_const (C := axialSectionArea (openRepresentative E) i (chamberCorner s i))
      (by simp : volume (Ico (0 : ℝ) 1)≠⊤)) measurableSet_Ico
    (fun t ht => (hbounds t ⟨ht.1,ht.2.le⟩).2)
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ico,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,smul_eq_mul,one_mul,hvol] at hlo hhi
  exact ⟨hlo,hhi⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_coordinate_multiplier_nonneg {V : ℝ} (hV : V∈Ioo 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {H : ℝ} (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) : 0≤H := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  obtain ⟨N,C,hN,hp,ha,hs,hd,_⟩ := Periodic.profile_hessian_of_CMC hV' hE hm hμ
    (fun _ hF hpF => Periodic.weakCMC_identity hμ hH hF hpF)
  have hh := profile_upper_support_slope_nonneg hV hs
  rw [hd] at hh
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_halfMass_competitor_bounds {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    0<(μ.mass : ℝ)/2 ∧ (μ.mass : ℝ)/2≤Real.sqrt (Real.pi*V) ∧ (μ.mass : ℝ)/2≤1 := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  have hmass : 0<(μ.mass : ℝ) := by
    rw [hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV' hm.1.1 hm.2.1).ne' hm.1.2.ne
  have hprof := isoperimetricProfile_le_candidate ⟨hV.1.le,hV'.2.le⟩
  rw [isoperimetricProfile_eq_of_isMinimizerAt hm,← hμ.1] at hprof
  have hmin : min V (1-V)=V := min_eq_left (by linarith [hV.2])
  have hc1 : candidateProfile V≤2*Real.sqrt (Real.pi*V) := by
    unfold candidateProfile
    rw [hmin]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hc2 : candidateProfile V≤2 :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  exact ⟨by linarith,by linarith,by linarith⟩

theorem isMinimizerAt_four_corner_necessary_data {V : ℝ} (hV : V∈Ioo 0 (1/2))
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
    (ht1 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=1)))∉openRepresentative E)
    (ht2 : quotientMap (chamberVertex c (fun j => decide (j=0 ∨ j=2)))∉openRepresentative E)
    (hb1 : quotientMap (chamberVertex c (fun j => decide (j=1)))∈openRepresentative E)
    (hb2 : quotientMap (chamberVertex c (fun j => decide (j=2)))∈openRepresentative E) :
    let A : ℝ := (μ.mass : ℝ)/2
    let h := H/2
    let r := axialSectionArea (openRepresentative E) 0 (chamberCorner c 0+1/2)
    let s := axialSectionArea (openRepresentative E) 0 (chamberCorner c 0)
    let b := axialFluxWeight μ 0
    0 < A ∧ A ≤ Real.sqrt (Real.pi*V) ∧ A ≤ 1 ∧ 0 ≤ h ∧
      0 ≤ r ∧ r ≤ V ∧ V ≤ s ∧ s ≤ 1 ∧ 0 ≤ b ∧ b ≤ 1 ∧
      Real.sqrt (Real.pi*r)≤A*b-h*(V-r) ∧
      Real.sqrt (Real.pi*(1-s))≤A*b+h*(s-V) ∧
      s-r≤A*Real.sqrt (1-b) := by
  dsimp only
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  obtain ⟨hA,hAc,hA1⟩ := isMinimizerAt_halfMass_competitor_bounds ⟨hV.1,hV.2.le⟩ hm hμ
  have hH0 := isMinimizerAt_coordinate_multiplier_nonneg hV hE hm hμ hH
  obtain ⟨hrV,hVs⟩ := isMinimizerAt_endpoint_volume_bounds hV' hE hm hμ hN hp ha hs hsg 0
  have ht := isMinimizerAt_two_missing_vertices_top_flux hV' hE hm hμ hN hp ha hs hsg hH ht1 ht2
  have hb := isMinimizerAt_two_occupied_vertices_bottom_flux hV' hE hm hμ hN hp ha hs hsg hH hb1 hb2
  have hproj := axialProjection_bound μ 0
  rw [isMinimizerAt_axial_endFlux hV' hE hm hμ hN hp ha hs hsg hH 0] at hproj
  refine ⟨hA,hAc,hA1,by linarith,axialSectionArea_nonneg _ _ _,hrV,hVs,
    axialSectionArea_le_one _ _ _,axialFluxWeight_nonneg μ 0,
    axialFluxWeight_le_one μ 0 (by linarith),?_,hb,?_⟩
  · convert ht using 1; ring
  · linarith

end CubicTorus

end
end

end OAI
