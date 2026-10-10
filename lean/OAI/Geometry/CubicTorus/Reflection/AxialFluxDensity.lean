import Mathlib
import OAI.Geometry.CubicTorus.Reflection.AxialSectionCoordinates

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

theorem deriv_ae_eq_of_integrable_weak_derivative {u v : ℝ → ℝ}
    (hu : Continuous u) {a b : ℝ} (hab : a<b)
    (hv : IntegrableOn v (Icc a b))
    (hweak : ∀ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t,u t*deriv ψ t)=-(∫ t,v t*ψ t)) :
    ∀ᵐ t ∂volume.restrict (Ioo a b),deriv u t=v t := by
  let g : ℝ → ℝ := (Icc a b).indicator v
  have hg : Integrable g := hv.integrable_indicator measurableSet_Icc
  let F : ℝ → ℝ := fun t => ∫ s in a..t,g s
  have hF : Continuous F := intervalIntegral.continuous_primitive (fun c d => hg.intervalIntegrable) a
  have hFac : AbsolutelyContinuousOnInterval F a b :=
    hg.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hd : ∀ᵐ t, t∈uIcc a b → deriv F t=g t := by
    filter_upwards [hg.intervalIntegrable.ae_hasDerivAt_integral (a := a) (b := b)] with t ht htab
    exact (ht htab a (by simp)).deriv
  have hz : ∀ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ ⊆ Ioo a b →
      (∫ t,(u t-F t)*deriv ψ t)=0 := by
    intro ψ hψ hs
    have hsc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset isClosed_closure
      (hs.trans Ioo_subset_Icc_self)
    have hiu : Integrable (fun t => u t*deriv ψ t) :=
      (hu.mul (hψ.continuous_deriv (by simp))).integrable_of_hasCompactSupport hsc.deriv.mul_left
    have hiF : Integrable (fun t => F t*deriv ψ t) :=
      (hF.mul (hψ.continuous_deriv (by simp))).integrable_of_hasCompactSupport hsc.deriv.mul_left
    have hacψ : AbsolutelyContinuousOnInterval ψ a b :=
      (hψ.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    have hparts := hFac.integral_mul_deriv_eq_deriv_mul hacψ
    have hψa : ψ a=0 := image_eq_zero_of_notMem_tsupport (fun h => (hs h).1.false)
    have hψb : ψ b=0 := image_eq_zero_of_notMem_tsupport (fun h => (hs h).2.false)
    have hsd : tsupport (deriv ψ) ⊆ Ioo a b := (tsupport_deriv_subset (f := ψ)).trans hs
    rw [hψa,hψb,mul_zero,mul_zero,sub_self,zero_sub,
      integral_compact_eq_interval hab.le hsd] at hparts
    have hr : (∫ t in a..b,deriv F t*ψ t)=∫ t,v t*ψ t := by
      calc
        _ = ∫ t in a..b,g t*ψ t := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [hd] with t ht htab
          rw [ht (uIoc_subset_uIcc htab)]
        _ = ∫ t in a..b,v t*ψ t := by
          apply intervalIntegral.integral_congr
          intro t ht
          change g t*ψ t=v t*ψ t
          rw [show g t=v t from indicator_of_mem (by simpa [uIcc_of_le hab.le] using ht) v]
        _ = _ := integral_compact_eq_interval hab.le hs
    rw [hr] at hparts
    simp_rw [sub_mul]
    rw [integral_sub hiu hiF,hweak ψ hψ hs,hparts,sub_self]
  let c := (a+b)/2
  have hc : c∈Ioo a b := by dsimp [c]; constructor <;> linarith
  have he : EqOn u (fun t => F t+(u c-F c)) (Ioo a b) := by
    intro t ht
    have hh := continuous_constant_of_weak_derivative_zero (hu.sub hF) ht hc hz
    change u t-F t=u c-F c at hh
    linarith
  have hec : EqOn u (fun t => F t+(u c-F c)) (Icc a b) := by
    rw [← closure_Ioo hab.ne]
    exact he.closure hu (hF.add continuous_const)
  have hdloc : ∀ᵐ t ∂volume.restrict (Ioo a b),deriv F t=g t := by
    filter_upwards [ae_restrict_of_ae hd,ae_restrict_mem measurableSet_Ioo] with t ht htab
    exact ht (by simpa [uIcc_of_le hab.le] using Ioo_subset_Icc_self htab)
  filter_upwards [hdloc,ae_restrict_mem measurableSet_Ioo] with t ht htab
  have heq : u =ᶠ[𝓝 t] (fun t => F t+(u c-F c)) := by
    filter_upwards [show ∀ᶠ r in 𝓝 t,r∈Ioo a b from isOpen_Ioo.mem_nhds htab] with r hr
    exact he hr
  rw [heq.deriv_eq,deriv_add_const,ht]
  exact indicator_of_mem (Ioo_subset_Icc_self htab) v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axial_section_weak_derivative_of_density {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    {g : AddCircle (1 : ℝ) → ℝ}
    (hgm : ∀ f : AddCircle (1 : ℝ) → ℝ,Continuous f →
      (∫ t,g t*f t)=∫ z,-((z.2 : Cover) i)*f (axialBundleHeight i z) ∂(μ : Measure NormalBundle)) :
    ∀ ψ : ℝ → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → tsupport ψ⊆Ioo (0 : ℝ) 1 →
      (∫ t,axialSectionArea E i t*deriv ψ t)=-(∫ t : ℝ,g (t : AddCircle (1 : ℝ))*ψ t) := by
  intro ψ hψ hs
  have hc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset isClosed_closure
    (hs.trans Ioo_subset_Icc_self)
  let f := circlePeriodize ψ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := circlePeriodize_contDiff hψ hc
  have hp : Function.Periodic f 1 := circlePeriodize_periodic ψ
  have heval (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : f t=ψ t :=
    (circlePeriodize_unit_eventuallyEq hc hs ht).eq_of_nhds
  have hder (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : deriv f t=deriv ψ t :=
    (circlePeriodize_unit_eventuallyEq hc hs ht).deriv_eq
  have hflux := axial_section_periodic_flux hE hμ i hf hp
  have hl : (∫ t in (0 : ℝ)..1,axialSectionArea E i t*deriv f t)=
      ∫ t,axialSectionArea E i t*deriv ψ t := by
    calc
      _=∫ t in (0 : ℝ)..1,axialSectionArea E i t*deriv ψ t := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [hder t (by simpa [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using ht)]
      _=_ := integral_compact_eq_interval (by norm_num)
        ((tsupport_deriv_subset (f := ψ)).trans hs)
  rw [hl] at hflux
  have hdens := hgm hp.lift (continuous_periodic_lift hp hf.continuous)
  have hdc : (∫ t : AddCircle (1 : ℝ),g t*hp.lift t)=
      ∫ t : ℝ,g (t : AddCircle (1 : ℝ))*ψ t := by
    rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
    simp only [zero_add,Function.Periodic.lift_coe]
    calc
      _=∫ t in (0 : ℝ)..1,g (t : AddCircle (1 : ℝ))*ψ t := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only
        rw [heval t (by simpa [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using ht)]
      _=_ := integral_compact_eq_interval (by norm_num) hs
  rw [hdc] at hdens
  have hn : (∫ z,-((z.2 : Cover) i)*hp.lift (axialBundleHeight i z) ∂(μ : Measure NormalBundle))=
      -(∫ z,((z.2 : Cover) i)*f (z.1.1 i) ∂(μ : Measure NormalBundle)) := by
    simp only [axialBundleHeight,Function.Periodic.lift_coe,neg_mul,integral_neg]
  rw [hn] at hdens
  linarith

theorem axial_section_derivative_density {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    (hac : Measure.map (axialBundleHeight i) (μ : Measure NormalBundle)≪volume)
    (hc : Continuous (axialSectionArea E i)) :
    ∃ g : AddCircle (1 : ℝ) → ℝ,Integrable g ∧
      (∀ f : AddCircle (1 : ℝ) → ℝ,Measurable f → (∃ M : ℝ,∀ t,‖f t‖≤M) →
        (∫ t,g t*f t)=∫ z,-((z.2 : Cover) i)*f (axialBundleHeight i z) ∂(μ : Measure NormalBundle)) ∧
      ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),deriv (axialSectionArea E i) t=g (t : AddCircle (1 : ℝ)) := by
  obtain ⟨g,hg,hgm⟩ := circle_weighted_density_bounded (μ : Measure NormalBundle)
    (continuous_axialBundleHeight i) hac
    (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).neg)
  refine ⟨g,hg,hgm,deriv_ae_eq_of_integrable_weak_derivative hc (by norm_num) ?_ ?_⟩
  · simpa only [zero_add] using circle_integrable_preimage_Icc hg 0
  apply axial_section_weak_derivative_of_density hE hμ i
  intro f hf
  obtain ⟨M,_,hM⟩ := (isCompact_univ.image hf).isBounded.exists_pos_norm_le
  exact hgm f hf.measurable ⟨M,fun t => hM _ ⟨t,mem_univ _,rfl⟩⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_axial_endFlux {V : ℝ} (hV : V∈Ioo 0 1)
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
    (∫ z,|((z.2 : Cover) i)| ∂(μ : Measure NormalBundle))=
      2*(axialSectionArea (openRepresentative E) i (chamberCorner s i)-
        axialSectionArea (openRepresentative E) i (chamberCorner s i+1/2)) := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hm
  have hμo := hμ.congr_ae hae.symm
  have hac := isMinimizerAt_axialHeight_absolutelyContinuous hV hE hm hμ hN hp ha hs hsg hH i
  have hc := isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i
  obtain ⟨g,hg,hgm,hgd⟩ := axial_section_derivative_density
    (isOpen_openRepresentative E).measurableSet hμo i hac hc
  have htest := hgm (chamberHeightSign (s i)) (measurable_chamberHeightSign (s i))
    ⟨1,fun t => (norm_chamberHeightSign (s i) t).le⟩
  have hfront := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμo
  have hn : (∫ z,-((z.2 : Cover) i)*chamberHeightSign (s i) (axialBundleHeight i z)
      ∂(μ : Measure NormalBundle))=-(∫ z,|((z.2 : Cover) i)| ∂(μ : Measure NormalBundle)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hfront,ha] with z hz hzn
    have he := isMinimizerAt_normal_chamberHeightSign hV hE hm hμ hN hp ha hs hsg hz i
    rw [hzn] at he
    change -((z.2 : Cover) i)*chamberHeightSign (s i) (z.1.1 i) = -|((z.2 : Cover) i)|
    rw [neg_mul,he]
  rw [hn] at htest
  have hd : (∫ t in (0 : ℝ)..1,g (t : AddCircle (1 : ℝ))*chamberHeightSign (s i) t)=
      (∫ t in (0 : ℝ)..1,deriv (axialSectionArea (openRepresentative E) i) t*chamberHeightSign (s i) t) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1),← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [hgd] with t ht
    simp only [ht]
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0] at htest
  simp only [zero_add] at htest
  rw [hd] at htest
  have hperiod : axialSectionArea (openRepresentative E) i 1=
      axialSectionArea (openRepresentative E) i 0 := by
    simpa only [zero_add] using axialSectionArea_periodic (openRepresentative E) i 0
  have hFTC := chamberSign_integral_deriv
    (isMinimizerAt_absolutelyContinuous_axialSectionArea hV hE hm hμ hN hp ha hs hsg hH i)
    hperiod (s i)
  rw [hFTC] at htest
  dsimp only [chamberCorner]
  linarith [htest]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

def axialCircleArea (E : Set Torus) (i : Fin 3) : AddCircle (1 : ℝ) → ℝ :=
  (axialSectionArea_periodic E i).lift

@[simp] lemma axialCircleArea_coe (E : Set Torus) (i : Fin 3) (t : ℝ) :
    axialCircleArea E i t=axialSectionArea E i t :=
  Function.Periodic.lift_coe (axialSectionArea_periodic E i) t

lemma integral_axialCircleArea_mul {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {f : ℝ → ℝ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    (∫ t,axialCircleArea E i t*hp.lift t)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x i) := by
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0]
  simp only [zero_add,axialCircleArea_coe,Function.Periodic.lift_coe]
  rw [axial_section_fubini hE i hf hp,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),
    integral_Ico_eq_integral_Ioc]

theorem axialWeightedHeight_density {V : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hvol : torusVolume.real E=V)
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) (hc : Continuous (axialSectionArea E i)) :
    (∀ t : ℝ,0≤(μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i t-V)) ∧
    axialWeightedHeight μ i=volume.withDensity (fun t => ENNReal.ofReal
      ((μ.mass : ℝ)*axialFluxWeight μ i+H*(axialCircleArea E i t-V))) := by
  have hvc : Continuous (axialCircleArea E i) :=
    continuous_periodic_lift (axialSectionArea_periodic E i) hc
  let C := (μ.mass : ℝ)*axialFluxWeight μ i
  have hC : C=(∫ z,axialNormalWeight i z ∂(μ : Measure NormalBundle)) := by
    by_cases hm : (μ.mass : ℝ)=0
    · have hz : μ=0 := (FiniteMeasure.mass_zero_iff μ).mp (NNReal.coe_eq_zero.mp hm)
      simp [C,hz,axialFluxWeight]
    · dsimp [C,axialFluxWeight]
      field_simp
  obtain ⟨hpos,hdens⟩ := circle_positive_density_of_smooth_moments
    (A := axialWeightedHeight μ i) (q := fun t => C+H*(axialCircleArea E i t-V))
    (continuous_const.add (continuous_const.mul (hvc.sub continuous_const))) (by
      intro f hf hp
      rw [integral_axialWeightedHeight μ i hf.continuous hp]
      have he := axial_flux_moment hH i hf hp
      have hvol' : volume.real (fundamentalCube∩quotientMap ⁻¹' E)=V := by
        rw [← realVolume_lift hE,hvol]
      rw [hvol',← hC] at he
      have hfi : Integrable hp.lift := circle_continuous_integrable (continuous_periodic_lift hp hf.continuous)
      have hvi : Integrable (fun t => axialCircleArea E i t*hp.lift t) :=
        circle_continuous_integrable (hvc.mul (continuous_periodic_lift hp hf.continuous))
      have hfun : (fun t => (C+H*(axialCircleArea E i t-V))*hp.lift t)=
          (fun t => H*(axialCircleArea E i t*hp.lift t)+(C-H*V)*hp.lift t) := by
        funext t
        ring
      rw [hfun,integral_add (hvi.const_mul H) (hfi.const_mul (C-H*V)),
        integral_const_mul,integral_const_mul,integral_axialCircleArea_mul hE i hf.continuous hp]
      have hcircle := AddCircle.intervalIntegral_preimage (1 : ℝ) 0 hp.lift
      simp only [zero_add,Function.Periodic.lift_coe] at hcircle
      rw [← hcircle]
      linarith [he])
  exact ⟨fun t => by simpa only [axialCircleArea_coe,C] using hpos (t : AddCircle (1 : ℝ)),hdens⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialSectionIntegral (E : Set Torus) (i : Fin 3) (g : Cover → ℝ) (t : ℝ) : ℝ :=
  ∫ y in transverseSquare,characteristic E (quotientMap ((axialSplit i).symm (t,y)))*
    g ((axialSplit i).symm (t,y))

lemma axialSectionIntegral_periodic (E : Set Torus) (i : Fin 3) {g : Cover → ℝ}
    (hp : ∀ m x,g (x+latticeVector m)=g x) : Function.Periodic (axialSectionIntegral E i g) 1 := by
  intro t
  apply setIntegral_congr_fun measurableSet_transverseSquare
  intro y hy
  have he : EuclideanSpace.single i (1 : ℝ)=latticeVector (Pi.single i (1 : ℤ)) := by
    ext j
    simp [latticeVector,Pi.single_apply]
  dsimp only
  rw [axialSplit_symm_axis_line i (t+1) t y,show t+1-t=1 by ring,one_smul,he,
    hp,quotientMap_add,quotientMap_latticeVector,add_zero]

lemma continuous_axialSectionIntegral_of_boundary_null {E : Set Torus}
    (hE : MeasurableSet E) (i : Fin 3)
    (hz : ∀ t : ℝ,volume {y : Plane | quotientMap ((axialSplit i).symm (t,y))∈frontier E}=0)
    {g : Cover → ℝ} (hg : Continuous g) (hp : ∀ m x,g (x+latticeVector m)=g x) :
    Continuous (axialSectionIntegral E i g) := by
  obtain ⟨M,hM0,hM⟩ := periodic_bounded hg hp
  rw [continuous_iff_continuousAt]
  intro t
  apply continuousAt_of_dominated (bound := fun _ : Plane => M)
  · apply Eventually.of_forall
    intro u
    exact (((measurable_characteristic hE).comp (measurable_quotientMap.comp
      ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))).mul
      (hg.measurable.comp ((axialSplit i).symm.measurable.comp (measurable_const.prodMk measurable_id)))).aestronglyMeasurable
  · exact Eventually.of_forall fun u => Eventually.of_forall fun y => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (characteristic_bound E _) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hM ((axialSplit i).symm (u,y)))
  · exact integrableOn_const volume_transverseSquare_lt_top.ne
  · have hnull : ∀ᵐ y : Plane,quotientMap ((axialSplit i).symm (t,y))∉frontier E := by
      rw [ae_iff]
      simpa only [not_not] using hz t
    filter_upwards [ae_restrict_of_ae hnull] with y hy
    have hc : ContinuousAt (characteristic E) (quotientMap ((axialSplit i).symm (t,y))) :=
      (continuousOn_const : ContinuousOn (fun _ : Torus => (1 : ℝ)) (interior E)).continuousAt_indicator hy
    have hx : ContinuousAt (fun u : ℝ => (axialSplit i).symm (u,y)) t :=
      ((continuous_axialSplit_symm i).comp (continuous_id.prodMk continuous_const)).continuousAt
    have hq : ContinuousAt (fun u : ℝ => quotientMap ((axialSplit i).symm (u,y))) t :=
      ContinuousAt.comp (f := fun u : ℝ => (axialSplit i).symm (u,y)) continuous_quotientMap.continuousAt hx
    exact (ContinuousAt.comp (f := fun u : ℝ => quotientMap ((axialSplit i).symm (u,y))) hc hq).mul
      (ContinuousAt.comp (f := fun u : ℝ => (axialSplit i).symm (u,y)) hg.continuousAt hx)

lemma integrable_axialWeightedIndicator {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {g : Cover → ℝ} (hg : Continuous g) (hp : ∀ m x,g (x+latticeVector m)=g x) :
    IntegrableOn (fun z : ℝ × Plane => characteristic E (quotientMap ((axialSplit i).symm z))*g ((axialSplit i).symm z))
      (Ico (0 : ℝ) 1 ×ˢ transverseSquare) := by
  obtain ⟨M,hM0,hM⟩ := periodic_bounded hg hp
  apply IntegrableOn.of_bound (by rw [volume_axialRectangle]; simp)
    (((measurable_characteristic hE).comp (measurable_quotientMap.comp (axialSplit i).symm.measurable)).mul
      (hg.measurable.comp (axialSplit i).symm.measurable)).aestronglyMeasurable M
  exact Eventually.of_forall fun z => by
    change ‖characteristic E (quotientMap ((axialSplit i).symm z))*g ((axialSplit i).symm z)‖≤M
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (characteristic_bound E _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hM ((axialSplit i).symm z))

theorem axial_weighted_section_fubini {E : Set Torus} (hE : MeasurableSet E)
    (i : Fin 3) {g : Cover → ℝ} (hg : Continuous g) (hp : ∀ m x,g (x+latticeVector m)=g x) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,g x)=
      ∫ t in Ico (0 : ℝ) 1,axialSectionIntegral E i g t := by
  let f : ℝ × Plane → ℝ := fun z => characteristic E (quotientMap ((axialSplit i).symm z))*g ((axialSplit i).symm z)
  have he := (axialSplit_measurePreserving i).setIntegral_preimage_emb
    (axialSplit i).measurableEmbedding f (Ico (0 : ℝ) 1 ×ˢ transverseSquare)
  rw [axialSplit_preimage_cube] at he
  have hleft : (fun x : Cover => f (axialSplit i x))=(quotientMap ⁻¹' E).indicator g := by
    funext x
    dsimp [f]
    rw [(axialSplit i).symm_apply_apply]
    by_cases hx : quotientMap x∈E <;> simp [characteristic,hx]
  rw [hleft,setIntegral_indicator (hE.preimage measurable_quotientMap)] at he
  rw [he]
  have hi := integrable_axialWeightedIndicator hE i hg hp
  rw [Measure.volume_eq_prod] at hi ⊢
  rw [setIntegral_prod _ hi]
  rfl

lemma axialSectionIntegral_mul_height (E : Set Torus) (i : Fin 3) (g : Cover → ℝ) (f : ℝ → ℝ) (t : ℝ) :
    axialSectionIntegral E i (fun x => g x*f (x i)) t=axialSectionIntegral E i g t*f t := by
  dsimp only [axialSectionIntegral]
  simp only [axialSplit_symm_axis,← mul_assoc]
  exact integral_mul_const _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma divergence_height_tangent {F : Cover → Cover} (hF : AdmissibleField F)
    (i : Fin 3) (ht : ∀ x,F x i=0) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Cover) :
    divergence (fun y => f (y i) • F y) x=divergence F x*f (x i) := by
  have hfa : ContDiff ℝ (⊤ : ℕ∞) (fun y : Cover => f (y i)) :=
    hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff
  rw [divergence_smul_function (hfa.differentiable (by simp) x) (hF.1.differentiable (by simp) x),
    inner_gradient_left,fderiv_axial_function i (hf.differentiable (by simp)),ht,mul_zero,add_zero,mul_comm]

lemma axial_slice_flux_moment {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ t in Ico (0 : ℝ) 1,axialSectionIntegral E i (divergence F) t*f t)=
      ∫ z,f (z.1.1 i)*normalTest F hF.1.continuous z ∂(μ : Measure NormalBundle) := by
  have hfa : ContDiff ℝ (⊤ : ℕ∞) (fun y : Cover => f (y i)) :=
    hf.comp (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff
  have he := normalMeasure_weighted_flux hμ hfa (axial_function_periodic i hp) hF
  simp_rw [divergence_height_tangent hF i ht hf] at he
  have hgp : ∀ m x,divergence F (x+latticeVector m)*f ((x+latticeVector m) i)=divergence F x*f (x i) := by
    intro m x
    rw [divergence_periodic hF.2.1,axial_function_periodic i hp]
  have hh := axial_weighted_section_fubini hE i ((continuous_divergence hF.1).mul hfa.continuous) hgp
  change (∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x*f (x i))=
    ∫ t in Ico (0 : ℝ) 1,axialSectionIntegral E i (fun x => divergence F x*f (x i)) t at hh
  rw [hh] at he
  simpa only [axialSectionIntegral_mul_height] using he.symm

lemma unit_normal_tangent_quadratic_bound {u v : Cover} (hu : ‖u‖=1) (hv : ‖v‖≤1)
    (i : Fin 3) (ht : v i=0) : ⟪u,v⟫≤1-(u i)^2/2 := by
  have hp := PiLp.norm_apply_le (x := u-v) i
  simp only [PiLp.sub_apply,ht,sub_zero,Real.norm_eq_abs] at hp
  have hps : (u i)^2≤‖u-v‖^2 := by
    exact (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (u i)) (norm_nonneg (u-v))).mpr hp)
  rw [norm_sub_sq_real,hu,one_pow] at hps
  have hvs : ‖v‖^2≤1 := by nlinarith [norm_nonneg v]
  linarith

theorem axial_slice_flux_quadratic_bound {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0)
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) (hf0 : ∀ t,0≤f t) :
    (∫ t in Ico (0 : ℝ) 1,axialSectionIntegral E i (divergence F) t*f t)≤
      (∫ z,axialNormalWeight i z*f (z.1.1 i) ∂(μ : Measure NormalBundle))+
      (∫ z,((z.2 : Cover) i)^2/2*f (z.1.1 i) ∂(μ : Measure NormalBundle)) := by
  rw [axial_slice_flux_moment hE hμ hF i ht hf hp]
  have hcF : Continuous (fun z : NormalBundle => f (z.1.1 i)) :=
    hf.continuous.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp (continuous_subtype_val.comp continuous_fst))
  have hcn : Continuous (fun z : NormalBundle => ((z.2 : Cover) i)^2/2) :=
    ((((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).pow 2).div_const 2)
  have hi1 : Integrable (fun z => axialNormalWeight i z*f (z.1.1 i)) (μ : Measure NormalBundle) :=
    ((continuous_axialNormalWeight i).mul hcF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun z => ((z.2 : Cover) i)^2/2*f (z.1.1 i)) (μ : Measure NormalBundle) :=
    (hcn.mul hcF).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hia := integral_add hi1 hi2
  change (∫ z,axialNormalWeight i z*f (z.1.1 i)+((z.2 : Cover) i)^2/2*f (z.1.1 i) ∂(μ : Measure NormalBundle))=_ at hia
  rw [← hia]
  apply integral_mono
    ((hcF.mul (normalTest F hF.1.continuous).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (hi1.add hi2)
  intro z
  have hb := unit_normal_tangent_quadratic_bound z.2.property (hF.2.2 z.1) i (ht z.1)
  have hh := mul_le_mul_of_nonneg_right hb (hf0 (z.1.1 i))
  change f (z.1.1 i)*⟪(z.2 : Cover),F z.1⟫≤_
  dsimp only [axialNormalWeight,Pi.add_apply]
  nlinarith [hh]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma axial_density_moment {V : ℝ} {E : Set Torus} (hE : MeasurableSet E)
    (hvol : torusVolume.real E=V) {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (hc : Continuous (axialSectionArea E i))
    {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : Function.Periodic f 1) :
    (∫ t in (0 : ℝ)..1,((μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i t-V))*f t)=
      ∫ z,axialNormalWeight i z*f (z.1.1 i) ∂(μ : Measure NormalBundle) := by
  obtain ⟨hq0,hd⟩ := axialWeightedHeight_density hE hvol hH i hc
  have he := integral_axialWeightedHeight μ i hf.continuous hp
  have hqc : Continuous (fun t : AddCircle (1 : ℝ) =>
      (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialCircleArea E i t-V)) :=
    continuous_const.add (continuous_const.mul
      ((continuous_periodic_lift (axialSectionArea_periodic E i) hc).sub continuous_const))
  rw [hd,integral_withDensity_eq_integral_toReal_smul hqc.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at he
  have hq0' (t : AddCircle (1 : ℝ)) :
      0≤(μ.mass : ℝ)*axialFluxWeight μ i+H*(axialCircleArea E i t-V) := by
    obtain ⟨u,rfl⟩ := Quotient.exists_rep t
    simpa only [axialCircleArea_coe] using hq0 u
  simp_rw [ENNReal.toReal_ofReal (hq0' _),smul_eq_mul] at he
  rw [← AddCircle.intervalIntegral_preimage (1 : ℝ) 0] at he
  simp only [zero_add,axialCircleArea_coe,Function.Periodic.lift_coe] at he
  exact he.trans (integral_congr_ae (Eventually.of_forall fun z => mul_comm _ _))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodic_smooth_lipschitz {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hp : ∀ m x,F (x+latticeVector m)=F x) :
    ∃ K : ℝ≥0,LipschitzWith K F := by
  obtain ⟨M,hM,hb⟩ := periodic_bounded (hF.continuous_fderiv (by simp)) (fderiv_periodic hp)
  exact ⟨⟨M,hM⟩,lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by simp)) hb⟩

lemma half_abs_sin_bound {t : ℝ} (ht : |t|≤1/2) :
    2*|t|≤|Real.sin (Real.pi*t)| := by
  have hh := Real.le_sin_mul (show 0≤2*|t| by positivity) (show 2*|t|≤1 by linarith)
  have he : Real.pi/2*(2*|t|)=Real.pi*|t| := by ring
  rw [he] at hh
  rcases le_total 0 t with h|h
  · rw [abs_of_nonneg h] at hh ⊢
    exact hh.trans (le_abs_self _)
  · rw [abs_of_nonpos h] at hh ⊢
    rw [show Real.pi * -t = -(Real.pi*t) by ring,Real.sin_neg] at hh
    exact hh.trans (neg_le_abs _)

theorem isMinimizerAt_normal_reflection_rate {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    ∃ K : ℝ≥0,∀ (i : Fin 3) (b : Bool) (x : Cover),x∈closedFundamentalCube →
      quotientMap x∈frontier (openRepresentative E) →
      |N x i|≤(K : ℝ)*|Real.sin (Real.pi*(x i-(if b then 1/2 else 0)))| := by
  obtain ⟨K,hK⟩ := periodic_smooth_lipschitz hN hp
  refine ⟨K,?_⟩
  intro i b x hx hbd
  have hxi : ∀ j : Fin 3,0≤x j ∧ x j≤1 := by
    obtain ⟨y,hy,rfl⟩ := hx
    exact fun j => ⟨hy.1 j,hy.2 j⟩
  have hk (k : ℤ) : |N x i|≤(K : ℝ)*|x i-(k : ℝ)/2| := by
    let y := coverCoordinateReflection i x+latticeVector (Pi.single i k)
    have hNi : N y i= -N x i := by
      rw [show N y=N (coverCoordinateReflection i x) from hp _ _]
      have he := congrArg (fun z : Cover => z i) (isMinimizerAt_normal_reflection hV hE hm hμ hN hp ha i (hs i) x hbd)
      simp only [coverCoordinateReflection_apply,ite_true] at he
      linarith
    have hd := hK.dist_le_mul x y
    have hl : 2*|N x i|≤dist (N x) (N y) := by
      have hh := PiLp.norm_apply_le (x := N x-N y) i
      simpa only [PiLp.sub_apply,hNi,sub_neg_eq_add,← two_mul,Real.norm_eq_abs,abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ)≤2),dist_eq_norm] using hh
    have he : x-y=(2*(x i-(k : ℝ)/2)) • EuclideanSpace.single i 1 := by
      ext j
      by_cases hj : j=i
      · subst j
        simp [y,coverCoordinateReflection_apply,latticeVector,Pi.single_apply]; ring
      · simp [y,coverCoordinateReflection_apply,latticeVector,Pi.single_apply,hj]
    have hd' : dist x y=2*|x i-(k : ℝ)/2| := by
      rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
      simp
    rw [hd'] at hd
    nlinarith [hl.trans hd]
  cases b
  · simp only [Bool.false_eq_true,ite_false,sub_zero]
    by_cases ht : x i≤1/2
    · have hsin := half_abs_sin_bound (t := x i) (by rw [abs_of_nonneg (hxi i).1]; exact ht)
      have hh := hk 0
      simp only [Int.cast_zero,zero_div,sub_zero] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (x i)]) K.coe_nonneg)
    · have hsin := half_abs_sin_bound (t := x i-1) (by
        rw [abs_of_nonpos (by linarith [(hxi i).2])]
        linarith)
      have he : Real.sin (Real.pi*(x i-1))= -Real.sin (Real.pi*x i) := by
        rw [mul_sub,mul_one,Real.sin_sub_pi]
      rw [he,abs_neg] at hsin
      have hh := hk 2
      norm_num at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (x i-1)]) K.coe_nonneg)
  · simp only [ite_true]
    have hsin := half_abs_sin_bound (t := x i-1/2) (by
      rw [abs_le]
      constructor <;> linarith [(hxi i).1,(hxi i).2])
    have hh := hk 1
    norm_num at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [abs_nonneg (x i-1/2)]) K.coe_nonneg)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma abs_sin_height_periodic (a : ℝ) :
    Function.Periodic (fun t : ℝ => |Real.sin (Real.pi*(t-a))|) 1 := by
  intro t
  dsimp only
  rw [show Real.pi*(t+1-a)=Real.pi*(t-a)+Real.pi by ring,Real.sin_add_pi,abs_neg]

theorem circle_quadratic_contact {h : ℝ → ℝ} (hc : Continuous h)
    (hp : Function.Periodic h 1) (a : ℝ) {M : ℝ} (hM : 0≤M)
    (hmom : ∀ (f : ℝ → ℝ),ContDiff ℝ (⊤ : ℕ∞) f → Function.Periodic f 1 →
      (∀ t,0≤f t) → (∀ t,f t≤1) → ∀ δ : ℝ,0≤δ →
      (∀ t,f t≠0 → |Real.sin (Real.pi*(t-a))|≤δ) →
      (∫ t in (0 : ℝ)..1,h t*f t)≤M*δ^2) : h a≤0 := by
  by_contra ha
  have ha : 0<h a := lt_of_not_ge ha
  let c := h a/2
  have hc0 : 0<c := by dsimp [c]; positivity
  have hca : c<h a := by dsimp [c]; linarith
  have hv : ∀ᶠ t in 𝓝 a,c<h t := hc.continuousAt.eventually (eventually_gt_nhds hca)
  obtain ⟨r,hr,hlocal⟩ := Metric.mem_nhds_iff.mp hv
  let B := M*Real.pi^2+1
  have hB : 0<B := by dsimp [B]; positivity
  let ε := min (r/2) (min (1/4) (c/(2*B)))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hεr : ε<r := (min_le_left _ _).trans_lt (by linarith)
  have hεh : ε<1/2 := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by norm_num))
  have hεB : ε≤c/(2*B) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : M*Real.pi^2*ε<c := by
    have hmul := (le_div_iff₀ (by positivity : 0<2*B)).mp hεB
    dsimp [B] at hmul
    nlinarith [mul_nonneg hM (sq_nonneg Real.pi)]
  let b : ContDiffBump a :=
    { rIn := ε/2
      rOut := ε
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hbs : tsupport b⊆Ioo (a-1/2) (a+1/2) := by
    rw [b.tsupport_eq]
    intro t ht
    have hd : |t-a|≤ε := by simpa only [Metric.mem_closedBall,Real.dist_eq,b] using ht
    obtain ⟨hl,hu⟩ := abs_le.mp hd
    constructor <;> linarith
  let f : ℝ → ℝ := circlePeriodize b
  have hfc : ContDiff ℝ (⊤ : ℕ∞) f := circlePeriodize_contDiff b.contDiff b.hasCompactSupport
  have hfp : Function.Periodic f 1 := circlePeriodize_periodic b
  have hfb (t) : 0≤f t ∧ f t≤1 := circlePeriodize_unit_bounds hbs (fun _ => ⟨b.nonneg,b.le_one⟩) t
  have hsupport (t) (ht : f t≠0) : ∃ n : ℤ,|t+n-a|<ε := by
    by_contra hn
    have hz : ∀ n : ℤ,b (t+n)=0 := by
      intro n
      apply b.zero_of_le_dist
      have hn' : ¬|t+n-a|<ε := fun h => hn ⟨n,h⟩
      simpa only [Real.dist_eq,b] using le_of_not_gt hn'
    apply ht
    show (∑' n : ℤ,b (t+n))=0
    simp only [hz,tsum_zero]
  have hsin (t) (ht : f t≠0) : |Real.sin (Real.pi*(t-a))|≤Real.pi*ε := by
    obtain ⟨n,hn⟩ := hsupport t ht
    have he := (abs_sin_height_periodic a).int_mul n t
    simp only [mul_one] at he
    rw [← he]
    exact Real.abs_sin_le_abs.trans (by rw [abs_mul,abs_of_pos Real.pi_pos]; exact mul_le_mul_of_nonneg_left hn.le Real.pi_pos.le)
  have hprod (t) : c*f t≤h t*f t := by
    by_cases ht : f t=0
    · simp [ht]
    · obtain ⟨n,hn⟩ := hsupport t ht
      have hnear : t+n∈Metric.ball a r := by rw [Metric.mem_ball,Real.dist_eq]; exact hn.trans hεr
      have hh : c<h (t+n) := hlocal hnear
      have he := hp.int_mul n t
      simp only [mul_one] at he
      rw [he] at hh
      exact mul_le_mul_of_nonneg_right hh.le (hfb t).1
  have heq (t) (ht : t∈Icc (a-1/2) (a+1/2)) : f t=b t :=
    (circlePeriodize_eventuallyEq b.hasCompactSupport hbs ht).eq_of_nhds
  have hint : ε≤∫ t in (0 : ℝ)..1,f t := by
    have hshift := hfp.intervalIntegral_add_eq 0 (a-1/2)
    simp only [zero_add] at hshift
    rw [show a-1/2+1=a+1/2 by ring] at hshift
    rw [hshift]
    have hbint : (∫ t in a-1/2..a+1/2,f t)=∫ t in a-1/2..a+1/2,b t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith : a-1/2≤a+1/2)] at ht
      exact heq t ht
    rw [hbint]
    have hine : (∫ t in a-ε/2..a+ε/2,b t)=ε := by
      have he := intervalIntegral.integral_congr (μ := volume) (a := a-ε/2) (b := a+ε/2) (f := (b : ℝ → ℝ)) (g := fun _ => (1 : ℝ)) (by
        intro t ht
        rw [uIcc_of_le (by linarith : a-ε/2≤a+ε/2)] at ht
        apply b.one_of_mem_closedBall
        rw [Metric.mem_closedBall,Real.dist_eq]
        change |t-a|≤ε/2
        rw [abs_le]
        constructor <;> linarith [ht.1,ht.2])
      rw [he,intervalIntegral.integral_const]
      simp only [smul_eq_mul,mul_one]
      ring
    rw [← hine]
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Eventually.of_forall fun _ => b.nonneg) (b.continuous.intervalIntegrable _ _)
  have hlo : c*ε≤∫ t in (0 : ℝ)..1,h t*f t := by
    apply (mul_le_mul_of_nonneg_left hint hc0.le).trans
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono (by norm_num)
      ((continuous_const.mul hfc.continuous).intervalIntegrable _ _)
      ((hc.mul hfc.continuous).intervalIntegrable _ _) hprod
  have hupper := hmom f hfc hfp (fun t => (hfb t).1) (fun t => (hfb t).2)
    (Real.pi*ε) (by positivity) hsin
  have hbig : c≤M*Real.pi^2*ε := by nlinarith [hlo.trans hupper]
  exact (not_le_of_gt hsmall) hbig

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem axial_slice_endpoint_bound {V : ℝ} {E : Set Torus}
    (hE : MeasurableSet E) (hvol : torusVolume.real E=V)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0)
    (hc : Continuous (axialSectionArea E i))
    (hcf : Continuous (axialSectionIntegral E i (divergence F)))
    (a : ℝ) {K : ℝ} (hK : 0≤K)
    (hR : ∀ᵐ z ∂(μ : Measure NormalBundle),|((z.2 : Cover) i)|≤K*|Real.sin (Real.pi*(z.1.1 i-a))|) :
    axialSectionIntegral E i (divergence F) a≤
      (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i a-V) := by
  let p := axialSectionIntegral E i (divergence F)
  let q := fun t => (μ.mass : ℝ)*axialFluxWeight μ i+H*(axialSectionArea E i t-V)
  have hqc : Continuous q := continuous_const.add (continuous_const.mul (hc.sub continuous_const))
  have hpp : Function.Periodic p 1 := axialSectionIntegral_periodic E i (divergence_periodic hF.2.1)
  have hqp : Function.Periodic q 1 := by
    intro t
    dsimp [q]
    rw [axialSectionArea_periodic E i]
  suffices h : p a-q a≤0 by dsimp [p,q] at h; linarith
  apply circle_quadratic_contact (hcf.sub hqc) (hpp.sub hqp) a
    (M := K^2/2*(μ.mass : ℝ)) (by positivity)
  intro f hf hp hf0 hf1 δ hδ hδsupp
  have hb := axial_slice_flux_quadratic_bound hE hμ hF i ht hf hp hf0
  have hden := axial_density_moment hE hvol hH i hc hf hp
  have hic : (∫ t in Ico (0 : ℝ) 1,p t*f t)=∫ t in (0 : ℝ)..1,p t*f t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1),integral_Ico_eq_integral_Ioc]
  change (∫ t in Ico (0 : ℝ) 1,p t*f t)≤_ at hb
  rw [hic] at hb
  have hsub : (∫ t in (0 : ℝ)..1,(p t-q t)*f t)=
      (∫ t in (0 : ℝ)..1,p t*f t)-(∫ t in (0 : ℝ)..1,q t*f t) := by
    simp_rw [sub_mul]
    exact intervalIntegral.integral_sub ((hcf.mul hf.continuous).intervalIntegrable _ _)
      ((hqc.mul hf.continuous).intervalIntegrable _ _)
  change (∫ t in (0 : ℝ)..1,(p t-q t)*f t)≤_
  rw [hsub]
  change (∫ t in (0 : ℝ)..1,q t*f t)=_ at hden
  rw [hden]
  apply (sub_le_iff_le_add'.mpr hb).trans
  have hcn : Continuous (fun z : NormalBundle => ((z.2 : Cover) i)^2/2*f (z.1.1 i)) :=
    ((((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp continuous_normalUnit).pow 2).div_const 2).mul
      (hf.continuous.comp ((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous.comp
        (continuous_subtype_val.comp continuous_fst)))
  calc
    (∫ z,((z.2 : Cover) i)^2/2*f (z.1.1 i) ∂(μ : Measure NormalBundle))≤
        ∫ _ : NormalBundle,K^2*δ^2/2 ∂(μ : Measure NormalBundle) := by
      apply integral_mono_ae (hcn.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (integrable_const _)
      filter_upwards [hR] with z hz
      by_cases hzero : f (z.1.1 i)=0
      · simp only [hzero,mul_zero]
        positivity
      · have hn := hz.trans (mul_le_mul_of_nonneg_left (hδsupp _ hzero) hK)
        have hsq : ((z.2 : Cover) i)^2≤K^2*δ^2 := by
          have hh := (sq_le_sq₀ (abs_nonneg ((z.2 : Cover) i)) (mul_nonneg hK hδ)).mpr hn
          simpa only [sq_abs,mul_pow] using hh
        calc
          _≤((z.2 : Cover) i)^2/2*1 := mul_le_mul_of_nonneg_left (hf1 _) (by positivity)
          _≤K^2*δ^2/2 := by nlinarith
    _=K^2/2*(μ.mass : ℝ)*δ^2 := by
      simp only [integral_const,smul_eq_mul,Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]
      ring

theorem isMinimizerAt_axial_slice_endpoint_bound {V : ℝ} (hV : V∈Ioo 0 1)
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
      H*directionalFlux E D.coordinate D.function)
    {F : Cover → Cover} (hF : AdmissibleField F) (i : Fin 3) (ht : ∀ x,F x i=0) (b : Bool) :
    axialSectionIntegral (openRepresentative E) i (divergence F) (if b then 1/2 else 0)≤
      (μ.mass : ℝ)*axialFluxWeight μ i+
        H*(axialSectionArea (openRepresentative E) i (if b then 1/2 else 0)-V) := by
  have hae := isMinimizerAt_openRepresentative_ae hV hE hm
  have hμo := hμ.congr_ae hae.symm
  have hvol : torusVolume.real (openRepresentative E)=V := by
    rw [Measure.real,measure_congr hae,hm.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hHo : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux (openRepresentative E) D.coordinate D.function := by
    intro D
    rw [directionalFlux_congr_ae hae,hH]
  have hc := isMinimizerAt_continuous_axial_sections hV hE hm hμ hN hp ha hs hsg i
  have hcf := continuous_axialSectionIntegral_of_boundary_null
    (isOpen_openRepresentative E).measurableSet i
    (isMinimizerAt_axial_boundary_null hV hE hm hμ hN hp ha hs hsg i)
    (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  obtain ⟨K,hK⟩ := isMinimizerAt_normal_reflection_rate hV hE hm hμ hN hp ha hs
  apply axial_slice_endpoint_bound (isOpen_openRepresentative E).measurableSet hvol hμo hHo hF i ht hc hcf
    (if b then 1/2 else 0) K.coe_nonneg
  filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμo,ha] with z hz hzn
  have hh := hK i b z.1 z.1.property hz
  rw [hzn] at hh
  exact hh

end CubicTorus

end
end

end OAI
