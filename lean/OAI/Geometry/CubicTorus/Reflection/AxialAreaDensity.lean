import Mathlib
import OAI.Geometry.CubicTorus.Profiles.PlanarRadialDownset

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_zero_at_reflection_height {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {t : AxisCircle} (ht : -t=t) {z : Torus}
    (hz : z∈frontier (openRepresentative E)) (hzi : z i=t) :
    N (representative z) i=0 := by
  have hfix : (axisReflection i).torus z=z := by
    apply PiLp.ext
    intro j
    rw [axisReflection_torus_apply]
    split_ifs with h
    · subst j
      rw [hzi,ht]
    · rfl
  have he := (axisReflection i).normal_equivariant hV hE hmin hR hμ hN hp hae
    (representative z) (by rwa [quotientMap_representative])
  have hrep : N (representative z)=N ((axisReflection i).cover (representative z)) := by
    have hh := periodic_representative hp ((axisReflection i).cover (representative z))
    rwa [(axisReflection i).commute,quotientMap_representative,hfix] at hh
  have hh := congrArg (fun v : Cover ↦ v i) (hrep.trans he)
  rw [axisReflection_cover_apply,ite_eq_left rfl] at hh
  linarith

lemma normal_transverse_near_reflection_height {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {t : AxisCircle} (ht : -t=t) {c : ℝ} (hc : c∈Ioo 0 1) :
    ∃ S : Set AxisCircle,IsOpen S ∧ t∈S ∧
      ∀ᵐ z ∂(μ : Measure NormalBundle),(((z.1 : Cover) i) : AxisCircle)∈S →
        c*normalTransverseLength i z≤(normalTransverseLength i z)^2 := by
  let n : Torus → ℝ := fun z ↦ N (representative z) i
  have hn : Continuous n := continuous_periodic_descent
    ((PiLp.continuous_apply 2 _ i).comp hN.continuous) (fun m x ↦ congrArg (fun y : Cover ↦ y i) (hp m x))
  let B : Set Torus := frontier (openRepresentative E)∩{z | 1-c^2≤(n z)^2}
  have hB : IsCompact B := (isClosed_frontier.inter (isClosed_le continuous_const (hn.pow 2))).isCompact
  let S : Set AxisCircle := ((fun z : Torus ↦ z i) '' B)ᶜ
  have hSo : IsOpen S := (hB.image (PiLp.continuous_apply 2 _ i)).isClosed.isOpen_compl
  have htS : t∈S := by
    rintro ⟨z,hz,hzt⟩
    have he := normal_zero_at_reflection_height hV hE hmin i hR hμ hN hp hae ht hz.1 hzt
    have hbad := hz.2
    change 1-c^2≤(N (representative z) i)^2 at hbad
    rw [he] at hbad
    nlinarith [hc.1,hc.2]
  refine ⟨S,hSo,htS,?_⟩
  have hμO := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  filter_upwards [normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμO,hae] with z hz he
  intro ht
  have hsmall : ((z.2 : Cover) i)^2<1-c^2 := by
    by_contra! hbad
    apply ht
    refine ⟨quotientMap z.1,⟨hz,?_⟩,rfl⟩
    change 1-c^2≤(N (representative (quotientMap z.1)) i)^2
    rw [periodic_representative hp,he]
    exact hbad
  have hs := normalTransverseLength_sq i z
  have hsn := normalTransverseLength_nonneg i z
  have hcs : c≤normalTransverseLength i z := by nlinarith
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axialAreaDensity (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) : ℝ :=
  ((axialAreaMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal

def axialSecondDensity (μ : FiniteMeasure NormalBundle) (i : Fin 3) (t : AxisCircle) : ℝ :=
  ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal

lemma axialAreaDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialAreaDensity μ i) := Measure.integrable_toReal_rnDeriv
lemma axialSecondDensity_integrable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Integrable (axialSecondDensity μ i) := Measure.integrable_toReal_rnDeriv
lemma axialAreaDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialAreaDensity μ i) := (Measure.measurable_rnDeriv _ _).ennreal_toReal
lemma axialSecondDensity_measurable (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    Measurable (axialSecondDensity μ i) := (Measure.measurable_rnDeriv _ _).ennreal_toReal

lemma axialAreaDensity_pairing {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialAreaDensity μ i t*f t)=
      ∫ z,f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  simp only [axialAreaDensity]
  rw [integral_toReal_rnDeriv_mul ha,axialAreaMarginal_integral μ i hf]

lemma axialSurfaceMarginal_ac_of_area {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (axialSurfaceMarginal μ i : Measure AxisCircle)≪volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hz
  have hh := ha hz
  change Measure.map _ _ s=0 at hh ⊢
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hs] at hh ⊢
  exact withDensity_absolutelyContinuous _ _ hh

lemma axialSecondDensity_pairing {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialSecondDensity μ i t*f t)=
      ∫ z,(normalTransverseLength i z)^2*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  simp only [axialSecondDensity]
  rw [integral_toReal_rnDeriv_mul (axialSurfaceMarginal_ac_of_area i ha),
    axialSurfaceMarginal_integral μ i hf]
  apply integral_congr_ae
  filter_upwards [] with z
  have hh := normalTransverseLength_sq i z
  rw [show 1-((z.2 : Cover) i)^2=(normalTransverseLength i z)^2 by linarith]
  ring

lemma axialPerimeterDensity_pairing {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Continuous f) :
    (∫ t,axialPerimeterDensity μ i t*f t)=
      ∫ z,normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPerimeterMarginal_absolutelyContinuous i ha
  change (∫ t,((axialPerimeterMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal*f t)=_
  rw [integral_toReal_rnDeriv_mul hp]
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul
    (normalTransverseLength_continuous i).measurable.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (normalTransverseLength_nonneg i z),smul_eq_mul]

theorem axial_moment_nonneg_ae {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (a b c d : ℝ)
    (hpos : ∀ z : NormalBundle,0≤a+b*normalTransverseLength i z+
      c*(normalTransverseLength i z)^2+d*((z.2 : Cover) i)) :
    ∀ᵐ t,0≤a*axialAreaDensity μ i t+b*axialPerimeterDensity μ i t+
      c*axialSecondDensity μ i t+d*axialNormalDensity μ i t := by
  have hi := (((axialAreaDensity_integrable μ i).const_mul a).add
    ((axialPerimeterDensity_integrable μ i).const_mul b)).add
    ((axialSecondDensity_integrable μ i).const_mul c) |>.add ((axialNormalDensity_integrable μ i).const_mul d)
  apply integrable_circle_nonneg_of_smooth_pairing hi
  intro ψ hψ hp hn
  let f := hp.lift
  have hf : Continuous f := continuous_periodic_lift hp hψ.continuous
  have hfn (t : AxisCircle) : 0≤f t := by
    induction t using Quotient.inductionOn with | h t => exact hn t
  have hA := circle_integrable_mul_continuous (axialAreaDensity_integrable μ i) hf
  have hP := circle_integrable_mul_continuous (axialPerimeterDensity_integrable μ i) hf
  have hT := circle_integrable_mul_continuous (axialSecondDensity_integrable μ i) hf
  have hD := circle_integrable_mul_continuous (axialNormalDensity_integrable μ i) hf
  change 0≤∫ t,(a*axialAreaDensity μ i t+b*axialPerimeterDensity μ i t+
    c*axialSecondDensity μ i t+d*axialNormalDensity μ i t)*f t
  simp only [add_mul,mul_assoc]
  have hAP : Integrable (fun t ↦ a*(axialAreaDensity μ i t*f t)+b*(axialPerimeterDensity μ i t*f t)) :=
    (hA.const_mul a).add (hP.const_mul b)
  have hAPT : Integrable (fun t ↦ a*(axialAreaDensity μ i t*f t)+b*(axialPerimeterDensity μ i t*f t)+
      c*(axialSecondDensity μ i t*f t)) := hAP.add (hT.const_mul c)
  rw [integral_add hAPT (hD.const_mul d),integral_add hAP (hT.const_mul c),
    integral_add (hA.const_mul a) (hP.const_mul b)]
  simp only [integral_const_mul]
  rw [axialAreaDensity_pairing i ha hf,axialPerimeterDensity_pairing i ha hf,
    axialSecondDensity_pairing i ha hf,axialNormalDensity_pairing i ha hf]
  have hci (g : NormalBundle → ℝ) (hg : Continuous g) : Integrable g (μ : Measure NormalBundle) :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hk : Continuous (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) :=
    hf.comp (normal_axisCircle_continuous i)
  have hα := normalTransverseLength_continuous i
  have hν := normal_component_continuous i
  rw [←integral_const_mul,←integral_const_mul,←integral_const_mul,←integral_const_mul]
  have hia : Integrable (fun z : NormalBundle ↦ a*f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) := hci _ (continuous_const.mul hk)
  have hib : Integrable (fun z : NormalBundle ↦ b*(normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hci _ (continuous_const.mul (hα.mul hk))
  have hic : Integrable (fun z : NormalBundle ↦ c*((normalTransverseLength i z)^2*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hci _ (continuous_const.mul ((hα.pow 2).mul hk))
  have hid : Integrable (fun z : NormalBundle ↦ d*(((z.2 : Cover) i)*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hci _ (continuous_const.mul (hν.mul hk))
  have hiab : Integrable (fun z : NormalBundle ↦ a*f (((z.1 : Cover) i) : AxisCircle)+b*(normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hia.add hib
  have hiabc : Integrable (fun z : NormalBundle ↦ a*f (((z.1 : Cover) i) : AxisCircle)+b*(normalTransverseLength i z*f (((z.1 : Cover) i) : AxisCircle))+c*((normalTransverseLength i z)^2*f (((z.1 : Cover) i) : AxisCircle))) (μ : Measure NormalBundle) := hiab.add hic
  rw [←integral_add hia hib,←integral_add hiab hic,←integral_add hiabc hid]
  apply integral_nonneg
  intro z
  convert mul_nonneg (hpos z) (hfn (((z.1 : Cover) i) : AxisCircle)) using 1
  first | rfl | ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSecondDensity_pairing_bounded {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Measurable f) :
    (∫ t,axialSecondDensity μ i t*f t)=
      ∫ z,(normalTransverseLength i z)^2*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  simp only [axialSecondDensity]
  rw [integral_toReal_rnDeriv_mul (axialSurfaceMarginal_ac_of_area i ha)]
  change (∫ t,f t ∂Measure.map _ _)=_
  rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
  have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1-((z.2 : Cover) i)^2)) :=
    (continuous_const.sub ((normal_component_continuous i).pow 2)).measurable.ennreal_ofReal
  rw [integral_withDensity_eq_integral_toReal_smul hw
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i)),smul_eq_mul]
  have hh := normalTransverseLength_sq i z
  congr 1
  linarith

lemma axial_density_local_comparison {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {S : Set AxisCircle} (hS : MeasurableSet S) {c : ℝ}
    (hc : ∀ᵐ z ∂(μ : Measure NormalBundle),(((z.1 : Cover) i) : AxisCircle)∈S →
      c*normalTransverseLength i z≤(normalTransverseLength i z)^2) :
    ∀ᵐ t,t∈S → c*axialPerimeterDensity μ i t≤axialSecondDensity μ i t := by
  have hh : (fun t ↦ c*axialPerimeterDensity μ i t)≤ᵐ[volume.restrict S]axialSecondDensity μ i := by
    apply ae_le_of_forall_setIntegral_le ((axialPerimeterDensity_integrable μ i).const_mul c).integrableOn
      (axialSecondDensity_integrable μ i).integrableOn
    intro T hT ht
    rw [Measure.restrict_restrict hT]
    let f : AxisCircle → ℝ := (T∩S).indicator (fun _ ↦ 1)
    have hf : Measurable f := measurable_const.indicator (hT.inter hS)
    have hfb (t : AxisCircle) : |f t|≤1 := by
      by_cases ht : t∈T∩S <;> simp [f,ht]
    have hp := axialPerimeterDensity_pairing_bounded i ha hf hfb
    have hq := axialSecondDensity_pairing_bounded i ha hf
    have he (g : AxisCircle → ℝ) : (fun t ↦ g t*f t)=(T∩S).indicator g := by
      funext t
      by_cases ht : t∈T∩S <;> simp [f,ht]
    rw [he,integral_indicator (hT.inter hS)] at hp hq
    rw [integral_const_mul,hp,hq,←integral_const_mul]
    have hfi : AEStronglyMeasurable (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
      (hf.comp (normal_axisCircle_continuous i).measurable).aestronglyMeasurable
    have hFint : Integrable (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
      Integrable.of_bound hfi 1 (ae_of_all _ fun z ↦ hfb _)
    have hbounded (g : NormalBundle → ℝ) (hg : Continuous g) :
        Integrable (fun z ↦ g z*f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) := by
      let G : C(NormalBundle,ℝ) := ⟨g,hg⟩
      exact hFint.bdd_mul hg.aestronglyMeasurable (ae_of_all _ fun z ↦ G.norm_coe_le_norm z)
    apply integral_mono_ae ((hbounded _ (normalTransverseLength_continuous i)).const_mul c)
      (hbounded _ ((normalTransverseLength_continuous i).pow 2))
    filter_upwards [hc] with z hz
    by_cases ht : (((z.1 : Cover) i) : AxisCircle)∈T∩S
    · simp only [f,indicator_of_mem ht,mul_one]
      exact hz ht.2
    · simp [f,ht]
  exact (ae_restrict_iff' hS).mp hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSliceIntegral_continuous_of_boundary_null {U : Set Torus} (hU : MeasurableSet U)
    (i : Fin 3) (hn : ∀ t : AxisCircle,volume (axialSlice (frontier U) i t)=0)
    {f : Torus → ℝ} (hf : Continuous f) : Continuous (axialSliceIntegral U i f) := by
  let g : C(Torus,ℝ) := ⟨f,hf⟩
  let C := ‖g‖
  have hC (z : Torus) : ‖f z‖ ≤ C := g.norm_coe_le_norm z
  rw [show axialSliceIntegral U i f=(fun t ↦ ∫ y,U.indicator f ((torusAxialSplit i).symm (t,y))) from
    funext (axialSliceIntegral_indicator hU i f)]
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_of_dominated (bound := fun _ ↦ max C 0)
  · apply Eventually.of_forall
    intro s
    exact (hf.measurable.indicator hU |>.comp ((torusAxialSplit i).symm.measurable.comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  · apply Eventually.of_forall
    intro s
    apply ae_of_all
    intro y
    exact (norm_indicator_le_norm_self _ _).trans ((hC _).trans (le_max_left _ _))
  · exact integrable_const _
  · have hnb : ∀ᵐ y : TransverseProduct,(torusAxialSplit i).symm (t,y)∉frontier U := by
      rw [ae_iff]
      simpa only [not_not,axialSlice] using hn t
    filter_upwards [hnb] with y hy
    exact ContinuousAt.comp (f := fun s ↦ (torusAxialSplit i).symm (s,y))
      (g := U.indicator f) (hf.continuousOn.continuousAt_indicator hy)
      (axialSlice_point_continuous i y).continuousAt

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma circle_continuous_le_of_local_ae {f g : AxisCircle → ℝ}
    (hf : Continuous f) (hg : Continuous g) {S : Set AxisCircle} (hS : IsOpen S)
    {t : AxisCircle} (ht : t∈S) (ha : ∀ᵐ s,s∈S → f s≤g s) : f t≤g t := by
  by_contra! hbad
  let A : Set AxisCircle := S∩{s | g s<f s}
  have hAo : IsOpen A := hS.inter (isOpen_lt hg hf)
  have hpos := hAo.measure_pos volume ⟨t,ht,hbad⟩
  have hz : volume A=0 := by
    have hh : ∀ᵐ s : AxisCircle,s∉A := by
      filter_upwards [ha] with s hs
      intro hm
      exact (not_lt_of_ge (hs hm.1)) hm.2
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hh
  rw [hz] at hpos
  exact lt_irrefl _ hpos

theorem reflection_seam_planar_perimeter_le_flux {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (i : Fin 3) (hR : E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {t : AxisCircle} (ht : -t=t) :
    planarTorusPerimeter (axialSlice (openRepresentative E) i t)≤
      ENNReal.ofReal (actualAxialFlux (openRepresentative E) μ H i t) := by
  let O := openRepresentative E
  have hO : MeasurableSet O := (isOpen_openRepresentative E).measurableSet
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμO := hμ.congr_ae hOE.symm
  have hHO : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux O D.coordinate D.function := by
    intro D
    rw [hH]
    congr 1
    exact directionalFlux_congr_ae hOE.symm D.coordinate D.function
  have hnull := isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha
  have hvc := axialSliceVolume_continuous_of_boundary_null hO i hnull
  have hfluxc : Continuous (actualAxialFlux O μ H i) :=
    continuous_const.add (continuous_const.mul (hvc.sub continuous_const))
  rw [←axialTestPerimeter_eq_planar]
  refine iSup_le fun F ↦ iSup_le fun hF ↦ iSup_le fun hFi ↦ ENNReal.ofReal_le_ofReal ?_
  let I := axialSliceIntegral O i (fun z ↦ divergence F (representative z))
  have hd : Continuous (fun z : Torus ↦ divergence F (representative z)) :=
    continuous_periodic_descent (continuous_divergence hF.1) (divergence_periodic hF.2.1)
  have hIc : Continuous I := axialSliceIntegral_continuous_of_boundary_null hO i hnull hd
  have hI := axialSliceIntegral_ae_le hO hμO i ha hF hFi
  have hq := axialSurface_density_eq_flux hO hHO i
  have hc (c : ℝ) (hc : c∈Ioo 0 1) : c*I t≤actualAxialFlux O μ H i t := by
    obtain ⟨S,hSo,htS,hSn⟩ := normal_transverse_near_reflection_height hV hE hmin i hR hμ hN hp hae ht hc
    have hs := axial_density_local_comparison i ha hSo.measurableSet hSn
    apply circle_continuous_le_of_local_ae (continuous_const.mul hIc) hfluxc hSo htS
    filter_upwards [hI,hs,hq] with s hIs hss hqs
    intro hsS
    calc
      c*I s ≤ c*axialPerimeterDensity μ i s := mul_le_mul_of_nonneg_left hIs hc.1.le
      _ ≤ axialSecondDensity μ i s := hss hsS
      _ = actualAxialFlux O μ H i s := hqs
  have hclosed : IsClosed {c : ℝ | c*I t≤actualAxialFlux O μ H i t} :=
    isClosed_le (continuous_id.mul continuous_const) continuous_const
  have hsub := closure_minimal (show Ioo (0 : ℝ) 1⊆{c : ℝ | c*I t≤actualAxialFlux O μ H i t} from hc) hclosed
  have hmem : (1 : ℝ)∈closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ)≠1)]
    norm_num
  simpa only [mem_ofPred_eq,one_mul] using hsub hmem

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma congruentAE_congr_ae_left {E F K : Set Torus} (h : E=ᵐ[torusVolume]F) :
    CongruentAE E K ↔ CongruentAE F K := by
  constructor
  · rintro ⟨φ,hφ⟩; exact ⟨φ,h.symm.trans hφ⟩
  · rintro ⟨φ,hφ⟩; exact ⟨φ,h.trans hφ⟩

lemma smallStandardRegion_congr_ae {E F : Set Torus} (h : E=ᵐ[torusVolume]F) (V : ℝ) :
    SmallStandardRegion V E ↔ SmallStandardRegion V F := by
  simp only [SmallStandardRegion,congruentAE_congr_ae_left h]

lemma standardRegionAt_congr_ae {E F : Set Torus} (h : E=ᵐ[torusVolume]F) (V : ℝ) :
    StandardRegionAt V E ↔ StandardRegionAt V F := by
  have hh : Eᶜ=ᵐ[torusVolume]Fᶜ := by
    filter_upwards [h] with x hx
    exact congrArg Not hx
  unfold StandardRegionAt
  split_ifs
  · exact smallStandardRegion_congr_ae h V
  · exact smallStandardRegion_congr_ae hh (1-V)

end CubicTorus

end
end

section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_openRepresentative_ae_nullMeasurable {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) : openRepresentative E =ᵐ[torusVolume] E := by
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F =ᵐ[torusVolume] E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).2 hmin
  have hUF := isMinimizerAt_openRepresentative_ae hV hF hmF
  rw [openRepresentative_congr_ae hFE] at hUF
  exact hUF.trans hFE

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axisFixedHeights_neg_eq {t : AxisCircle} (ht : t∈axisFixedHeights) : -t=t := by
  rcases ht with rfl|ht
  · simp
  have he : t=((1/2 : ℝ) : AxisCircle) := by simpa only [mem_singleton_iff] using ht
  rw [he]
  apply neg_eq_iff_add_eq_zero.mpr
  rw [←AddCircle.coe_add]
  norm_num [AddCircle.coe_period]

theorem isMinimizerAt_nonstandard_seam_perimeters {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ i : Fin 3,(axialAreaMarginal μ i : Measure AxisCircle)≪volume) ∧
      ∀ i : Fin 3,∀ t∈axisFixedHeights,
        planarTorusPerimeter (axialSlice (openRepresentative E) i t)≤
          ENNReal.ofReal (actualAxialFlux (openRepresentative E) μ H i t) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have hsF : ¬StandardRegionAt V F := fun hs ↦ hstd ((standardRegionAt_congr_ae hFE V).mp hs)
  have hcF : IsPreconnected (frontier (openRepresentative F)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV' hmF).resolve_right (fun h ↦ hsF h.2.2)
  have hRF (i : Fin 3) : F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F) :=
    hFE.trans ((hR i).trans ((axisReflection i).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  obtain ⟨μ,H,hμ,hCMC,_,_⟩ := isMinimizerAt_CMC_sign hV' hF hmF
  obtain ⟨N,hN,hp,hae,_⟩ := isMinimizerAt_stationary_tubular_normal hV' hF hmF hμ hCMC
  obtain ⟨b,hsg⟩ := isMinimizerAt_nonstandard_strict_signs_of_actual_normal hV hF hmF hcF hsF hRF hμ hN hp hae
  have hH := Periodic.coordinateCMC_of_global hμ hCMC
  have hn (i : Fin 3) := strict_normal_component_ne_zero_ae hV' hF hmF hRF hμ hH hN hp hae hsg i
  have ha (i : Fin 3) := axialAreaMarginal_absolutelyContinuous hH hn i
  refine ⟨μ,H,hμ.congr_ae hFE,hCMC,ha,fun i t ht ↦ ?_⟩
  have hh := reflection_seam_planar_perimeter_le_flux hV' hF hmF i (hRF i) hμ hH (ha i) hN hp hae
    (axisFixedHeights_neg_eq ht)
  rwa [openRepresentative_congr_ae hFE] at hh

theorem isMinimizerAt_missing_neighbor_seam_bound {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    planarTorusPerimeter (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))≤
      ENNReal.ofReal (H*(axialSliceVolume (openRepresentative E) i (octantHeight b i 0 : AxisCircle)).toReal) := by
  obtain ⟨N,hN,hp,hae,_⟩ := isMinimizerAt_stationary_tubular_normal hV hE hmin hμ hCMC
  have hH := Periodic.coordinateCMC_of_global hμ hCMC
  have hfix : -(octantHeight b i 0 : AxisCircle)=(octantHeight b i 0 : AxisCircle) := by
    unfold octantHeight
    cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · norm_num [AddCircle.coe_period]
    · exact axisFixedHeights_neg_eq (by simp [axisFixedHeights])
  have hh := reflection_seam_planar_perimeter_le_flux hV hE hmin i (hR i) hμ hH ha hN hp hae hfix
  have hf := isMinimizerAt_missing_neighbor_flux_unrestricted hV hE hmin hR b hd hμ hH i hv
  have hvol : torusVolume.real (openRepresentative E)=V := by
    rw [measureReal_def,measure_congr (isMinimizerAt_openRepresentative_ae hV hE hmin),
      hmin.2.1,ENNReal.toReal_ofReal hV.1.le]
  convert hh using 1
  congr 1
  rw [actualAxialFlux,hf,hvol]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_bottom_extent_calibration {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (hout : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E))
    (hin0 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==0))∈openRepresentative E)
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    0<H*s ∧ Real.pi*(1-s)≤((H/2)*s)^2 ∧
      ∃ L : ℝ,L∈Ioo 0 1 ∧
        (∀ y∈centeredAxialSlice (openRepresentative Eᶜ) (fun k ↦ !b k) i (octantHeight b i 0 : AxisCircle),2*‖y 1‖<L) ∧
        (1-s)/L+Real.pi*L/4≤(H/2)*s := by
  dsimp only
  let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
  have hs : 0 ≤ s := measureReal_nonneg
  have hs1 : s ≤ 1 := by
    have hv : volume (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))≤1 := by
      simpa using (measure_mono (subset_univ (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))) : volume _≤volume univ)
    exact (ENNReal.toReal_mono ENNReal.one_ne_top hv).trans_eq ENNReal.toReal_one
  have hn := isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha (octantHeight b i 0 : AxisCircle)
  obtain ⟨L,hL,hband,hcal,hdisk⟩ := isMinimizerAt_section_complement_calibration hV hmin hR hd i (octantHeight b i 0) hout hin0 hin1 hn
  have hp := isMinimizerAt_missing_neighbor_seam_bound hV hE hmin hR b hd hμ hCMC i ha hv
  change planarTorusPerimeter _≤ENNReal.ofReal (H*s) at hp
  have hand : ENNReal.ofReal ((1-s)/L+Real.pi*L)≤ENNReal.ofReal (H*s) := hcal.trans hp
  have hpos : 0<(1-s)/L+Real.pi*L := add_pos_of_nonneg_of_pos
    (div_nonneg (sub_nonneg.mpr hs1) hL.1.le) (mul_pos Real.pi_pos hL.1)
  have hcal' : (1-s)/L+Real.pi*L≤H*s := by
    rcases ENNReal.ofReal_le_ofReal_iff'.mp hand with hh|hh
    · exact hh
    · exact (not_le_of_gt hpos hh).elim
  have hHs : 0<H*s := hpos.trans_le hcal'
  have hdk : 2*Real.sqrt (Real.pi*(1-s))≤H*s :=
    (ENNReal.ofReal_le_ofReal_iff hHs.le).mp (hdisk.trans hp)
  have hsq := Real.sq_sqrt (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hs1))
  have hsqrt := Real.sqrt_nonneg (Real.pi*(1-s))
  refine ⟨hHs,?_,2*L,⟨mul_pos (by norm_num) hL.1,by linarith [hL.2]⟩,?_,?_⟩
  · nlinarith [sq_nonneg (H*s-2*Real.sqrt (Real.pi*(1-s)))]
  · intro y hy
    linarith [hband y hy]
  · have he : (1-s)/(2*L)+Real.pi*(2*L)/4=((1-s)/L+Real.pi*L)/2 := by field_simp; ring
    rw [he]
    nlinarith [hcal']

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def planeSwap : Plane ≃ₗᵢ[ℝ] Plane :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)

def planarSwap : TransverseProduct ≃ᵐ TransverseProduct :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin 2 ↦ AxisCircle) (Equiv.swap (0 : Fin 2) 1)

@[simp] lemma planeSwap_apply (x : Plane) (j : Fin 2) :
    planeSwap x j=x (Equiv.swap 0 1 j) := rfl
@[simp] lemma planarSwap_apply (y : TransverseProduct) (j : Fin 2) :
    planarSwap y j=y (Equiv.swap 0 1 j) := by
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin 2 ↦ AxisCircle) (Equiv.swap (0 : Fin 2) 1) y (Equiv.swap 0 1 j)
  simpa only [planarSwap,Equiv.swap_apply_self] using h
@[simp] lemma planeSwap_involutive (x : Plane) : planeSwap (planeSwap x)=x := by
  ext j; simp
@[simp] lemma planarSwap_involutive (x : TransverseProduct) : planarSwap (planarSwap x)=x := by
  ext j; simp

lemma planarSwap_measurePreserving : MeasurePreserving planarSwap :=
  volume_measurePreserving_piCongrLeft _ _

lemma planeSwap_single (j : Fin 2) : planeSwap (EuclideanSpace.single j 1)=
    EuclideanSpace.single (Equiv.swap 0 1 j) 1 := by
  ext k
  fin_cases j <;> fin_cases k <;> simp

lemma planeDivergence_swap {F : Plane →Plane} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (x : Plane) :
    planeDivergence (fun y ↦ planeSwap (F (planeSwap y))) x=planeDivergence F (planeSwap x) := by
  have hd := planeSwap.toContinuousLinearEquiv.hasFDerivAt.comp x
    (((hF.differentiable (by simp) _).hasFDerivAt).comp x planeSwap.toContinuousLinearEquiv.hasFDerivAt)
  change HasFDerivAt (fun y ↦ planeSwap (F (planeSwap y))) _ x at hd
  rw [planeDivergence,hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    planeDivergence]
  simp
  rw [planeSwap_single,planeSwap_single]
  norm_num
  ring

lemma planarAdmissibleField_swap {F : Plane →Plane} (hF : PlanarAdmissibleField F) :
    PlanarAdmissibleField (fun y ↦ planeSwap (F (planeSwap y))) := by
  refine ⟨planeSwap.contDiff.comp (hF.1.comp planeSwap.contDiff),?_,?_⟩
  · intro n y
    change planeSwap (F (planeSwap (y+WithLp.toLp 2 (fun j ↦ (n j : ℝ)))))=planeSwap (F (planeSwap y))
    rw [map_add]
    have he : planeSwap (WithLp.toLp 2 (fun j ↦ (n j : ℝ)))=
        WithLp.toLp 2 (fun j ↦ ((n (Equiv.swap 0 1 j)) : ℝ)) := by ext j; rfl
    rw [he,hF.2.1]
  · intro y
    rw [planeSwap.norm_map]
    exact hF.2.2 _

lemma planeSwap_representative (y : TransverseProduct) :
    planeSwap (planarRepresentative y)=planarRepresentative (planarSwap y) := by
  ext j
  simp only [planeSwap_apply,planarRepresentative,planarSwap_apply]

lemma planarTorusPerimeter_swap_le (A : Set TransverseProduct) :
    planarTorusPerimeter (planarSwap ⁻¹' A)≤planarTorusPerimeter A := by
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  let G : Plane →Plane := fun y ↦ planeSwap (F (planeSwap y))
  have hG : PlanarAdmissibleField G := planarAdmissibleField_swap hF
  have hh := planarSwap_measurePreserving.setIntegral_preimage_emb planarSwap.measurableEmbedding
    (fun y ↦ planeDivergence G (planarRepresentative y)) A
  have he : (fun y ↦ planeDivergence G (planarRepresentative (planarSwap y)))=
      (fun y ↦ planeDivergence F (planarRepresentative y)) := by
    funext y
    rw [show planeDivergence G (planarRepresentative (planarSwap y))=planeDivergence F (planeSwap (planarRepresentative (planarSwap y))) from planeDivergence_swap hF.1 _,
      planeSwap_representative,planarSwap_involutive]
  rw [he] at hh
  rw [hh]
  exact le_iSup_of_le G (le_iSup_of_le hG le_rfl)

theorem planarTorusPerimeter_swap (A : Set TransverseProduct) :
    planarTorusPerimeter (planarSwap ⁻¹' A)=planarTorusPerimeter A := by
  refine le_antisymm (planarTorusPerimeter_swap_le A) ?_
  have hh := planarTorusPerimeter_swap_le (planarSwap ⁻¹' A)
  have he : planarSwap ⁻¹' (planarSwap ⁻¹' A)=A := by ext y; simp
  rwa [he] at hh

lemma planar_volume_swap (A : Set TransverseProduct) :
    volume.real (planarSwap ⁻¹' A)=volume.real A := by
  apply congrArg ENNReal.toReal
  exact planarSwap_measurePreserving.measure_preimage_emb planarSwap.measurableEmbedding A

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planarSwap_continuous : Continuous planarSwap := by
  apply continuous_pi
  intro j
  simpa only [planarSwap_apply] using (continuous_apply (Equiv.swap 0 1 j) : Continuous (fun y : TransverseProduct ↦ y (Equiv.swap 0 1 j)))

lemma planarSwap_closure_subset (A : Set TransverseProduct) :
    closure (planarSwap ⁻¹' A)⊆planarSwap ⁻¹' closure A :=
  closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage planarSwap_continuous)

lemma planarRadialDownset_swap {A : Set TransverseProduct} (hd : PlanarRadialDownset A) :
    PlanarRadialDownset (planarSwap ⁻¹' A) := by
  intro y z hyz hz
  apply hd (planarSwap y) (planarSwap z) _ hz
  intro j
  simpa only [planarSwap_apply] using hyz (Equiv.swap 0 1 j)

@[simp] lemma planarSwap_zero : planarSwap (0 : TransverseProduct)=0 := by ext j; simp

@[simp] lemma planarSwap_firstAxisPoint (t : ℝ) : planarSwap (planarFirstAxisPoint t)=planarAxisPoint t := by
  ext j
  fin_cases j <;> simp [planarFirstAxisPoint,planarAxisPoint]

@[simp] lemma planarSwap_secondAxisPoint (t : ℝ) : planarSwap (planarAxisPoint t)=planarFirstAxisPoint t := by
  rw [←planarSwap_firstAxisPoint,planarSwap_involutive]

lemma planar_radial_full_calibration {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout0 : planarFirstAxisPoint (1/2)∉closure A)
    (hout1 : planarAxisPoint (1/2)∉closure A) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y 1‖<L) ∧
      (∀ y : TransverseProduct,y 0=0 →‖y 1‖<L →y∈A) ∧
      ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  obtain ⟨L,hL,hband,hin⟩ := planar_radial_extent hA hd h0 hout1
  refine ⟨L,hL,hband,?_,planarTorusPerimeter_ge_semicircle_calibration hA hL ?_ hin
    (planar_radial_empty_fiber hd hout0)⟩
  · intro y hy0 hy1
    obtain ⟨t,he,ht⟩ := axisCircle_exists_centered_rep (y 1)
    exact hin t (ht.trans_lt hy1) y hy0 he.symm
  · intro y hy
    obtain ⟨t,he,ht⟩ := axisCircle_exists_centered_rep (y 1)
    exact ⟨t,ht ▸ hband y hy,he⟩

theorem planar_radial_both_extents {A : Set TransverseProduct} (hA : IsOpen A)
    (hd : PlanarRadialDownset A) (h0 : (0 : TransverseProduct)∈A)
    (hout0 : planarFirstAxisPoint (1/2)∉closure A)
    (hout1 : planarAxisPoint (1/2)∉closure A) (j : Fin 2) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈A,‖y j‖<L) ∧
      (∀ y : TransverseProduct,(∀ k : Fin 2,k≠j →y k=0) →‖y j‖<L →y∈A) ∧
      ENNReal.ofReal (volume.real A/L+Real.pi*L)≤planarTorusPerimeter A := by
  fin_cases j
  · have h0' : (0 : TransverseProduct)∈planarSwap ⁻¹' A := by simpa using h0
    have hout0' : planarFirstAxisPoint (1/2)∉closure (planarSwap ⁻¹' A) := by
      intro hh
      apply hout1
      simpa only [mem_preimage,planarSwap_firstAxisPoint] using planarSwap_closure_subset A hh
    have hout1' : planarAxisPoint (1/2)∉closure (planarSwap ⁻¹' A) := by
      intro hh
      apply hout0
      simpa only [mem_preimage,planarSwap_secondAxisPoint] using planarSwap_closure_subset A hh
    obtain ⟨L,hL,hband,hin,hp⟩ := planar_radial_full_calibration (hA.preimage planarSwap_continuous)
      (planarRadialDownset_swap hd) h0' hout0' hout1'
    refine ⟨L,hL,?_,?_,?_⟩
    · intro y hy
      have hb := hband (planarSwap y) (by simpa using hy)
      simpa using hb
    · intro y hzero hy
      have hb := hin (planarSwap y) (by simpa using hzero 1 (by decide)) (by simpa using hy)
      simpa using hb
    · simpa only [planar_volume_swap,planarTorusPerimeter_swap] using hp
  · obtain ⟨L,hL,hband,hin,hp⟩ := planar_radial_full_calibration hA hd h0 hout0 hout1
    exact ⟨L,hL,hband,fun y hzero hy ↦ hin y (hzero 0 (by decide)) hy,hp⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_section_both_extents {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) (t : ℝ)
    (hin : quotientMap (axialSectionCorner b i t (fun _ ↦ false))∈openRepresentative E)
    (hout0 : quotientMap (axialSectionCorner b i t (fun j ↦ j==0))∉closure (openRepresentative E))
    (hout1 : quotientMap (axialSectionCorner b i t (fun j ↦ j==1))∉closure (openRepresentative E))
    (j : Fin 2) :
    ∃ L : ℝ,L∈Ioo 0 (1/2) ∧
      (∀ y∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle),‖y j‖<L) ∧
      (∀ y : TransverseProduct,(∀ k : Fin 2,k≠j →y k=0) →‖y j‖<L →
        y∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)) ∧
      ENNReal.ofReal (volume.real (axialSlice (openRepresentative E) i (t : AxisCircle))/L+Real.pi*L)≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i (t : AxisCircle)) := by
  have hzero : (0 : TransverseProduct)∈centeredAxialSlice (openRepresentative E) b i (t : AxisCircle) := by
    change (torusAxialSplit i).symm ((t : AxisCircle),0+axialSectionCenter b i)∈openRepresentative E
    rwa [centered_section_zero]
  have hv0 : planarFirstAxisPoint (1/2)∉closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)) := by
    intro hh
    have hz := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
    change (torusAxialSplit i).symm ((t : AxisCircle),planarFirstAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hz
    rw [centered_section_first_axis] at hz
    exact hout0 hz
  have hv1 : planarAxisPoint (1/2)∉closure (centeredAxialSlice (openRepresentative E) b i (t : AxisCircle)) := by
    intro hh
    have hz := centeredAxialSlice_closure_subset (openRepresentative E) b i (t : AxisCircle) hh
    change (torusAxialSplit i).symm ((t : AxisCircle),planarAxisPoint (1/2)+axialSectionCenter b i)∈closure (openRepresentative E) at hz
    rw [centered_section_second_axis] at hz
    exact hout1 hz
  have hp := planar_radial_both_extents (centeredAxialSlice_isOpen (isOpen_openRepresentative E) b i _)
    (isMinimizerAt_centered_section_radial hV hmin hR hd i _) hzero hv0 hv1 j
  simpa only [centeredAxialSlice_volume,centeredAxialSlice_perimeter] using hp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
