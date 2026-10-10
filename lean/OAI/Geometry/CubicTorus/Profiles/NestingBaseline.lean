import Mathlib
import OAI.Geometry.CubicTorus.Profiles.SharpSectionWeight

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_measurable_weighted_area_bound {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγn : ∀ x,0≤γ x)
    (hγw : ∀ᵐ t,γ ((axialSliceVolume (openRepresentative E) i t).toReal)≤
      Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/axialPerimeterDensity μ i t))
    {τ : ℝ} (hτ : τ∈Icc (0 : ℝ) 1) :
    Nesting.lambda*axialTransverseMass μ i+
      2*|∫ y in (axialSliceVolume (openRepresentative E) i 0).toReal..
        (axialSliceVolume (openRepresentative E) i (τ : AxisCircle)).toReal,γ y|≤
      (perimeter E).toReal := by
  let O := openRepresentative E
  have hO : MeasurableSet O := (isOpen_openRepresentative E).measurableSet
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμO := hμ.congr_ae hOE.symm
  have hHO (D : Periodic.Variation) : Periodic.normalFirstVariation μ D=
      H*directionalFlux O D.coordinate D.function := by rw [directionalFlux_congr_ae hOE]; exact hH D
  let v : AxisCircle → ℝ := fun t ↦ (axialSliceVolume O i t).toReal
  have hv : Continuous v := axialSliceVolume_continuous_of_boundary_null hO i
    (isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha)
  have hp : Function.Periodic (fun t : ℝ ↦ v (t : AxisCircle)) 1 := by
    intro t
    change v (((t+1 : ℝ) : AxisCircle))=v (t : AxisCircle)
    rw [AddCircle.coe_add_period]
  have hc : Continuous (fun t : ℝ ↦ v (t : AxisCircle)) := hv.comp (AddCircle.continuous_mk' (1 : ℝ))
  obtain ⟨hac,hd⟩ := isMinimizerAt_slice_absolutelyContinuous hV hE hmin hμ i ha
  have hlift (t : AxisCircle) : hp.lift t=v t := by
    induction t using Quotient.inductionOn with | h t => rfl
  have hwEq : (fun t ↦ Nesting.weight (actualAxialFlux O μ H i t/axialPerimeterDensity μ i t)*
      |axialNormalDensity μ i t|)=ᵐ[volume](fun t ↦ Nesting.weight
        (axialSecondDensity μ i t/axialPerimeterDensity μ i t)*|axialNormalDensity μ i t|) := by
    filter_upwards [axialSurface_density_eq_flux hO hHO i] with t ht
    rw [←ht]
    rfl
  have hlarge := (axial_weighted_normal_integrable μ i).congr hwEq.symm
  have hsmall : Integrable (fun t ↦ γ (v t)*|axialNormalDensity μ i t|) := by
    apply hlarge.mono' ((hγ.comp hv.measurable).mul (axialNormalDensity_measurable μ i).abs).aestronglyMeasurable
    filter_upwards [hγw] with t ht
    simp only [Pi.mul_apply,Function.comp_apply,Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (hγn _) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _)
  have hwint : Integrable (fun t ↦ γ (hp.lift t)*|(-axialNormalDensity μ i) t|) := by
    simpa only [hlift,Pi.neg_apply,abs_neg] using hsmall
  have hb := circle_ac_measurable_weight_integrable hp hc hac (axialNormalDensity_integrable μ i).neg hd hγ hγn hwint hτ
  simp only [hlift,Pi.neg_apply,abs_neg,AddCircle.coe_zero] at hb
  have him := integral_mono_ae hsmall hlarge (by
    filter_upwards [hγw] with t ht
    exact mul_le_mul_of_nonneg_right ht (abs_nonneg _))
  have hflux := axial_integrated_flux_actual hO hμO hHO i ha
  rw [perimeter_congr_ae hOE] at hflux
  change _≤(perimeter E).toReal
  have hh := hb.trans him
  exact (add_le_add le_rfl hh).trans hflux

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_missing_neighbor_slice_empty {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    axialSlice (openRepresentative E) i (octantHeight b i 1 : AxisCircle)=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  exact isMinimizerAt_missing_neighbor_gap hV hmin hR b hd i hv
    ((torusAxialSplit i).symm ((octantHeight b i 1 : AxisCircle),y))
    (subset_closure hy) (torusAxialSplit_symm_same _ _ _)

theorem isMinimizerAt_missing_neighbor_area_flux {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    {γ : ℝ → ℝ} (hγ : Measurable γ) (hγn : ∀ x,0≤γ x)
    (hγw : ∀ᵐ t,γ ((axialSliceVolume (openRepresentative E) i t).toReal)≤
      Nesting.weight (H*(axialSliceVolume (openRepresentative E) i t).toReal/
        axialPerimeterDensity μ i t)) :
    Nesting.lambda*H*V+2*(∫ s in (0 : ℝ)..
      (axialSliceVolume (openRepresentative E) i (octantHeight b i 0 : AxisCircle)).toReal,γ s)
      ≤(perimeter E).toReal := by
  have hf := isMinimizerAt_missing_neighbor_flux_unrestricted hV hE hmin hR b hd hμ hH i hv
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hvol : torusVolume.real (openRepresentative E)=V := by
    rw [measureReal_def,measure_congr hOE,hmin.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hg : ∀ᵐ t,γ ((axialSliceVolume (openRepresentative E) i t).toReal)≤
      Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/axialPerimeterDensity μ i t) := by
    filter_upwards [hγw] with t ht
    convert ht using 1
    congr 2
    rw [actualAxialFlux,hf,hvol]
    ring
  have hh := isMinimizerAt_measurable_weighted_area_bound hV hE hmin hμ hH i ha hγ hγn hg
    (τ := 1/2) (by constructor <;> norm_num)
  rw [hf] at hh
  have he : axialSliceVolume (openRepresentative E) i (octantHeight b i 1 : AxisCircle)=0 := by
    simp only [axialSliceVolume,isMinimizerAt_missing_neighbor_slice_empty hV hmin hR b hd i hv,measure_empty]
  have hni (x : ℝ) (hx : 0≤x) : 0≤∫ s in (0 : ℝ)..x,γ s :=
    intervalIntegral.integral_nonneg hx (fun s hs ↦ hγn s)
  unfold octantHeight at he ⊢
  cases hbi : b i <;> simp only [hbi,Bool.false_eq_true,ite_false,ite_true] at he ⊢
  · have hhalf : (1-1/2 : ℝ)=1/2 := by norm_num
    rw [hhalf] at he
    simp only [sub_zero,zero_div] at ⊢
    have hz : ((1 : ℝ) : AxisCircle)=0 := by simp
    rw [hz]
    rw [he,ENNReal.toReal_zero,intervalIntegral.integral_symm,abs_neg,
      abs_of_nonneg (hni _ ENNReal.toReal_nonneg)] at hh
    nlinarith [hh]
  · norm_num only at he ⊢
    have hz : ((1 : ℝ) : AxisCircle)=0 := by simp
    rw [hz] at he
    rw [he,ENNReal.toReal_zero,abs_of_nonneg (hni _ ENNReal.toReal_nonneg)] at hh
    nlinarith [hh]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_sharp_section_weight_ae {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 →Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ} (hH : 0≤H)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    ∀ᵐ t : AxisCircle,sharpSectionWeight H ((axialSliceVolume (openRepresentative E) i t).toReal)≤
      Nesting.weight (H*(axialSliceVolume (openRepresentative E) i t).toReal/axialPerimeterDensity μ i t) := by
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hO := (isOpen_openRepresentative E).measurableSet
  have hp := planarTorusPerimeter_slice_ae_le hO (hμ.congr_ae hOE.symm) i ha
  filter_upwards [hp,isMinimizerAt_planar_profile_circle hV hE hmin hR hd i] with t ht hs
  apply sharpSectionWeight_le hH
  · refine ⟨ENNReal.toReal_nonneg,?_⟩
    simpa using (ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞)≠⊤)
      (axialSliceVolume_le_one (openRepresentative E) i t))
  · exact axialPerimeterDensity_nonneg μ i t
  · have hh := ENNReal.toReal_mono (by simp) (hs.trans ht)
    simpa only [axialSliceVolume,measureReal_def,ENNReal.toReal_ofReal (unitPlanarProfile_nonneg _),
      ENNReal.toReal_ofReal (axialPerimeterDensity_nonneg μ i t)] using hh

theorem isMinimizerAt_missing_neighbor_sharp_area_flux {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ} (hH0 : 0≤H)
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    Nesting.lambda*H*V+2*(∫ s in (0 : ℝ)..
      (axialSliceVolume (openRepresentative E) i (octantHeight b i 0 : AxisCircle)).toReal,
        sharpSectionWeight H s)≤(perimeter E).toReal := by
  exact isMinimizerAt_missing_neighbor_area_flux hV hE hmin hR b hd hμ hH i ha hv
    (sharpSectionWeight_measurable H) (sharpSectionWeight_nonneg hH0)
    (isMinimizerAt_sharp_section_weight_ae hV hE hmin hR hd hμ hH0 i ha)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_improved_section_weight_ae {V : ℝ} (hV : V∈Ioo 0 1)
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
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E)
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    let δ := nestingDelta (H/2) s
    ∀ᵐ t : AxisCircle,improvedSectionWeight H δ ((axialSliceVolume (openRepresentative E) i t).toReal)≤
      Nesting.weight (H*(axialSliceVolume (openRepresentative E) i t).toReal/axialPerimeterDensity μ i t) := by
  intro s δ
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hO := (isOpen_openRepresentative E).measurableSet
  have hp := planarTorusPerimeter_slice_ae_le hO (hμ.congr_ae hOE.symm) i ha
  have hbase := isMinimizerAt_planar_profile_circle hV hE hmin hR hd i
  have himp : ∀ᵐ t : AxisCircle,0<δ →
      volume.real (axialSlice (openRepresentative E) i t)∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2)) →
      ENNReal.ofReal (2*Real.sqrt (1+Shape.c*δ^2*Shape.shape ((volume.real (axialSlice (openRepresentative E) i t)-Shape.u (H/2)+δ)/δ)))≤
        planarTorusPerimeter (axialSlice (openRepresentative E) i t) := by
    by_cases hδ : 0<δ
    · filter_upwards [isMinimizerAt_nesting_improved_profile_circle hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1 hH hδ] with t ht
      exact fun _ ↦ ht
    · exact Filter.Eventually.of_forall (fun _ h ↦ (hδ h).elim)
  filter_upwards [hp,hbase,himp] with t ht hs hi
  apply improvedSectionWeight_le_density hH (nestingDelta_mem _ _)
  · exact ⟨ENNReal.toReal_nonneg,by simpa using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞)≠⊤) (axialSliceVolume_le_one (openRepresentative E) i t)⟩
  · exact axialPerimeterDensity_nonneg μ i t
  · have hh := ENNReal.toReal_mono (by simp) (hs.trans ht)
    simpa only [axialSliceVolume,measureReal_def,ENNReal.toReal_ofReal (unitPlanarProfile_nonneg _),ENNReal.toReal_ofReal (axialPerimeterDensity_nonneg μ i t)] using hh
  · intro hδ htv
    have hh := ENNReal.toReal_mono (by simp) ((hi hδ htv).trans ht)
    rw [ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (axialPerimeterDensity_nonneg μ i t)] at hh
    exact hh

theorem isMinimizerAt_missing_neighbor_improved_area_flux {V : ℝ} (hV : V∈Ioo 0 1)
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
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E)
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    let δ := nestingDelta (H/2) s
    Nesting.lambda*H*V+2*(∫ v in (0 : ℝ)..s,improvedSectionWeight H δ v)≤(perimeter E).toReal := by
  intro s δ
  exact isMinimizerAt_missing_neighbor_area_flux hV hE hmin hR b hd hμ
    (Periodic.coordinateCMC_of_global hμ hCMC) i ha hv
    (improvedSectionWeight_measurable H δ) (fun v ↦ (improvedSectionWeight_mem hH (nestingDelta_mem _ _) v).1)
    (isMinimizerAt_improved_section_weight_ae hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1 hH)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma unitPlanarProfile_middle {v : ℝ} (hv : v∈Icc (1/Real.pi) (1-1/Real.pi)) :
    unitPlanarProfile v=2 := by
  have h0 : (1 : ℝ) ≤ Real.pi*v := by
    have := mul_le_mul_of_nonneg_left hv.1 Real.pi_pos.le
    have hp : Real.pi*(1/Real.pi)=1 := by field_simp
    rwa [hp] at this
  have h1 : (1 : ℝ) ≤ Real.pi*(1-v) := by
    have := mul_le_mul_of_nonneg_left hv.2 Real.pi_pos.le
    have hp : Real.pi*(1/Real.pi)=1 := by field_simp
    nlinarith
  have hs0 : (1 : ℝ) ≤ Real.sqrt (Real.pi*v) := by simpa using Real.sqrt_le_sqrt h0
  have hs1 : (1 : ℝ) ≤ Real.sqrt (Real.pi*(1-v)) := by simpa using Real.sqrt_le_sqrt h1
  simp only [unitPlanarProfile,min_eq_left (show (2 : ℝ) ≤ 2*Real.sqrt (Real.pi*(1-v)) by linarith)]
  exact min_eq_right (by linarith)

lemma sharpSectionWeight_middle {H δ v : ℝ}
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) (hδ : δ∈Icc 0 Shape.dm)
    (hv : v∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2))) :
    sharpSectionWeight H v=Nesting.weight ((H/2)*v) := by
  have hp := Shape.interval_placement hH
  have hvpi : v∈Icc (1/Real.pi) (1-1/Real.pi) := ⟨by linarith [hp.2.1,hp.2.2.1,hδ.2,hv.1],hv.2.trans hp.2.2.2.1⟩
  have hv0 : 0 ≤ v := by linarith [hp.2.1,hδ.2,hv.1]
  have hinv : 0<1/Real.pi := by positivity
  have hv1 : v<1 := lt_of_le_of_lt hvpi.2 (by linarith)
  rw [sharpSectionWeight,ite_eq_left ⟨hv0,hv1⟩,unitPlanarProfile_middle hvpi]
  congr 1
  ring

lemma improvedSectionWeight_ge_sharp {H δ : ℝ}
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) (hδ : δ∈Icc 0 Shape.dm) (v : ℝ) :
    sharpSectionWeight H v ≤ improvedSectionWeight H δ v := by
  unfold improvedSectionWeight
  split_ifs with hm
  · rw [sharpSectionWeight_middle hH hδ hm.2]
    let q := (v-Shape.u (H/2)+δ)/δ
    have hq : q∈Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hm.2.1]) hm.1.le,(div_le_one hm.1).mpr (by linarith [hm.2.2])⟩
    have hK : 0 ≤ Shape.c*δ^2*Shape.shape q := mul_nonneg (by norm_num [Shape.c]; positivity) (Shape.shape_nonneg hq)
    have hs : (1 : ℝ) ≤ Real.sqrt (1+Shape.c*δ^2*Shape.shape q) := by simpa using Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1+Shape.c*δ^2*Shape.shape q by linarith)
    have hv0 : 0 ≤ v := by linarith [(Shape.interval_placement hH).2.1,hδ.2,hm.2.1]
    have hh0 : 0 ≤ H/2 := by linarith [hH.1]
    apply Nesting.antitoneOn_weight
    · exact div_nonneg (mul_nonneg hh0 hv0) (Real.sqrt_nonneg _)
    · exact mul_nonneg hh0 hv0
    · exact div_le_self (mul_nonneg hh0 hv0) hs
  · exact le_rfl

lemma sharpSectionWeight_mem {H : ℝ} (hH : 0 ≤ H) (v : ℝ) : sharpSectionWeight H v∈Icc 0 1 := by
  refine ⟨sharpSectionWeight_nonneg hH v,?_⟩
  unfold sharpSectionWeight
  split_ifs with hs
  · exact (Nesting.weight_mem (div_nonneg (mul_nonneg hH hs.1) (unitPlanarProfile_nonneg _))).2
  · norm_num [Nesting.ell]

lemma improvedSectionWeight_integrable {H δ : ℝ}
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) (hδ : δ∈Icc 0 Shape.dm) (a b : ℝ) :
    IntervalIntegrable (improvedSectionWeight H δ) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' (improvedSectionWeight_measurable H δ).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun v ↦ by dsimp only; rw [Real.norm_eq_abs,abs_of_nonneg (improvedSectionWeight_mem hH hδ v).1]; exact (improvedSectionWeight_mem hH hδ v).2)

lemma sharpSectionWeight_integrable {H : ℝ} (hH : 0 ≤ H) (a b : ℝ) :
    IntervalIntegrable (sharpSectionWeight H) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun' (sharpSectionWeight_measurable H).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun v ↦ by dsimp only; rw [Real.norm_eq_abs,abs_of_nonneg (sharpSectionWeight_mem hH v).1]; exact (sharpSectionWeight_mem hH v).2)

theorem improvedSectionWeight_area_gain {H δ s : ℝ}
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) (hδ : δ∈Icc 0 Shape.dm)
    (hs : Shape.t (H/2) ≤ s) :
    (∫ v in (0 : ℝ)..s,sharpSectionWeight H v)+
      min ((134/1000 : ℝ)*(H/2)^3) (36/100)*δ^3 ≤
        ∫ v in (0 : ℝ)..s,improvedSectionWeight H δ v := by
  have hh0 : 0 ≤ H := by linarith [hH.1]
  have hi (a b : ℝ) := improvedSectionWeight_integrable hH hδ a b
  have hb (a b : ℝ) := sharpSectionWeight_integrable hh0 a b
  let f : ℝ →ℝ := fun v ↦ improvedSectionWeight H δ v-sharpSectionWeight H v
  have hfi (a b : ℝ) : IntervalIntegrable f volume a b := (hi a b).sub (hb a b)
  have hp := Shape.interval_placement hH
  have hlu : 0 ≤ Shape.u (H/2)-δ := by linarith [hp.2.1,hδ.2]
  have hus : Shape.u (H/2) ≤ s := hp.2.2.2.2.1.le.trans hs
  have hmono := intervalIntegral.integral_mono_interval hlu (show Shape.u (H/2)-δ ≤ Shape.u (H/2) by linarith [hδ.1]) hus
    (Filter.Eventually.of_forall (fun v ↦ sub_nonneg.mpr (improvedSectionWeight_ge_sharp hH hδ v))) (hfi 0 s)
  have hgain : min ((134/1000 : ℝ)*(H/2)^3) (36/100)*δ^3 ≤ ∫ v in (Shape.u (H/2)-δ)..Shape.u (H/2),f v := by
    by_cases hz : δ=0
    · subst δ
      simp
    have hδ0 : 0<δ := lt_of_le_of_ne hδ.1 (Ne.symm hz)
    have hchange := intervalIntegral.smul_integral_comp_add_mul f (a := (0 : ℝ)) (b := (1 : ℝ)) δ (Shape.u (H/2)-δ)
    have heq : (∫ v in (Shape.u (H/2)-δ)..Shape.u (H/2),f v)=
        δ*(∫ q in (0 : ℝ)..1,(Nesting.weight (((H/2)*(Shape.u (H/2)-δ+δ*q))/Real.sqrt (1+Shape.c*δ^2*Shape.shape q))-Nesting.weight ((H/2)*(Shape.u (H/2)-δ+δ*q)))) := by
      rw [show Shape.u (H/2)-δ+δ*0=Shape.u (H/2)-δ by ring,show Shape.u (H/2)-δ+δ*1=Shape.u (H/2) by ring] at hchange
      rw [←hchange,smul_eq_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro q hq
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hq
      have hv : Shape.u (H/2)-δ+δ*q∈Icc (Shape.u (H/2)-δ) (Shape.u (H/2)) := ⟨by nlinarith [mul_nonneg hδ.1 hq.1],by nlinarith [mul_le_mul_of_nonneg_left hq.2 hδ.1]⟩
      dsimp only [f]
      rw [sharpSectionWeight_middle hH hδ hv,improvedSectionWeight,ite_eq_left ⟨hδ0,hv⟩]
      have hqeq : (Shape.u (H/2)-δ+δ*q-Shape.u (H/2)+δ)/δ=q := by field_simp; ring
      rw [hqeq]
    rw [heq]
    exact NestingGain.integrated_uniform_gain hH hδ
  have hg := hgain.trans hmono
  rw [intervalIntegral.integral_sub (hi 0 s) (hb 0 s)] at hg
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nesting_cubic_gain {V : ℝ} (hV : V∈Ioo 0 1)
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
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E)
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    let δ := nestingDelta (H/2) s
    Nesting.lambda*H*V+2*((∫ v in (0 : ℝ)..s,sharpSectionWeight H v)+
      min ((134/1000 : ℝ)*(H/2)^3) (36/100)*δ^3)≤(perimeter E).toReal := by
  intro s δ
  have hi := isMinimizerAt_missing_neighbor_improved_area_flux hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1 hH
  obtain ⟨_,hdisc,_⟩ := isMinimizerAt_bottom_both_extents hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1
  have hs : Shape.t (H/2) ≤ s := source_root_le_of_bottom (by linarith [hH.1]) measureReal_nonneg hdisc
  have hg := improvedSectionWeight_area_gain hH (nestingDelta_mem (H/2) s) hs
  dsimp only at hi
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def nestingBaseline (h : ℝ) : ℝ :=
  Nesting.lambda*h/Real.pi+(∫ v in (0 : ℝ)..Shape.t h,sharpSectionWeight (2*h) v)-1

def nestingC0 (h : ℝ) : ℝ := min ((134/1000 : ℝ)*h^3) (36/100)
def nestingP (h : ℝ) : ℝ := Shape.u h-1+2*h*Shape.t h/Real.pi
def nestingQ (h : ℝ) : ℝ := (2/Real.pi)*Real.sqrt (Real.pi+2*h^2*Shape.t h)
def nestingExcess (h y : ℝ) : ℝ := Nesting.ell*y^2+
  nestingC0 h*(min Shape.dm (max (nestingP h-nestingQ h*y) 0))^3

def nestingGainInfimum (h : ℝ) : ℝ := sInf (nestingExcess h '' Ici 0)

lemma nestingExcess_nonneg {h : ℝ} (hh : 0 ≤ h) (y : ℝ) : 0 ≤ nestingExcess h y := by
  have hc : 0 ≤ nestingC0 h := le_min (mul_nonneg (by norm_num) (pow_nonneg hh 3)) (by norm_num)
  have hd : 0 ≤ min Shape.dm (max (nestingP h-nestingQ h*y) 0) := le_min (by norm_num [Shape.dm]) (le_max_right _ _)
  exact add_nonneg (mul_nonneg (by norm_num [Nesting.ell]) (sq_nonneg y)) (mul_nonneg hc (pow_nonneg hd 3))

lemma nestingGainInfimum_le {h y : ℝ} (hh : 0 ≤ h) (hy : 0 ≤ y) : nestingGainInfimum h ≤ nestingExcess h y := by
  apply csInf_le (show BddBelow (nestingExcess h '' Ici 0) from ⟨0,by rintro z ⟨y,hy,rfl⟩; exact nestingExcess_nonneg hh y⟩)
  exact ⟨y,hy,rfl⟩

lemma nestingExcess_at_sqrt {h s : ℝ} (hs : Shape.t h ≤ s) :
    nestingExcess h (Real.sqrt (s-Shape.t h))=
      Nesting.ell*(s-Shape.t h)+nestingC0 h*(nestingDelta h s)^3 := by
  have heq : nestingP h-nestingQ h*Real.sqrt (s-Shape.t h)=Shape.u h-nestingEndpointBound h s := by
    unfold nestingP nestingQ nestingEndpointBound
    ring
  simp only [nestingExcess,Real.sq_sqrt (sub_nonneg.mpr hs),heq,nestingDelta]

lemma sharpSectionWeight_ge_ell {H : ℝ} (hH : 0 ≤ H) (v : ℝ) : Nesting.ell ≤ sharpSectionWeight H v := by
  unfold sharpSectionWeight
  split_ifs with hm
  · exact (Nesting.weight_mem (div_nonneg (mul_nonneg hH hm.1) (unitPlanarProfile_nonneg _))).1
  · exact le_rfl

lemma nestingBaseline_slack {h s : ℝ} (hh : 0 ≤ h) (hs : Shape.t h ≤ s) :
    nestingBaseline h+Nesting.ell*(s-Shape.t h) ≤
      Nesting.lambda*h/Real.pi+(∫ v in (0 : ℝ)..s,sharpSectionWeight (2*h) v)-1 := by
  have hH : 0 ≤ 2*h := by positivity
  have hi (a b : ℝ) := sharpSectionWeight_integrable hH a b
  have hlow := intervalIntegral.integral_mono_on hs (intervalIntegrable_const (c := Nesting.ell)) (hi (Shape.t h) s)
    (fun v _ ↦ sharpSectionWeight_ge_ell hH v)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hlow
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hi 0 (Shape.t h)) (hi (Shape.t h) s)
  dsimp only [nestingBaseline]
  linarith

lemma nestingGainInfimum_actual_slack {h s : ℝ} (hh : 0 ≤ h) (hs : Shape.t h ≤ s) :
    nestingGainInfimum h ≤ Nesting.ell*(s-Shape.t h)+nestingC0 h*(nestingDelta h s)^3 := by
  have h := nestingGainInfimum_le hh (Real.sqrt_nonneg (s-Shape.t h))
  rwa [nestingExcess_at_sqrt hs] at h

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nesting_area_bound {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt (1/Real.pi) E)
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
    (hin1 : quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun j ↦ j==1))∈openRepresentative E)
    (hH : H/2∈Icc (51/50 : ℝ) (81/50 : ℝ)) :
    nestingBaseline (H/2)+nestingGainInfimum (H/2) ≤ (perimeter E).toReal/2-1 := by
  have hV : (1/Real.pi)∈Ioo (0 : ℝ) 1 := ⟨by positivity,(div_lt_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
  have hh := isMinimizerAt_nesting_cubic_gain hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1 hH
  obtain ⟨_,hdisc,_⟩ := isMinimizerAt_bottom_both_extents hV hE hmin hR b hd hμ hCMC i ha hv hout hin0 hin1
  have hH0 : 0 ≤ H/2 := by linarith [hH.1]
  have hs : Shape.t (H/2)  ≤  s := source_root_le_of_bottom (by linarith [hH.1]) measureReal_nonneg hdisc
  have hb := nestingBaseline_slack hH0 hs
  have hg := nestingGainInfimum_actual_slack hH0 hs
  rw [show 2*(H/2)=H by ring] at hb
  dsimp only [nestingC0] at hg
  change Nesting.lambda*H*(1/Real.pi)+2*((∫ v in (0 : ℝ)..s,sharpSectionWeight H v)+min ((134/1000 : ℝ)*(H/2)^3) (36/100)*(nestingDelta (H/2) s)^3) ≤ (perimeter E).toReal at hh
  have he : Nesting.lambda*H*(1/Real.pi)=2*(Nesting.lambda*(H/2)/Real.pi) := by ring
  rw [he] at hh
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSectionCorner_bottom_eq (b : Fin 3 →Bool) (i : Fin 3) (n : Fin 2 →Bool) :
    axialSectionCorner b i (octantHeight b i 0) n=orientedUpperVertex b (i.insertNth false n) := by
  ext k
  rcases Fin.eq_self_or_eq_succAbove i k with h|⟨j,rfl⟩
  · subst k
    rw [axialSectionCorner_same]
    simp only [orientedUpperVertex,upperVertex,WithLp.ofLp_toLp,Fin.insertNth_apply_same]
    cases hb : b i <;> norm_num [octantHeight,hb]
  · rw [axialSectionCorner_other]
    simp only [orientedUpperVertex,upperVertex,WithLp.ofLp_toLp,Fin.insertNth_apply_succAbove]
    cases hb : b (i.succAbove j) <;> cases hn : n j <;> norm_num [octantHeight,hb,hn]

lemma axialSectionCorner_bottom_far (b : Fin 3 →Bool) (i : Fin 3) :
    axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true)=
      orientedUpperVertex b (fun j ↦ if j=i then false else true) := by
  rw [axialSectionCorner_bottom_eq]
  congr 1
  funext k
  rcases Fin.eq_self_or_eq_succAbove i k with rfl|⟨j,rfl⟩ <;> simp [Fin.succAbove_ne]

lemma axialSectionCorner_bottom_axis (b : Fin 3 →Bool) (i : Fin 3) (j : Fin 2) :
    axialSectionCorner b i (octantHeight b i 0) (fun k ↦ k==j)=
      orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false) := by
  rw [axialSectionCorner_bottom_eq]
  congr 1
  funext k
  rcases Fin.eq_self_or_eq_succAbove i k with hki|⟨l,rfl⟩
  · subst k
    simp [Ne.symm (Fin.succAbove_ne i j)]
  · simp only [Fin.insertNth_apply_succAbove]
    by_cases h : l=j
    · subst l; simp
    · simp [h,(Fin.succAbove_right_injective).ne h]

theorem isMinimizerAt_three_vertex_bottom {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (haxes : ∀ j : Fin 2,quotientMap (orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false))∈openRepresentative E) :
    quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun _ ↦ true))∉closure (openRepresentative E) ∧
    ∀ j : Fin 2,quotientMap (axialSectionCorner b i (octantHeight b i 0) (fun k ↦ k==j))∈openRepresentative E := by
  refine ⟨?_,?_⟩
  · rw [axialSectionCorner_bottom_far]
    intro hcl
    have hout : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then false else true))∉openRepresentative E :=
      fun h ↦ hv (isMinimizerAt_no_face_pattern hV hmin hc hR b hd i h)
    have hb : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then false else true))∈frontier (openRepresentative E) := by
      rw [(isOpen_openRepresentative E).frontier_eq]
      exact ⟨hcl,hout⟩
    exact isMinimizerAt_common_fixed_not_boundary hV hmin hR _ (upperVertex_fixed _) hb
  · intro j
    rw [axialSectionCorner_bottom_axis]
    exact haxes j

end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus

private def phi (s : ℝ) : ℝ := s^2*(1-s)*(1+s)^2

private lemma phi_deriv (s : ℝ) : HasDerivAt phi (s*(1+s)*(2+s-5*s^2)) s := by
  have hh := (((hasDerivAt_id s).pow 2).mul ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))).mul
    (((hasDerivAt_const s (1 : ℝ)).add (hasDerivAt_id s)).pow 2)
  convert hh using 1 <;> first | rfl | (dsimp [phi]; ring)

private lemma phi_mono : MonotoneOn phi (Icc 0 (107/200)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) (by unfold phi; fun_prop) (fun s _ ↦ (phi_deriv s).hasDerivWithinAt) ?_
  intro s hs
  have hs' : s∈Icc (0 : ℝ) (107/200) := interior_subset hs
  have hsq := pow_le_pow_left₀ hs'.1 hs'.2 2
  exact mul_nonneg (mul_nonneg hs'.1 (by linarith [hs'.1])) (by nlinarith)

private lemma phi_anti : AntitoneOn phi (Icc (89/100) 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) (by unfold phi; fun_prop) (fun s _ ↦ (phi_deriv s).hasDerivWithinAt) ?_
  intro s hs
  have hs' : s∈Icc (89/100 : ℝ) 1 := interior_subset hs
  have hs0 : 0 ≤ s := by linarith [hs'.1]
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 89/100) hs'.1 2
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hs0 (by linarith)) (by nlinarith)

theorem three_vertex_parameter_algebra {h s A : ℝ}
    (hs : 0<s) (hh : 0<h) (hA : A∈Icc 0 1)
    (hdisc : Real.pi*(1-s) ≤ (h*s)^2)
    (hproj : s^2 ≤ A*(A-h/Real.pi)) :
    Real.sqrt (Real.pi*(1-s))/s ≤ h ∧ h ≤ Real.pi*(1-s^2) ∧
    s∈Ioo (107/200 : ℝ) (89/100 : ℝ) ∧ h∈Icc (16/25 : ℝ) (9/4 : ℝ) ∧ Shape.t h ≤ s := by
  have hp : 0<Real.pi := Real.pi_pos
  have hApos : 0<A := by
    by_contra hn
    have hz : A=0 := le_antisymm (le_of_not_gt hn) hA.1
    rw [hz,zero_mul] at hproj
    nlinarith
  have hdif : 0 ≤ A-h/Real.pi := by
    by_contra hn
    have hneg := mul_neg_of_pos_of_neg hApos (lt_of_not_ge hn)
    nlinarith [sq_nonneg s]
  have hup1 := hproj.trans (mul_le_of_le_one_left hdif hA.2)
  have hup : h ≤ Real.pi*(1-s^2) := by
    have hquot : h/Real.pi ≤ 1-s^2 := by linarith [hA.2]
    have hmul := (div_le_iff₀ hp).mp hquot
    nlinarith
  have hs1 : s<1 := by
    by_contra hn
    have hss : 1 ≤ s^2 := by nlinarith
    have hh' := mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr hss)
    linarith
  have hsqrt : Real.sqrt (Real.pi*(1-s)) ≤ h*s := (Real.sqrt_le_iff).mpr ⟨by positivity,hdisc⟩
  have hlo : Real.sqrt (Real.pi*(1-s))/s ≤ h := (div_le_iff₀ hs).mpr hsqrt
  have hue0 : 0 ≤ Real.pi*(1-s^2) := hh.le.trans hup
  have hsq := pow_le_pow_left₀ hh.le hup 2
  have hsq' := mul_le_mul_of_nonneg_right hsq (sq_nonneg s)
  have hexpand : (Real.pi*(1-s^2))^2*s^2-Real.pi*(1-s)=
      Real.pi*(1-s)*(Real.pi*phi s-1) := by unfold phi; ring
  have hmulnonneg : 0 ≤ Real.pi*(1-s)*(Real.pi*phi s-1) := by rw [←hexpand]; nlinarith
  have hph : 1 ≤ Real.pi*phi s := by
    have hh' := nonneg_of_mul_nonneg_right hmulnonneg (mul_pos hp (sub_pos.mpr hs1))
    linarith
  have hpiU : Real.pi < (22/7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hslo : (107/200 : ℝ)<s := by
    by_contra hn
    have hss : s ≤ (107/200 : ℝ) := le_of_not_gt hn
    have hmon := phi_mono ⟨hs.le,hss⟩ (by constructor <;> norm_num) hss
    have hbound := (mul_le_mul_of_nonneg_left hmon hp.le)
    have hstrict := mul_lt_mul_of_pos_right hpiU (show 0<phi (107/200) by norm_num [phi])
    have hpval : phi (107/200)=(100352282493/320000000000 : ℝ) := by norm_num [phi]
    rw [hpval] at hbound hstrict
    norm_num at hstrict
    linarith
  have hshi : s<(89/100 : ℝ) := by
    by_contra hn
    have hss : (89/100 : ℝ) ≤ s := le_of_not_gt hn
    have hmon := phi_anti (by constructor <;> norm_num) ⟨hss,hs1.le⟩ hss
    have hbound := mul_le_mul_of_nonneg_left hmon hp.le
    have hstrict := mul_lt_mul_of_pos_right hpiU (show 0<phi (89/100) by norm_num [phi])
    have hpval : phi (89/100)=(3112406451/10000000000 : ℝ) := by norm_num [phi]
    rw [hpval] at hbound hstrict
    norm_num at hstrict
    linarith
  have hhlo : (16/25 : ℝ) ≤ h := by
    by_contra hn
    have hh' : h<(16/25 : ℝ) := lt_of_not_ge hn
    have hhs : h*s < (16/25 : ℝ)*(89/100) := (mul_lt_mul_of_pos_right hh' hs).trans_le (mul_le_mul_of_nonneg_left hshi.le (by norm_num))
    have hsqb := pow_le_pow_left₀ (mul_nonneg hh.le hs.le) hhs.le 2
    have hpiL := Real.pi_gt_three
    have hdlo := (mul_lt_mul_of_pos_right hpiL (sub_pos.mpr hs1))
    have h33 : (33/100 : ℝ)<3*(1-s) := by linarith
    nlinarith
  have hsup2 : 1-s^2 < 1-(107/200 : ℝ)^2 := by nlinarith [mul_self_lt_mul_self (by norm_num : (0 : ℝ) ≤ 107/200) hslo]
  have hhhi : h ≤ (9/4 : ℝ) := by
    have hss0 : 0 ≤ 1-s^2 := (nonneg_of_mul_nonneg_right hue0 hp)
    have hcomp := (mul_le_mul_of_nonneg_right hpiU.le hss0).trans_lt
      (mul_lt_mul_of_pos_left hsup2 (by norm_num : (0 : ℝ)<22/7))
    nlinarith
  exact ⟨hlo,hup,⟨hslo,hshi⟩,⟨hhlo,hhhi⟩,source_root_le_of_bottom hh hs.le hdisc⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_perimeter_half_le_one {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E) : (perimeter E).toReal/2 ≤ 1 := by
  have hupper : perimeter E ≤ 2 :=
    (hmin.2.2 (stripe V) (finitePerimeter_stripe ⟨hV.1.le,hV.2.le⟩)
      (volume_stripe ⟨hV.1.le,hV.2.le⟩)).trans (perimeter_stripe_le ⟨hV.1.le,hV.2.le⟩)
  have hup : (perimeter E).toReal ≤ 2 := by
    simpa only [ENNReal.toReal_ofNat] using ENNReal.toReal_mono (by norm_num : (2 : ℝ≥0∞)≠⊤) hupper
  linarith

theorem isMinimizerAt_three_vertex_parameters {E : Set Torus}
    (hE : MeasurableSet E) (hmin : IsMinimizerAt (1/Real.pi) E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
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
    (haxes : ∀ j : Fin 2,quotientMap (orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false))∈openRepresentative E) :
    let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
    (perimeter E).toReal/2 ≤ 1 ∧
    Real.sqrt (Real.pi*(1-s))/s ≤ H/2 ∧ H/2 ≤ Real.pi*(1-s^2) ∧
    s∈Ioo (107/200 : ℝ) (89/100 : ℝ) ∧ H/2∈Icc (16/25 : ℝ) (9/4 : ℝ) ∧ Shape.t (H/2) ≤ s := by
  dsimp only
  have hV : (1/Real.pi)∈Ioo (0 : ℝ) 1 := ⟨by positivity,(div_lt_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  obtain ⟨hout,hin⟩ := isMinimizerAt_three_vertex_bottom hV hmin hc hR b hd i hv haxes
  obtain ⟨hHs,hdisc,_⟩ := isMinimizerAt_bottom_both_extents hV hE hmin hR b hd hμ hCMC i ha hv hout (hin 0) (hin 1)
  have hproj := isMinimizerAt_missing_neighbor_projection hV hE hmin hR b hd hμ (Periodic.coordinateCMC_of_global hμ hCMC) i ha hv
  let s := volume.real (axialSlice (openRepresentative E) i (octantHeight b i 0 : AxisCircle))
  have hs0 : 0 ≤ s := measureReal_nonneg
  have hs : 0<s := by
    change 0<H*s at hHs
    by_contra hn
    have hz : s=0 := le_antisymm (le_of_not_gt hn) hs0
    simp [hz] at hHs
  have hH : 0<H/2 := by
    change 0<H*s at hHs
    have hh : 0<H := (mul_pos_iff.mp hHs).resolve_right (fun hn ↦ (not_lt_of_ge hs0) hn.2) |>.1
    linarith
  have hA := isMinimizerAt_perimeter_half_le_one hV hmin
  have heq : (H/2)*(1/Real.pi)=(H/2)/Real.pi := by ring
  rw [heq] at hproj
  exact ⟨hA,three_vertex_parameter_algebra hs hH ⟨by positivity,hA⟩ hdisc hproj⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_nonstandard_integrated_flux {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ),IsNormalMeasure E μ ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ i : Fin 3,(axialAreaMarginal μ i : Measure AxisCircle)≪volume) ∧
      ∀ i : Fin 3,Nesting.lambda*axialTransverseMass μ i+
        (∫ t,Nesting.weight (actualAxialFlux (openRepresentative E) μ H i t/
          axialPerimeterDensity μ i t)*|axialNormalDensity μ i t|)≤(perimeter E).toReal := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  let O := openRepresentative E
  have hO : MeasurableSet O := (isOpen_openRepresentative E).measurableSet
  have hOE := isMinimizerAt_openRepresentative_ae_nullMeasurable hV' hmin
  have hmO := (isMinimizerAt_congr_ae hOE).mpr hmin
  have hsO : ¬StandardRegionAt V O := fun hs ↦ hstd ((standardRegionAt_congr_ae hOE V).mp hs)
  have hcO : IsPreconnected (frontier (openRepresentative O)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV' hmO).resolve_right (fun h ↦ hsO h.2.2)
  have hRO (i : Fin 3) : O=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' O) :=
    hOE.trans ((hR i).trans ((axisReflection i).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hOE.symm))
  obtain ⟨μ,H,hμ,hCMC,_,_⟩ := isMinimizerAt_CMC_sign hV' hO hmO
  obtain ⟨N,hN,hp,hae,_⟩ := isMinimizerAt_stationary_tubular_normal hV' hO hmO hμ hCMC
  obtain ⟨b,hsg⟩ := isMinimizerAt_nonstandard_strict_signs_of_actual_normal hV hO hmO hcO hsO hRO hμ hN hp hae
  have hH := Periodic.coordinateCMC_of_global hμ hCMC
  have hn (i : Fin 3) := strict_normal_component_ne_zero_ae hV' hO hmO hRO hμ hH hN hp hae hsg i
  have ha (i : Fin 3) := axialAreaMarginal_absolutelyContinuous hH hn i
  refine ⟨μ,H,hμ.congr_ae hOE,hCMC,ha,fun i ↦ ?_⟩
  have hh := axial_integrated_flux_actual hO hμ hH i (ha i)
  rwa [perimeter_congr_ae hOE] at hh

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
