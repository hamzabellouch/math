import Mathlib
import OAI.Geometry.CubicTorus.Reflection.AxialAreaMarginal

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_axialSlice_antitone {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) : AntitoneOn
      (fun t : ℝ ↦ axialSlice (openRepresentative E) i (octantHeight b i t : AxisCircle)) (Icc 0 1) := by
  intro s hs t ht hst y hyt
  let x := upperFold ((torusAxialSplit i).symm ((octantHeight b i s : AxisCircle),y))
  let z := upperFold ((torusAxialSplit i).symm ((octantHeight b i t : AxisCircle),y))
  have hxs : x∈closedUpperOctant := upperFold_mem _
  have hzt : z∈closedUpperOctant := upperFold_mem _
  have hxz : OrientedCoordinateLE b x z := by
    unfold OrientedCoordinateLE
    refine (Fin.forall_iff_succAbove i (P := fun j ↦ if b j then x j≤z j else z j≤x j)).mpr ?_
    constructor
    · have hxi := upperFold_slice_same i (octantHeight_mem b i hs) y
      have hzi := upperFold_slice_same i (octantHeight_mem b i ht) y
      change (if b i then x i≤z i else z i≤x i)
      change x i=octantHeight b i s at hxi
      change z i=octantHeight b i t at hzi
      rw [hxi,hzi]
      unfold octantHeight
      cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> linarith
    · intro k
      have he : x (i.succAbove k)=z (i.succAbove k) :=
        (upperFold_slice_succAbove i _ y k).trans (upperFold_slice_succAbove i _ y k).symm
      change (if b (i.succAbove k) then x (i.succAbove k)≤z (i.succAbove k) else z (i.succAbove k)≤x (i.succAbove k))
      rw [he]
      split_ifs <;> exact le_rfl
  have hr := reflection_invariant_openRepresentative hmin.1.1 hR
  have hzo : quotientMap z∈openRepresentative E := (upperFold_phase hr _).mpr hyt
  have hxo := isMinimizerAt_closed_octant_order hV hmin hR hd hxs hzt hxz hzo
  exact (upperFold_phase hr _).mp hxo

lemma isMinimizerAt_axialSliceVolume_antitone {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    {b : Fin 3 → Bool}
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) : AntitoneOn
      (fun t : ℝ ↦ axialSliceVolume (openRepresentative E) i (octantHeight b i t : AxisCircle)) (Icc 0 1) := by
  intro s hs t ht hst
  exact measure_mono (isMinimizerAt_axialSlice_antitone hV hmin hR hd i hs ht hst)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_slice_absolutelyContinuous {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (∀ a b,AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal) a b) ∧
    ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt
      (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal)
      (-axialNormalDensity μ i (t : AxisCircle)) t := by
  have hU : MeasurableSet (openRepresentative E) := (isOpen_openRepresentative E).measurableSet
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hc := axialSliceVolume_continuous_of_boundary_null hU i
    (isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha)
  obtain ⟨f,hp,hfc,hfac,hae,hd⟩ := circle_weak_integrable_has_ac_representative
    (axialSliceVolume_measurable hU i).ennreal_toReal (axialSliceVolume_real_integrable hU i)
    (axialNormalDensity_integrable μ i)
    (fun ψ hψ hψp ↦ axialSliceVolume_weak_derivative hU hμU i ha hψ hψp)
  have he := (hc.ae_eq_iff_eq (volume : Measure AxisCircle) (continuous_periodic_lift hp hfc)).mp hae
  have he' : (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal)=f := by
    funext t
    exact congrFun he (t : AxisCircle)
  rw [he']
  exact ⟨hfac,hd⟩

theorem isMinimizerAt_nonstandard_slices_ac_measurable {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ μ : FiniteMeasure NormalBundle,IsNormalMeasure E μ ∧
      ∀ i : Fin 3,(∀ a b,AbsolutelyContinuousOnInterval
        (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal) a b) ∧
        ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt
          (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal)
          (-axialNormalDensity μ i (t : AxisCircle)) t := by
  obtain ⟨μ,hμ,_,ha⟩ := isMinimizerAt_nonstandard_area_marginals hV hE hmin hc hstd hR
  exact ⟨μ,hμ,fun i ↦ isMinimizerAt_slice_absolutelyContinuous ⟨hV.1,by linarith [hV.2]⟩ hE hmin hμ i (ha i)⟩

theorem isMinimizerAt_nonstandard_slices_ac {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) (hstd : ¬StandardRegionAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ μ : FiniteMeasure NormalBundle,IsNormalMeasure E μ ∧
      ∀ i : Fin 3,(∀ a b,AbsolutelyContinuousOnInterval
        (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal) a b) ∧
        ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt
          (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal)
          (-axialNormalDensity μ i (t : AxisCircle)) t := by
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have ho := openRepresentative_congr_ae hFE
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by rwa [ho]
  have hsF : ¬StandardRegionAt V F := by
    intro hs
    apply hstd
    simp only [StandardRegionAt,ite_eq_left hV.2,SmallStandardRegion] at hs ⊢
    rcases hs with ⟨hv,φ,hφ⟩|⟨hl,hh,φ,hφ⟩|⟨hl,φ,hφ⟩
    · exact Or.inl ⟨hv,φ,hFE.symm.trans hφ⟩
    · exact Or.inr (Or.inl ⟨hl,hh,φ,hFE.symm.trans hφ⟩)
    · exact Or.inr (Or.inr ⟨hl,φ,hFE.symm.trans hφ⟩)
  have hRF (i : Fin 3) : F=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' F) :=
    hFE.trans ((hR i).trans ((axisReflection i).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  obtain ⟨μ,hμ,hh⟩ := isMinimizerAt_nonstandard_slices_ac_measurable hV hF hmF hcF hsF hRF
  refine ⟨μ,hμ.congr_ae hFE,?_⟩
  simpa only [ho] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialNormalDensity_pairing_bounded {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    {f : AxisCircle → ℝ} (hf : Measurable f) (hb : ∀ t,|f t|≤1) :
    (∫ t,axialNormalDensity μ i t*f t)=
      ∫ z,((z.2 : Cover) i)*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
  have hp := axialPositiveFluxMarginal_absolutelyContinuous i ha
  have hi (η : FiniteMeasure AxisCircle) : Integrable f (η : Measure AxisCircle) :=
    Integrable.mono' (integrable_const (1 : ℝ)) hf.aestronglyMeasurable (ae_of_all _ hb)
  have hf' : Measurable (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) :=
    hf.comp (normal_axisCircle_continuous i).measurable
  have hi' : Integrable (fun z : NormalBundle ↦ f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) :=
    Integrable.mono' (integrable_const (1 : ℝ)) hf'.aestronglyMeasurable (ae_of_all _ fun z ↦ hb _)
  have hi'' : Integrable (fun z : NormalBundle ↦ (1+((z.2 : Cover) i))*f (((z.1 : Cover) i) : AxisCircle)) (μ : Measure NormalBundle) := by
    apply Integrable.mono' (integrable_const (2 : ℝ))
      ((measurable_const.add (normal_component_continuous i).measurable).mul hf').aestronglyMeasurable
    filter_upwards [] with z
    simp only [Pi.mul_apply,Pi.add_apply]
    rw [Real.norm_eq_abs,abs_mul]
    have hn : |1+((z.2 : Cover) i)|≤2 := by
      obtain ⟨hl,hu⟩ := abs_le.mp (normal_component_abs_le_one z.2 i)
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    calc
      _ ≤ 2*1 := mul_le_mul hn (hb _) (abs_nonneg _) (by norm_num)
      _ = 2 := by ring
  simp only [axialNormalDensity,sub_mul]
  rw [integral_sub ((integrable_toReal_rnDeriv_mul_iff hp).mpr (hi _))
    ((integrable_toReal_rnDeriv_mul_iff ha).mpr (hi _)),
    integral_toReal_rnDeriv_mul hp,integral_toReal_rnDeriv_mul ha]
  have he1 : (∫ t,f t ∂(axialPositiveFluxMarginal μ i : Measure AxisCircle))=
      ∫ z,(1+((z.2 : Cover) i))*f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
    change (∫ t,f t ∂Measure.map _ _)=_
    rw [integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable]
    have hw : Measurable (fun z : NormalBundle ↦ ENNReal.ofReal (1+((z.2 : Cover) i))) :=
      (continuous_const.add (normal_component_continuous i)).measurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul hw (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [ENNReal.toReal_ofReal (by have hh := (abs_le.mp (normal_component_abs_le_one z.2 i)).1; linarith),smul_eq_mul]
  have he2 : (∫ t,f t ∂(axialAreaMarginal μ i : Measure AxisCircle))=
      ∫ z,f (((z.1 : Cover) i) : AxisCircle) ∂(μ : Measure NormalBundle) := by
    change (∫ t,f t ∂Measure.map _ _)=_
    exact integral_map (normal_axisCircle_continuous i).measurable.aemeasurable hf.aestronglyMeasurable
  rw [he1,he2,←integral_sub hi'' hi']
  apply integral_congr_ae
  filter_upwards [] with z
  ring

lemma axialNormalDensity_L1_le {μ : FiniteMeasure NormalBundle} (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    (∫ t,|axialNormalDensity μ i t|)≤
      ∫ z,|((z.2 : Cover) i)| ∂(μ : Measure NormalBundle) := by
  classical
  let f : AxisCircle → ℝ := fun t ↦ if 0≤axialNormalDensity μ i t then 1 else -1
  have hf : Measurable f := Measurable.ite
    (measurableSet_le measurable_const (axialNormalDensity_measurable μ i)) measurable_const measurable_const
  have hb (t : AxisCircle) : |f t|≤1 := by dsimp only [f]; split_ifs <;> norm_num
  have he (t : AxisCircle) : axialNormalDensity μ i t*f t=|axialNormalDensity μ i t| := by
    dsimp only [f]
    split_ifs with h
    · rw [mul_one,abs_of_nonneg h]
    · rw [mul_neg_one,abs_of_neg (lt_of_not_ge h)]
  have hh := axialNormalDensity_pairing_bounded i ha hf hb
  simp_rw [he] at hh
  rw [hh]
  apply integral_mono
  · apply Integrable.mono' (integrable_const (1 : ℝ))
      (((normal_component_continuous i).measurable).mul
        (hf.comp (normal_axisCircle_continuous i).measurable)).aestronglyMeasurable
    filter_upwards [] with z
    simp only [Pi.mul_apply,Function.comp_apply]
    rw [Real.norm_eq_abs,abs_mul]
    simpa using mul_le_mul (normal_component_abs_le_one z.2 i) (hb _) (abs_nonneg _) (by norm_num : (0 : ℝ)≤1)
  · exact (normal_component_continuous i).abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro z
    calc
      _ ≤ |((z.2 : Cover) i)*f (((z.1 : Cover) i) : AxisCircle)| := le_abs_self _
      _ = |((z.2 : Cover) i)| *|f (((z.1 : Cover) i) : AxisCircle)| := abs_mul _ _
      _ ≤ |((z.2 : Cover) i)| *1 := mul_le_mul_of_nonneg_left (hb _) (abs_nonneg _)
      _ = _ := mul_one _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normal_component_L1_le_sqrt (μ : FiniteMeasure NormalBundle) (i : Fin 3) :
    (∫ z,|((z.2 : Cover) i)| ∂(μ : Measure NormalBundle))≤
      Real.sqrt ((μ.mass : ℝ)*((μ.mass : ℝ)-axialTransverseMass μ i)) := by
  have hpq : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have hn : MemLp (fun z : NormalBundle ↦ ((z.2 : Cover) i)) (ENNReal.ofReal 2) (μ : Measure NormalBundle) :=
    (normal_component_continuous i).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : MemLp (fun _ : NormalBundle ↦ (1 : ℝ)) (ENNReal.ofReal 2) (μ : Measure NormalBundle) :=
    continuous_const.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := integral_mul_norm_le_Lp_mul_Lq hpq hn h1
  simp only [Real.norm_eq_abs,abs_one,mul_one,Real.rpow_two,sq_abs,one_pow,
    integral_const,smul_eq_mul,mul_one,Measure.real_def,←FiniteMeasure.ennreal_mass,
    ENNReal.coe_toReal,←Real.sqrt_eq_rpow] at hh
  have hq : (∫ z,((z.2 : Cover) i)^2 ∂(μ : Measure NormalBundle))=(μ.mass : ℝ)-axialTransverseMass μ i := by
    rw [axialTransverseMass_defect]
    ring
  rw [hq] at hh
  rw [Real.sqrt_mul (NNReal.coe_nonneg μ.mass),mul_comm]
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma circle_ac_oscillation_bound {f : ℝ → ℝ} {g : AxisCircle → ℝ}
    (hp : Function.Periodic f 1) (hf : ∀ a b,AbsolutelyContinuousOnInterval f a b)
    (hgi : Integrable g)
    (hd : ∀ᵐ t : ℝ,t∈Icc (0 : ℝ) 1 → HasDerivAt f (g (t : AxisCircle)) t)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    2*|f t-f 0|≤∫ s,|g s| := by
  have hi : IntervalIntegrable (fun s : ℝ ↦ g (s : AxisCircle)) volume 0 1 := circle_intervalIntegrable hgi
  have hi0 : IntervalIntegrable (fun s : ℝ ↦ g (s : AxisCircle)) volume 0 t := hi.mono (by
    rw [uIcc_of_le ht.1,uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact fun s hs ↦ ⟨hs.1,hs.2.trans ht.2⟩) le_rfl
  have hi1 : IntervalIntegrable (fun s : ℝ ↦ g (s : AxisCircle)) volume t 1 := hi.mono (by
    rw [uIcc_of_le ht.2,uIcc_of_le (by norm_num : (0 : ℝ)≤1)]
    exact fun s hs ↦ ⟨ht.1.trans hs.1,hs.2⟩) le_rfl
  have h0 : (∫ s in (0 : ℝ)..t,g (s : AxisCircle))=f t-f 0 := by
    rw [←(hf 0 t).integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with s hs hst
    exact (hs (by have hh := uIoc_subset_uIcc hst; rw [uIcc_of_le ht.1] at hh; exact ⟨hh.1,hh.2.trans ht.2⟩)).deriv.symm
  have h1 : (∫ s in t..1,g (s : AxisCircle))=f 1-f t := by
    rw [←(hf t 1).integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with s hs hst
    exact (hs (by have hh := uIoc_subset_uIcc hst; rw [uIcc_of_le ht.2] at hh; exact ⟨ht.1.trans hh.1,hh.2⟩)).deriv.symm
  have hb0 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun s : ℝ ↦ g (s : AxisCircle)) ht.1
  have hb1 := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun s : ℝ ↦ g (s : AxisCircle)) ht.2
  rw [h0,Real.norm_eq_abs] at hb0
  rw [h1,Real.norm_eq_abs,show f 1=f 0 from by simpa using hp 0,abs_sub_comm] at hb1
  have hh := add_le_add hb0 hb1
  rw [intervalIntegral.integral_add_adjacent_intervals hi0.norm hi1.norm] at hh
  rw [circle_integral_eq_interval hgi.abs.aestronglyMeasurable]
  simpa only [Real.norm_eq_abs,two_mul] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace CubicTorus

lemma ac_on_all_intervals_comp_affine {f : ℝ → ℝ}
    (hf : ∀ a b,AbsolutelyContinuousOnInterval f a b) (c d a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ f (c*t+d)) a b := by
  by_cases hc : c=0
  · simp only [hc,zero_mul,zero_add]
    exact (show ContDiff ℝ 1 (fun _ : ℝ ↦ f d) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval
  have hi (s t : ℝ) : IntervalIntegrable (fun x ↦ deriv f (c*x+d)) volume s t := by
    have hh := ((hf (c*s+d) (c*t+d)).intervalIntegrable_deriv.comp_add_right d).comp_mul_left (c := c)
    simpa only [add_sub_cancel_right,mul_div_cancel_left₀ _ hc] using hh
  have he : (fun t ↦ f (c*t+d))=(fun t ↦ f (c*a+d)+c*(∫ s in a..t,deriv f (c*s+d))) := by
    funext t
    have hh := intervalIntegral.smul_integral_comp_mul_add (deriv f) (a := a) (b := t) c d
    simp only [smul_eq_mul] at hh
    rw [hh,(hf (c*a+d) (c*t+d)).integral_deriv_eq_sub]
    ring
  rw [he]
  exact (show ContDiff ℝ 1 (fun _ : ℝ ↦ f (c*a+d)) from contDiff_const).contDiffOn.absolutelyContinuousOnInterval.add
    ((interval_primitive_absolutelyContinuous hi a b a).const_mul c)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_actual_projection_bound {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume) :
    2*|(axialSliceVolume (openRepresentative E) i ((1/2 : ℝ) : AxisCircle)).toReal-
      (axialSliceVolume (openRepresentative E) i 0).toReal|≤
      Real.sqrt ((μ.mass : ℝ)*((μ.mass : ℝ)-axialTransverseMass μ i)) := by
  obtain ⟨hac,hd⟩ := isMinimizerAt_slice_absolutelyContinuous hV hE hmin hμ i ha
  have hp : Function.Periodic
      (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (t : AxisCircle)).toReal) 1 := by
    intro t
    change (axialSliceVolume (openRepresentative E) i ((t+1 : ℝ) : AxisCircle)).toReal = _
    rw [AddCircle.coe_add_period]
  have hh := circle_ac_oscillation_bound hp hac (axialNormalDensity_integrable μ i).neg hd
    (t := 1/2) (by constructor <;> norm_num)
  simp only [Pi.neg_apply,abs_neg,AddCircle.coe_zero] at hh
  exact hh.trans ((axialNormalDensity_L1_le i ha).trans (normal_component_L1_le_sqrt μ i))

theorem isMinimizerAt_octantSliceVolume_ac {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (i : Fin 3) (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (b : Fin 3 → Bool) : AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ (axialSliceVolume (openRepresentative E) i (octantHeight b i t : AxisCircle)).toReal) 0 1 := by
  have hh := (isMinimizerAt_slice_absolutelyContinuous hV hE hmin hμ i ha).1
  unfold octantHeight
  cases hbi : b i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  · convert ac_on_all_intervals_comp_affine hh (-1/2) 1 0 1 using 1
    funext t
    congr 2
    congr 1
    ring
  · convert ac_on_all_intervals_comp_affine hh (1/2) (1/2) 0 1 using 1
    funext t
    congr 2
    congr 1
    ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def actualAxialFlux (E : Set Torus) (μ : FiniteMeasure NormalBundle) (H : ℝ)
    (i : Fin 3) (t : AxisCircle) : ℝ :=
  axialTransverseMass μ i+H*((axialSliceVolume E i t).toReal-torusVolume.real E)

lemma actualAxialFlux_integrable {E : Set Torus} (hE : MeasurableSet E)
    (μ : FiniteMeasure NormalBundle) (H : ℝ) (i : Fin 3) :
    Integrable (actualAxialFlux E μ H i) :=
  (integrable_const _).add (((axialSliceVolume_real_integrable hE i).sub (integrable_const _)).const_mul _)

lemma actualAxialFlux_measurable {E : Set Torus} (hE : MeasurableSet E)
    (μ : FiniteMeasure NormalBundle) (H : ℝ) (i : Fin 3) :
    Measurable (actualAxialFlux E μ H i) :=
  measurable_const.add (measurable_const.mul ((axialSliceVolume_measurable hE i).ennreal_toReal.sub measurable_const))

lemma axialSurface_density_eq_flux {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    (fun t ↦ ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal)=ᵐ[volume]
      actualAxialFlux E μ H i := by
  let d : AxisCircle → ℝ := fun t ↦ ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t).toReal
  have hd : Measurable d := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hdi : Integrable d := Measure.integrable_toReal_rnDeriv
  have hac := axialSurfaceMarginal_absolutelyContinuous hH i
  have hh := integrable_circle_eq_zero_of_continuous_pairing
    (hd.sub (actualAxialFlux_measurable hE μ H i))
    (hdi.sub (actualAxialFlux_integrable hE μ H i)) ?_
  · filter_upwards [hh] with t ht
    exact sub_eq_zero.mp ht
  intro f hf
  have hi (η : FiniteMeasure AxisCircle) : Integrable f (η : Measure AxisCircle) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfint : Integrable f := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvf := circle_integrable_mul_continuous (axialSliceVolume_real_integrable hE i) hf
  have hh := axial_circle_flux_integral hH i hf
  rw [axisCircleLebesgue_eq_volume,←realVolume_lift hE,
    axialVolumeMarginal_eq_withDensity hE i,
    integral_withDensity_eq_integral_toReal_smul (axialSliceVolume_measurable hE i)
      (ae_of_all _ fun t ↦ lt_of_le_of_lt (axialSliceVolume_le_one E i t) ENNReal.one_lt_top)] at hh
  simp only [smul_eq_mul] at hh
  simp only [Pi.sub_apply,sub_mul]
  rw [integral_sub (circle_integrable_mul_continuous hdi hf)
    (circle_integrable_mul_continuous (actualAxialFlux_integrable hE μ H i) hf)]
  have hleft : (∫ t,d t*f t)=∫ t,f t ∂(axialSurfaceMarginal μ i : Measure AxisCircle) :=
    integral_toReal_rnDeriv_mul hac
  rw [hleft]
  have hright : (∫ t,actualAxialFlux E μ H i t*f t)=
      axialTransverseMass μ i*(∫ t,f t)+H*((∫ t,(axialSliceVolume E i t).toReal*f t)-torusVolume.real E*(∫ t,f t)) := by
    simp only [actualAxialFlux,add_mul,mul_assoc,sub_mul]
    have hsub : Integrable (fun t ↦ (axialSliceVolume E i t).toReal*f t-torusVolume.real E*f t) := by
      exact (hvf.sub (hfint.const_mul (torusVolume.real E))).congr (ae_of_all _ fun t ↦ rfl)
    rw [integral_add (hfint.const_mul (axialTransverseMass μ i)) (hsub.const_mul H),
      integral_const_mul,integral_const_mul,integral_sub hvf (hfint.const_mul (torusVolume.real E)),integral_const_mul]
  rw [hright]
  linarith only [hh]

lemma actualAxialFlux_nonneg_ae {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3) :
    ∀ᵐ t,0≤actualAxialFlux E μ H i t := by
  filter_upwards [axialSurface_density_eq_flux hE hH i] with t ht
  rw [←ht]
  exact ENNReal.toReal_nonneg

lemma actualAxialFlux_nonneg {E : Set Torus} (hE : MeasurableSet E)
    {μ : FiniteMeasure NormalBundle} {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (hc : Continuous (fun t ↦ (axialSliceVolume E i t).toReal)) (t : AxisCircle) :
    0≤actualAxialFlux E μ H i t := by
  have hf : Continuous (actualAxialFlux E μ H i) :=
    continuous_const.add (continuous_const.mul (hc.sub continuous_const))
  have ht := (Measure.dense_of_ae (actualAxialFlux_nonneg_ae hE hH i)) t
  rwa [(isClosed_le continuous_const hf).closure_eq] at ht

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma axialSurfaceMarginal_zero_of_boundary_gap {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) (i : Fin 3)
    {S : Set AxisCircle} (hS : MeasurableSet S)
    (hg : ∀ z∈frontier (openRepresentative E),z i∉S) :
    (axialSurfaceMarginal μ i : Measure AxisCircle) S=0 := by
  have hμO := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hb := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμO
  change Measure.map _ _ S=0
  rw [Measure.map_apply (normal_axisCircle_continuous i).measurable hS]
  apply withDensity_absolutelyContinuous
  have hh : ∀ᵐ z : NormalBundle ∂(μ : Measure NormalBundle),
      ((z.1 : Cover) i : AxisCircle)∉S := by
    filter_upwards [hb] with z hz
    exact hg _ hz
  simpa only [not_not, Set.preimage] using ae_iff.mp hh

theorem actualAxialFlux_zero_of_empty_boundary_height {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (hc : Continuous (fun t ↦ (axialSliceVolume E i t).toReal)) (t : AxisCircle)
    (ht : ∀ z∈frontier (openRepresentative E),z i≠t) :
    actualAxialFlux E μ H i t=0 := by
  let K : Set AxisCircle := (fun z : Torus ↦ z i) '' frontier (openRepresentative E)
  have hK : IsClosed K := (isClosed_frontier.isCompact.image
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ AxisCircle) i)).isClosed
  have htK : t∈Kᶜ := by
    rintro ⟨z,hz,hzt⟩
    exact ht z hz hzt
  have hn : (axialSurfaceMarginal μ i : Measure AxisCircle) Kᶜ=0 :=
    axialSurfaceMarginal_zero_of_boundary_gap hV hE hmin hμ i hK.isOpen_compl.measurableSet
      (fun z hz hn ↦ hn ⟨z,hz,rfl⟩)
  have hr : (fun t ↦ ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t))
      =ᵐ[volume.restrict Kᶜ]0 := by
    apply (lintegral_eq_zero_iff (Measure.measurable_rnDeriv _ _)).mp
    rw [←withDensity_apply _ hK.isOpen_compl.measurableSet,
      Measure.withDensity_rnDeriv_eq _ _ (axialSurfaceMarginal_absolutelyContinuous hH i)]
    exact hn
  have hzero : actualAxialFlux E μ H i=ᵐ[volume.restrict Kᶜ]0 := by
    filter_upwards [hr,ae_restrict_of_ae (axialSurface_density_eq_flux hE hH i)] with s hs he
    rw [←he,hs]
    rfl
  have hf : Continuous (actualAxialFlux E μ H i) :=
    continuous_const.add (continuous_const.mul (hc.sub continuous_const))
  exact Measure.eqOn_open_of_ae_eq hzero hK.isOpen_compl hf.continuousOn continuous_const.continuousOn htK

theorem actual_transverse_mass_eq_curvature_volume_of_empty_end {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (hc : Continuous (fun t ↦ (axialSliceVolume E i t).toReal)) (t : AxisCircle)
    (ht : ∀ z∈frontier (openRepresentative E),z i≠t)
    (he : axialSlice E i t=∅) : axialTransverseMass μ i=H*V := by
  have hz := actualAxialFlux_zero_of_empty_boundary_height hV hE hmin hμ hH i hc t ht
  have hv : torusVolume.real E=V := by
    rw [measureReal_def,hmin.2.1,ENNReal.toReal_ofReal hV.1.le]
  have hs : axialSliceVolume E i t=0 := by simp [axialSliceVolume,he]
  rw [actualAxialFlux,hs,ENNReal.toReal_zero,hv] at hz
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_missing_neighbor_gap {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    ∀ z∈closure (openRepresentative E),z i≠(octantHeight b i 1 : AxisCircle) := by
  classical
  intro z hz hzi
  let v := orientedUpperVertex b (fun j ↦ if j=i then true else false)
  have hf : upperFold z i=if b i then (1 : ℝ) else 1/2 := by
    change 1-‖z i‖=_
    rw [hzi]
    unfold octantHeight
    cases b i <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> norm_num
  have hord : OrientedCoordinateLE b v (upperFold z) := by
    intro j
    by_cases hji : j=i
    · subst j
      dsimp only [v,orientedUpperVertex,upperVertex]
      simp only [ite_true,Bool.not_true]
      rw [hf]
      cases b i <;> simp
    · have hmin := orientedUpperVertex_min b (upperFold_mem z) j
      have hvj : v j=orientedUpperVertex b (fun _ ↦ false) j := by
        dsimp [v,orientedUpperVertex,upperVertex]
        simp [hji]
      change (if b j then v j≤upperFold z j else upperFold z j≤v j)
      rw [hvj]
      exact hmin
  have hy : quotientMap (upperFold z)∈closure (openRepresentative E) := by
    have hc : Continuous (fun z : Torus ↦ quotientMap (upperFold z)) := continuous_quotientMap.comp upperFold_continuous
    apply (closure_minimal (s := openRepresentative E)
      (t := (fun z : Torus ↦ quotientMap (upperFold z)) ⁻¹' closure (openRepresentative E))
      (fun z hz ↦ subset_closure ((upperFold_phase (reflection_invariant_openRepresentative hmin.1.1 hR) z).mpr hz))
      (isClosed_closure.preimage hc)) hz
  have hvc : quotientMap v∈closure (openRepresentative E) := octant_downset_closure
    (isOpen_openRepresentative E) (reflection_invariant_openRepresentative hmin.1.1 hR)
    hd (upperVertex_mem _) (upperFold_mem _) hord hy
  have hvb := isMinimizerAt_common_fixed_not_boundary hV hmin hR (quotientMap v) (upperVertex_fixed _)
  apply hvb
  rw [(isOpen_openRepresentative E).frontier_eq]
  exact ⟨hvc,hv⟩

theorem isMinimizerAt_missing_neighbor_flux {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (ha : (axialAreaMarginal μ i : Measure AxisCircle)≪volume)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    axialTransverseMass μ i=H*V := by
  have hg := isMinimizerAt_missing_neighbor_gap hV hmin hR b hd i hv
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hμO := hμ.congr_ae hOE.symm
  have hminO := (isMinimizerAt_congr_ae hOE).mpr hmin
  have hc := axialSliceVolume_continuous_of_boundary_null (isOpen_openRepresentative E).measurableSet i
    (isMinimizerAt_boundary_slice_null hV hE hmin hμ i ha)
  apply actual_transverse_mass_eq_curvature_volume_of_empty_end hV
    (isOpen_openRepresentative E).measurableSet hminO hμO
    (fun D ↦ by rw [directionalFlux_congr_ae hOE]; exact hH D) i hc (octantHeight b i 1 : AxisCircle)
  · rw [openRepresentative_congr_ae hOE]
    intro z hz
    exact hg z (frontier_subset_closure hz)
  · apply eq_empty_iff_forall_notMem.mpr
    intro y hy
    apply hg ((torusAxialSplit i).symm ((octantHeight b i 1 : AxisCircle),y)) (subset_closure hy)
    exact torusAxialSplit_symm_same _ _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_connected_transverse_mass_pos {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3) :
    0<axialTransverseMass μ i := by
  by_contra hpos
  have hz : axialTransverseMass μ i=0 := le_antisymm (le_of_not_gt hpos) (axialTransverseMass_nonneg μ i)
  have hν := (integral_eq_zero_iff_of_nonneg
    (fun z : NormalBundle ↦ sub_nonneg.mpr (normalSphere_coordinate_sq_le z.2 i))
    (normal_transverse_integrable μ i)).mp hz
  have haesq : ∀ᵐ z ∂(μ : Measure NormalBundle),(N z.1 i)^2=1 := by
    filter_upwards [hae,hν] with z he hz
    rw [he]
    change 1-((z.2 : Cover) i)^2=0 at hz
    linarith
  have hpoint (x : Torus) (hx : x∈frontier (openRepresentative E)) :
      (N (representative x) i)^2=1 := by
    apply isMinimizerAt_periodic_ae_eq_boundary hV hE hmin hμ
      ((((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous).comp hN.continuous).pow 2)
      continuous_const (fun m y ↦ by change (N (y+latticeVector m) i)^2=(N y i)^2; rw [hp])
      (fun _ _ ↦ rfl) haesq (representative x)
    simpa only [quotientMap_representative] using hx
  have hμU := hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet hμU
  have hmpos : 0<(μ : Measure NormalBundle).real univ := by
    rw [Measure.real,←FiniteMeasure.ennreal_mass,ENNReal.coe_toReal,hμ.1]
    exact ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne
  have : NeZero (μ : Measure NormalBundle) := ⟨by intro hz; simp [hz,Measure.real] at hmpos⟩
  obtain ⟨z,hz⟩ := hbd.exists
  let c : ℝ := N z.1 i
  have hc1 : c^2=1 := by
    have hh := hpoint (quotientMap z.1) hz
    rwa [periodic_representative hp] at hh
  have hcne : c≠0 := by intro he; simp [he] at hc1
  have hconst (x : Torus) (hx : x∈frontier (openRepresentative E)) : N (representative x) i=c := by
    have hm : MapsTo (fun x : Torus ↦ N (representative x) i)
        (frontier (openRepresentative E)) ({(1 : ℝ),-1} : Set ℝ) := by
      intro y hy
      simpa only [mem_insert_iff,mem_singleton_iff] using sq_eq_one_iff.mp (hpoint y hy)
    have hh := hc.constant_of_mapsTo (Set.toFinite ({(1 : ℝ),-1} : Set ℝ)).isDiscrete
      (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).continuous).comp
        (continuous_periodic_descent hN.continuous hp)).continuousOn hm hx hz
    change N (representative x) i=N (representative (quotientMap z.1)) i at hh
    rw [periodic_representative hp] at hh
    exact hh
  have hconstae : ∀ᵐ w ∂(μ : Measure NormalBundle),(w.2 : Cover) i=c := by
    filter_upwards [hbd,hae] with w hw he
    have hh := hconst (quotientMap w.1) hw
    rw [periodic_representative hp,he] at hh
    exact hh
  have hf : AdmissibleField (fun _ : Cover ↦ (EuclideanSpace.single i 1 : Cover)) := by
    exact ⟨contDiff_const,fun _ _ ↦ rfl,fun _ ↦ by simp⟩
  have hflux := hμ.2 _ hf
  have hi : (∫ w,normalTest (fun _ : Cover ↦ EuclideanSpace.single i 1) hf.1.continuous w
      ∂(μ : Measure NormalBundle))=(μ : Measure NormalBundle).real univ*c := by
    calc
      _=(∫ _ : NormalBundle,c ∂(μ : Measure NormalBundle)) := by
        apply integral_congr_ae
        filter_upwards [hconstae] with w hw
        simpa only [normalTest,ContinuousMap.coe_mk,EuclideanSpace.inner_single_right,
          RCLike.star_def,conj_trivial,one_mul] using hw
      _=_ := by simp
  rw [hi] at hflux
  have hd : divergence (fun _ : Cover ↦ (EuclideanSpace.single i 1 : Cover))=fun _ ↦ 0 := by
    funext x
    simp [divergence]
  rw [hd,integral_zero] at hflux
  exact (mul_ne_zero hmpos.ne' hcne) hflux

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_missing_neighbor_flux_unrestricted {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : Periodic.Variation,Periodic.normalFirstVariation μ D=
      H*directionalFlux E D.coordinate D.function) (i : Fin 3)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    axialTransverseMass μ i=H*V := by
  let O := openRepresentative E
  let t : AxisCircle := (octantHeight b i 1 : AxisCircle)
  let K : Set AxisCircle := (fun z : Torus ↦ z i) '' closure O
  have hOE := isMinimizerAt_openRepresentative_ae hV hE hmin
  have hHO (D : Periodic.Variation) : Periodic.normalFirstVariation μ D=
      H*directionalFlux O D.coordinate D.function := by
    rw [directionalFlux_congr_ae hOE]
    exact hH D
  have hK : IsClosed K := isClosed_closure.isCompact.image
    (PiLp.continuous_apply 2 (fun _ : Fin 3 ↦ AxisCircle) i) |>.isClosed
  have htK : t∈Kᶜ := by
    rintro ⟨z,hz,hzt⟩
    exact isMinimizerAt_missing_neighbor_gap hV hmin hR b hd i hv z hz hzt
  have hn : (axialSurfaceMarginal μ i : Measure AxisCircle) Kᶜ=0 :=
    axialSurfaceMarginal_zero_of_boundary_gap hV hE hmin hμ i hK.isOpen_compl.measurableSet
      (fun z hz hn ↦ hn ⟨z,frontier_subset_closure hz,rfl⟩)
  have hr : (fun t ↦ ((axialSurfaceMarginal μ i : Measure AxisCircle).rnDeriv volume t))
      =ᵐ[volume.restrict Kᶜ]0 := by
    apply (lintegral_eq_zero_iff (Measure.measurable_rnDeriv _ _)).mp
    rw [←withDensity_apply _ hK.isOpen_compl.measurableSet,
      Measure.withDensity_rnDeriv_eq _ _ (axialSurfaceMarginal_absolutelyContinuous hH i)]
    exact hn
  have hzero : actualAxialFlux O μ H i=ᵐ[volume.restrict Kᶜ]0 := by
    filter_upwards [hr,ae_restrict_of_ae (axialSurface_density_eq_flux (isOpen_openRepresentative E).measurableSet hHO i)] with s hs he
    rw [←he,hs]
    rfl
  have hvO : torusVolume.real O=V := by
    rw [measureReal_def,measure_congr hOE,hmin.2.1,ENNReal.toReal_ofReal hV.1.le]
  have heq : EqOn (actualAxialFlux O μ H i) (fun _ ↦ axialTransverseMass μ i-H*V) Kᶜ := by
    intro s hs
    have hempty : axialSlice O i s=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      apply hs
      exact ⟨(torusAxialSplit i).symm (s,y),subset_closure hy,torusAxialSplit_symm_same _ _ _⟩
    have hsv : axialSliceVolume O i s=0 := by simp [axialSliceVolume,hempty]
    rw [actualAxialFlux,hsv,ENNReal.toReal_zero,hvO]
    ring
  have hh := Measure.eqOn_open_of_ae_eq hzero hK.isOpen_compl
    (continuousOn_const.congr heq) continuous_const.continuousOn htK
  rw [heq htK] at hh
  change axialTransverseMass μ i-H*V=0 at hh
  linarith

theorem isMinimizerAt_missing_neighbor_volume_le_half {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 → Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    V≤1/2 := by
  obtain ⟨μ,H,hμ,hCMC,_,hsgn⟩ := isMinimizerAt_CMC_sign hV hE hmin
  obtain ⟨N,hN,hp,hae,_⟩ := isMinimizerAt_stationary_tubular_normal hV hE hmin hμ hCMC
  have hpos := isMinimizerAt_connected_transverse_mass_pos hV hE hmin hc hμ hN hp hae i
  have hflux := isMinimizerAt_missing_neighbor_flux_unrestricted hV hE hmin hR b hd hμ
    (Periodic.coordinateCMC_of_global hμ hCMC) i hv
  by_contra hlarge
  have hnon := mul_nonpos_of_nonpos_of_nonneg (hsgn (lt_of_not_ge hlarge)) hV.1.le
  rw [←hflux] at hnon
  exact (not_lt_of_ge hnon) hpos

end CubicTorus
end
end
end

end OAI
