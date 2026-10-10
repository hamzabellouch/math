import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeErrorInitial

namespace OAI

section

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume HodgeFrame Set Filter MeasureTheory
open scoped Manifold ContDiff Topology RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)

attribute [local irreducible] framePairing globalLeading globalResidual

include hE in
lemma globalCandidate_L2_of_bounds {T L C : ℝ} (hT : 0 < T)
    (hL : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T L (globalLeading J α ht A E))
    (hC : let := geometricMetricSpace J α hs ht
      VolterraKernel.HeatBound (geometricVolume A J α) 0 T C (globalCorrection J α ht A E T))
    (v : X → FrameSpace A) (hv : Continuous v) :
    ∃ (f : L2 A J α hs ht true) (U : ℝ → L2 A J α hs ht true) (M : ℝ),
      0 ≤ M ∧ U 0 = f ∧ (∀ t ∈ Icc 0 T, ‖U t‖ ≤ M) ∧
      (∀ a : PreL2 A J α hs ht true,
        ⟪f,smoothL2 A J α hs ht true a⟫ =
          ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α) ∧
      (∀ a : PreL2 A J α hs ht true, ∀ t ∈ Ioc 0 T,
        ⟪U t,smoothL2 A J α hs ht true a⟫ =
          kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
          kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t) ∧
      (∀ a : PreL2 A J α hs ht true,
        Tendsto (fun t => ⟪U t,smoothL2 A J α hs ht true a⟫) (𝓝[>] 0)
          (𝓝 ⟪f,smoothL2 A J α hs ht true a⟫)) := by
  classical
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  have hErr := VolterraKernel.convolution_heatBound (geometricVolume A J α) 0 hT.le _ _ hL hC
  obtain ⟨V₀,hV₀⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  let V := max V₀ 0
  have hV : 0 ≤ V := le_max_right _ _
  have hvb (y : X) : ‖v y‖ ≤ V := (hV₀ y (mem_univ y)).trans (le_max_left _ _)
  let f := boundedFrameSection A J α hs ht E hE v hv.aestronglyMeasurable V hV
    (Eventually.of_forall hvb)
  let P := heatBoundL2 A J α hs ht E hE _ T L hL v hv.stronglyMeasurable V hV hvb
  let Q := heatBoundL2 A J α hs ht E hE _ T (4*T*L*C) hErr v hv.stronglyMeasurable V hV hvb
  let U := fun t => if t=0 then f else P t+Q t
  let M := ‖f‖ + frameNormConstant A J α hs ht E hE*(L*V) +
    frameNormConstant A J α hs ht E hE*((4*T*L*C)*V)
  have hLn := mul_nonneg (frameNormConstant_nonneg A J α hs ht E hE) (mul_nonneg hL.nonneg hV)
  have hQn := mul_nonneg (frameNormConstant_nonneg A J α hs ht E hE) (mul_nonneg hErr.nonneg hV)
  have hf (a : PreL2 A J α hs ht true) : ⟪f,smoothL2 A J α hs ht true a⟫ =
      ∫ y, framePairing A J α ht E a.val y (v y) ∂geometricVolume A J α :=
    boundedFrameSection_pairing A J α hs ht E hE v hv.aestronglyMeasurable V hV
      (Eventually.of_forall hvb) a
  have hp (a : PreL2 A J α hs ht true) (t : ℝ) (htp : t ∈ Ioc 0 T) :
      ⟪U t,smoothL2 A J α hs ht true a⟫ =
        kernelWeakAction A J α ht E (globalLeading J α ht A E) v a.val t +
        kernelWeakAction A J α ht E (globalError J α ht A E T) v a.val t := by
    rw [show U t = P t+Q t by simp [U,htp.1.ne'],inner_add_left]
    rw [heatBoundL2_pairing A J α hs ht E hE _ T L hL v hv.stronglyMeasurable V hV hvb a htp,
      heatBoundL2_pairing A J α hs ht E hE _ T _ hErr v hv.stronglyMeasurable V hV hvb a htp]
    rfl
  refine ⟨f,U,M,by dsimp only [M]; positivity,by simp [U],?_,hf,hp,?_⟩
  · intro t _ht
    by_cases hz : t=0
    · simpa [U,hz,M] using (show ‖f‖ ≤ M by dsimp only [M]; linarith)
    · rw [show U t = P t+Q t by simp [U,hz]]
      have hP := heatBoundL2_norm A J α hs ht E hE _ T L hL v hv.stronglyMeasurable V hV hvb t
      have hQ := heatBoundL2_norm A J α hs ht E hE _ T _ hErr v hv.stronglyMeasurable V hV hvb t
      exact (norm_add_le _ _).trans (by dsimp only [M]; linarith [norm_nonneg f])
  · intro a
    have hh := (kernelWeakAction_leading_initial A J α hs ht E hE v hv a.val a.property).add
      (globalError_weak_initial_of_bounds A J α hs ht E hE hT hL hC v hv a.val a.property)
    rw [add_zero,← hf a] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hT).filter_mono nhdsWithin_le_nhds] with t htp htT
    exact (hp a t ⟨htp,htT.le⟩).symm

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open ManifoldForms ManifoldVolume ManifoldLocalization HodgeFrame Set MeasureTheory
open scoped Manifold ContDiff Topology
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]
variable (J : AlmostComplexStructure X) (α : TwoForm X) (hs : IsSmooth α) (ht : Tames α J)
  (A : FiniteCharts X) (D : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)

include hD in
lemma globalCorrection_small_bound (n : ℕ) :
    let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
    ∃ T L C : ℝ, 0 < T ∧ T ≤ 1 ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T L (globalLeading J α ht A D) ∧
      VolterraKernel.HeatBound (geometricVolume A J α) n T C (globalCorrection J α ht A D T) ∧
      (∀ t ∈ Ioc 0 T, ∀ x y, globalResidual J α ht A D t x y +
        globalCorrection J α ht A D T t x y +
        VolterraKernel.convolution (geometricVolume A J α) (globalResidual J α ht A D)
          (globalCorrection J α ht A D T) t x y = 0) := by
  dsimp only
  let := geometricMetricSpace J α hs ht
  let := geometricVolume_finite A J α hs ht
  obtain ⟨L,hL⟩ := globalLeading_heatBound J α hs ht A D hD n 1
  obtain ⟨R,hR⟩ := globalResidual_heatBound J α hs ht A D hD n 1
  let T := (8*(R+1))⁻¹
  have hp : 0 < 8*(R+1) := by have := hR.nonneg; positivity
  have hT : 0 < T := inv_pos.mpr hp
  have hT1 : T ≤ 1 := (inv_le_one₀ hp).mpr (by linarith [hR.nonneg])
  have hq : 4*T*R < 1 := by
    dsimp [T]
    rw [show 4*(8*(R+1))⁻¹*R = (4*R)/(8*(R+1)) by ring]
    exact (div_lt_one hp).mpr (by linarith [hR.nonneg])
  have hR' := hR.mono_time _ hT1
  refine ⟨T,L,R/(1-4*T*R),hT,hT1,hL.mono_time _ hT1,?_,?_⟩
  · exact KernelSeries.correction_heatBound (geometricVolume A J α) n hT.le _ hR' hq
  · intro t htp x y
    exact KernelSeries.correction_equation (geometricVolume A J α) n hT.le _ hR' hq htp x y

end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.WeakHeat
open Set Filter MeasureTheory
open scoped Topology

lemma of_primitive {I : Type*} (D : I → I) (F : I → ℝ → ℝ) (f : I → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hi : ∀ a, IntegrableOn (F a) (Icc 0 T))
    (hp : ∀ a, ∀ t ∈ Icc 0 T, F a t = f a - ∫ s in Ioo 0 t, F (D a) s) :
    (∀ a, ContinuousOn (F a) (Icc 0 T)) ∧
      (∀ a, ∀ t ∈ Ioo 0 T, HasDerivAt (F a) (-F (D a) t) t) := by
  have he (a : I) (t : ℝ) (ht : t ∈ Icc 0 T) :
      F a t = f a - ∫ s in 0..t, F (D a) s := by
    rw [hp a t ht,intervalIntegral.integral_of_le ht.1,integral_Ioc_eq_integral_Ioo]
  have hc (a : I) : ContinuousOn (F a) (Icc 0 T) := by
    have hh : ContinuousOn (fun t => ∫ s in 0..t, F (D a) s) (Icc 0 T) := by
      have hh := intervalIntegral.continuousOn_primitive_interval (show IntegrableOn (F (D a)) (uIcc 0 T) by
        simpa [uIcc_of_le hT] using hi (D a))
      simpa [uIcc_of_le hT] using hh
    exact (continuousOn_const.sub hh).congr (fun t ht => he a t ht)
  refine ⟨hc,?_⟩
  intro a t ht
  have hcc : Icc 0 T ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hcont : ContinuousAt (F (D a)) t := (hc (D a) t ⟨ht.1.le,ht.2.le⟩).continuousAt hcc
  have hint : IntervalIntegrable (F (D a)) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1.le).mpr
      ((hi (D a)).mono_set (Icc_subset_Icc_right ht.2.le))
  have hd := (intervalIntegral.integral_hasDerivAt_right hint
    ⟨Icc 0 T,hcc,(hi (D a)).aestronglyMeasurable⟩ hcont).const_sub (f a)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hcc] with s hs
  exact he a s hs

end TamingCompatibility.GeometricHilbert.WeakHeat

end
end

end

end OAI
