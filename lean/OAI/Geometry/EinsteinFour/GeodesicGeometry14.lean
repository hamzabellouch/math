import OAI.Geometry.EinsteinFour.GeodesicGeometry05
import OAI.Geometry.EinsteinFour.GeodesicGeometry12
import OAI.Geometry.EinsteinFour.GeodesicGeometry13
import OAI.Geometry.EinsteinFour.LocalIncrementMeanValue
import OAI.Geometry.EinsteinFour.MetricChartDistance
import OAI.Geometry.EinsteinFour.WeylEstimates14

namespace OAI


section

/-! The actual cut locus equals the two chart images. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

theorem actual_complex_distance_le_radius (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (x : M) : metricDistance g e.base x ≤ complexJacobiRadius := by
  obtain ⟨P,rfl⟩ := actualComplexProjectiveMap_surjective hRic hminus hdim W hstar hw hz e he hstd x
  obtain ⟨t,ht,q,rfl⟩ := complexProjectivePolar_surjective P
  rw [actualComplexProjectiveMap_radial hRic hminus hdim W hstar hw hz e he hstd t ht q]
  exact ht.2

theorem complexCutChartImage_iff (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (c : M) (A : FourSpace ≃L[ℝ] FourSpace) (x : FourSpace)
    (hx : A x ∈ (chartAt FourSpace c).target) :
    x ∈ ⋃ i, complexCutChartMap g o e c A.symm.toContinuousLinearMap i ''
      complexCutChartDomain g o e c i ↔
    metricDistance g e.base ((chartAt FourSpace c).symm (A x)) = complexJacobiRadius := by
  constructor
  · intro h
    obtain ⟨i,z,hzdom,hcoord⟩ := mem_iUnion.mp h
    have hchart : chartAt FourSpace c (actualComplexProjectiveMap g o e (complexCutPoint i z)) = A x := by
      have hh := congrArg A hcoord
      simpa only [complexCutChartMap,ContinuousLinearEquiv.coe_coe,A.apply_symm_apply] using hh
    have hF : actualComplexProjectiveMap g o e (complexCutPoint i z) =
        (chartAt FourSpace c).symm (A x) := by
      rw [← hchart]
      exact ((chartAt FourSpace c).left_inv hzdom).symm
    rw [← hF]
    exact (actualComplexProjectiveMap_cut_iff hRic hminus hdim W hstar hw hz e he hstd _).mpr
      (cp2UnitRep_cut_head i z)
  · intro h
    obtain ⟨i,z,_,hF⟩ := (actual_complex_cut_disk_cover hRic hminus hdim W hstar hw hz e he hstd _).mp h
    refine mem_iUnion.mpr ⟨i,z,?_,?_⟩
    · change actualComplexProjectiveMap g o e (complexCutPoint i z) ∈ (chartAt FourSpace c).source
      rw [hF]
      exact (chartAt FourSpace c).map_target hx
    · change A.symm (chartAt FourSpace c (actualComplexProjectiveMap g o e (complexCutPoint i z))) = x
      rw [hF,(chartAt FourSpace c).right_inv hx,A.symm_apply_apply]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Actual inverse-distance control on a chart, including detours around its cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjective_section_chart_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (c : M) (A : FourSpace ≃L[ℝ] FourSpace) (V : Set FourSpace)
    (hV : IsOpen V) (hconv : Convex ℝ V) (hVT : ∀ x ∈ V, A x ∈ (chartAt FourSpace c).target)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ V, ∀ y ∈ V,
      metricDistance g ((chartAt FourSpace c).symm (A x)) ((chartAt FourSpace c).symm (A y)) ≤ K*dist x y)
    (x y : FourSpace) (hx : x ∈ V) (hy : y ∈ V)
    (hxR : metricDistance g e.base ((chartAt FourSpace c).symm (A x)) < complexJacobiRadius)
    (hyR : metricDistance g e.base ((chartAt FourSpace c).symm (A y)) < complexJacobiRadius) :
    fubiniStudyDistance (S ((chartAt FourSpace c).symm (A x)))
      (S ((chartAt FourSpace c).symm (A y))) ≤ (Real.sqrt 2)⁻¹*K*dist x y := by
  let T : FourSpace → M := fun z => (chartAt FourSpace c).symm (A z)
  let p := complexCutChartMap g o e c A.symm.toContinuousLinearMap
  let U := complexCutChartDomain g o e c
  let G := V \ ⋃ i, p i '' U i
  have hgood (z : FourSpace) (hzG : z ∈ G) : metricDistance g e.base (T z) < complexJacobiRadius := by
    apply lt_of_le_of_ne (actual_complex_distance_le_radius hRic hminus hdim W hstar hw hz e he hstd (T z))
    intro heq
    exact hzG.2 ((complexCutChartImage_iff hRic hminus hdim W hstar hw hz e he hstd c A z (hVT z hzG.1)).mpr heq)
  have hT : ContinuousOn T V :=
    (chartAt FourSpace c).symm.continuousOn.comp A.continuous.continuousOn hVT
  have hcont : ContinuousOn (S ∘ T) G := by
    intro z hzG
    exact (actualComplexProjective_section_continuousAt hRic hminus hdim W hstar hw hz e he hstd
      S hS (T z) (hgood z hzG)).comp_continuousWithinAt ((hT z hzG.1).mono sdiff_subset)
  have hlocal (z : FourSpace) (hzG : z ∈ G) :
      ∀ᶠ w in 𝓝[G] z, dist ((S ∘ T) z) ((S ∘ T) w) ≤ ((Real.sqrt 2)⁻¹*K)*dist z w := by
    have hD : ContinuousWithinAt (fun w => metricDistance g (T z) (T w)) V z :=
      (metricDistance_continuous g).continuousAt.comp_continuousWithinAt
        (continuousWithinAt_const.prodMk (hT z hzG.1))
    have hzpos : 0 < complexJacobiRadius-metricDistance g e.base (T z) := sub_pos.mpr (hgood z hzG)
    have hD0 : metricDistance g (T z) (T z) = 0 := (metricDistance_eq_zero_iff g _ _).mpr rfl
    have hevent : ∀ᶠ w in 𝓝[V] z,
        metricDistance g (T z) (T w) < complexJacobiRadius-metricDistance g e.base (T z) := by
      exact hD.eventually (gt_mem_nhds (by
        change metricDistance g (T z) (T z) < _
        rwa [hD0]))
    filter_upwards [nhdsWithin_mono z (show G ⊆ V from sdiff_subset) hevent,
      self_mem_nhdsWithin] with w hwclose hwG
    have heq := actualComplexProjective_section_local_distance hRic hminus hdim W hstar hw hz e he hstd
      S hS (T z) (T w) (by linarith)
    change fubiniStudyDistance (S (T z)) (S (T w)) ≤ _
    calc
      _ = (Real.sqrt 2)⁻¹ * metricDistance g (T z) (T w) := by
        rw [← heq,← mul_assoc,inv_mul_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),one_mul]
      _ ≤ (Real.sqrt 2)⁻¹ * (K * dist z w) :=
        mul_le_mul_of_nonneg_left (hbound z hzG.1 w hwG.1) (by positivity)
      _ = _ := by ring
  have hxG : x ∈ G := ⟨hx,fun hh => (ne_of_lt hxR)
    ((complexCutChartImage_iff hRic hminus hdim W hstar hw hz e he hstd c A x (hVT x hx)).mp hh)⟩
  have hyG : y ∈ G := ⟨hy,fun hh => (ne_of_lt hyR)
    ((complexCutChartImage_iff hRic hminus hdim W hstar hw hz e he hstd c A y (hVT y hy)).mp hh)⟩
  exact dist_le_of_complexThinSet (S ∘ T) p U
    (fun i => complexCutChartMap_locallyLipschitz hRic hminus hdim W hstar hw hz e he hstd c A.symm.toContinuousLinearMap i)
    V hV hconv ((Real.sqrt 2)⁻¹*K) (mul_nonneg (by positivity) hK) hcont hlocal x y hxG hyG

end
end PositiveEinsteinFour.Geometry
end


section

/-! Continuous inverse chart bounds hold at the cut locus as well. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjective_section_chart_all_distance_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (hSc : Continuous S) (c : M) (A : FourSpace ≃L[ℝ] FourSpace) (V : Set FourSpace)
    (hV : IsOpen V) (hconv : Convex ℝ V) (hVT : ∀ x ∈ V, A x ∈ (chartAt FourSpace c).target)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ x ∈ V, ∀ y ∈ V,
      metricDistance g ((chartAt FourSpace c).symm (A x)) ((chartAt FourSpace c).symm (A y)) ≤ K*dist x y)
    (x y : FourSpace) (hx : x ∈ V) (hy : y ∈ V) :
    fubiniStudyDistance (S ((chartAt FourSpace c).symm (A x)))
      (S ((chartAt FourSpace c).symm (A y))) ≤ (Real.sqrt 2)⁻¹*K*dist x y := by
  let T : FourSpace → M := fun z => (chartAt FourSpace c).symm (A z)
  let p := complexCutChartMap g o e c A.symm.toContinuousLinearMap
  let U := complexCutChartDomain g o e c
  let D := (⋃ i, p i '' U i)ᶜ
  have hp := fun i => complexCutChartMap_locallyLipschitz hRic hminus hdim W hstar hw hz e he hstd c A.symm.toContinuousLinearMap i
  have hD : Dense D := complexParametrizedImage_compl_dense p U hp
  have hT : ContinuousOn T V :=
    (chartAt FourSpace c).symm.continuousOn.comp A.continuous.continuousOn hVT
  have hcont : ContinuousOn (S ∘ T) V := hSc.comp_continuousOn hT
  have hgood (z : FourSpace) (hzV : z ∈ V) (hzD : z ∈ D) :
      metricDistance g e.base (T z) < complexJacobiRadius := by
    apply lt_of_le_of_ne (actual_complex_distance_le_radius hRic hminus hdim W hstar hw hz e he hstd (T z))
    intro heq
    exact hzD ((complexCutChartImage_iff hRic hminus hdim W hstar hw hz e he hstd c A z (hVT z hzV)).mpr heq)
  exact dist_le_on_open_of_dense D hD V hV (S ∘ T) hcont ((Real.sqrt 2)⁻¹*K)
    (fun z hzV hzD w hwV hwD => actualComplexProjective_section_chart_distance_le
      hRic hminus hdim W hstar hw hz e he hstd S hS c A V hV hconv hVT K hK hbound
      z w hzV hwV (hgood z hzV hzD) (hgood w hwV hwD)) x y hx hy

end
end PositiveEinsteinFour.Geometry
end


section

/-! Density and the actual chart distance estimate give singleton fibers at the cut locus. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjectiveMap_interior_distance_lt (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    {P : ComplexProjective2} (hP : P ∈ complexProjectiveInterior) :
    metricDistance g e.base (actualComplexProjectiveMap g o e P) < complexJacobiRadius := by
  obtain ⟨t,ht,q,rfl⟩ := hP
  rw [actualComplexProjectiveMap_radial hRic hminus hdim W hstar hw hz e he hstd t ⟨ht.1,ht.2.le⟩ q]
  exact ht.2

theorem actualComplexProjectiveMap_injective (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    : Function.Injective (actualComplexProjectiveMap g o e) := by
  let F := actualComplexProjectiveMap g o e
  have hsurj : Function.Surjective F := actualComplexProjectiveMap_surjective hRic hminus hdim W hstar hw hz e he hstd
  let S := actualComplexProjectiveSection g o e hsurj
  have hS : Function.RightInverse S F := actualComplexProjectiveSection_rightInverse e hsurj
  have hF : Continuous F := actualComplexProjectiveMap_continuous hRic hminus hdim W hstar hw hz e he hstd
  intro P Q hPQ
  change F P = F Q at hPQ
  let c := F P
  obtain ⟨u,hu,huP⟩ := exists_complexInterior_sequence P
  obtain ⟨v,hv,hvQ⟩ := exists_complexInterior_sequence Q
  have huR (n : ℕ) : metricDistance g e.base (F (u n)) < complexJacobiRadius :=
    actualComplexProjectiveMap_interior_distance_lt hRic hminus hdim W hstar hw hz e he hstd (hu n)
  have hvR (n : ℕ) : metricDistance g e.base (F (v n)) < complexJacobiRadius :=
    actualComplexProjectiveMap_interior_distance_lt hRic hminus hdim W hstar hw hz e he hstd (hv n)
  have huS (n : ℕ) : S (F (u n)) = u n :=
    actualComplexProjectiveMap_fiber_eq_of_radial_lt hRic hminus hdim W hstar hw hz e he hstd
      _ _ (hS _) (by change metricDistance g e.base (F (S (F (u n)))) < _; rw [hS]; exact huR n)
  have hvS (n : ℕ) : S (F (v n)) = v n :=
    actualComplexProjectiveMap_fiber_eq_of_radial_lt hRic hminus hdim W hstar hw hz e he hstd
      _ _ (hS _) (by change metricDistance g e.base (F (S (F (v n)))) < _; rw [hS]; exact hvR n)
  have huc : Tendsto (fun n => F (u n)) atTop (𝓝 c) := hF.continuousAt.tendsto.comp huP
  have hvc : Tendsto (fun n => F (v n)) atTop (𝓝 c) := by
    simpa only [c,← hPQ,Function.comp_def] using! hF.continuousAt.tendsto.comp hvQ
  let Z := chartAt FourSpace c
  have hcsrc : c ∈ Z.source := mem_chart_source FourSpace c
  have huchart : Tendsto (fun n => Z (F (u n))) atTop (𝓝 (Z c)) := (Z.continuousAt hcsrc).tendsto.comp huc
  have hvchart : Tendsto (fun n => Z (F (v n))) atTop (𝓝 (Z c)) := (Z.continuousAt hcsrc).tendsto.comp hvc
  obtain ⟨r,hr,K,hball,hbound⟩ := exists_metric_chart_bound g c
  let V := Metric.ball (Z c) r
  have hVT (z : FourSpace) (hzV : z ∈ V) : z ∈ Z.target := hball (Metric.ball_subset_closedBall hzV)
  have hb (x : FourSpace) (hx : x ∈ V) (y : FourSpace) (hy : y ∈ V) :
      metricDistance g (Z.symm x) (Z.symm y) ≤ (K : ℝ)*dist x y := by
    have hh := hbound x (Metric.ball_subset_closedBall hx) y (Metric.ball_subset_closedBall hy)
    rw [← ofReal_metricDistance g,edist_dist,← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (p := (K : ℝ)) K.property] at hh
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg K.property dist_nonneg)).mp hh
  have hboundSeq : ∀ᶠ n in atTop, fubiniStudyDistance (u n) (v n) ≤
      (Real.sqrt 2)⁻¹*(K : ℝ)*dist (Z (F (u n))) (Z (F (v n))) := by
    filter_upwards [huchart (Metric.ball_mem_nhds _ hr),hvchart (Metric.ball_mem_nhds _ hr),
      huc (Z.open_source.mem_nhds hcsrc),hvc (Z.open_source.mem_nhds hcsrc)] with n hun hvn hus hvs
    have hsu : (chartAt FourSpace c).symm (Z (F (u n))) = F (u n) := Z.left_inv hus
    have hsv : (chartAt FourSpace c).symm (Z (F (v n))) = F (v n) := Z.left_inv hvs
    have hh := actualComplexProjective_section_chart_distance_le hRic hminus hdim W hstar hw hz e he hstd
      S hS c (ContinuousLinearEquiv.refl ℝ FourSpace) V Metric.isOpen_ball (convex_ball _ _)
      hVT (K : ℝ) K.property hb (Z (F (u n))) (Z (F (v n))) hun hvn
      (by simpa only [ContinuousLinearEquiv.refl_apply,hsu] using huR n)
      (by simpa only [ContinuousLinearEquiv.refl_apply,hsv] using hvR n)
    simpa only [ContinuousLinearEquiv.refl_apply,hsu,hsv,huS,hvS] using hh
  have hleft : Tendsto (fun n => fubiniStudyDistance (u n) (v n)) atTop
      (𝓝 (fubiniStudyDistance P Q)) := continuous_dist.continuousAt.tendsto.comp (huP.prodMk_nhds hvQ)
  have hright : Tendsto (fun n => (Real.sqrt 2)⁻¹*(K : ℝ)*dist (Z (F (u n))) (Z (F (v n))))
      atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := (Real.sqrt 2)⁻¹*(K : ℝ))).mul
      (continuous_dist.continuousAt.tendsto.comp (huchart.prodMk_nhds hvchart))
    simpa only [Function.comp_def,dist_self,mul_zero] using! hh
  have hzero : fubiniStudyDistance P Q = 0 := le_antisymm
    (le_of_tendsto_of_tendsto hleft hright hboundSeq) (by
      rw [fubiniStudyDistance_eq_arccos]; exact Real.arccos_nonneg _)
  exact (fubiniStudyDistance_eq_zero_iff P Q).mp hzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual CP2 parametrization is a global homeomorphism. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

def actualComplexHomeomorph (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    : ComplexProjective2 ≃ₜ M := by
  let : CompactSpace ComplexProjective2 := complexProjective_compactSpace
  let E := Equiv.ofBijective (actualComplexProjectiveMap g o e)
    ⟨actualComplexProjectiveMap_injective hRic hminus hdim W hstar hw hz e he hstd,
      actualComplexProjectiveMap_surjective hRic hminus hdim W hstar hw hz e he hstd⟩
  exact Continuous.homeoOfEquivCompactToT2 (f := E)
    (actualComplexProjectiveMap_continuous hRic hminus hdim W hstar hw hz e he hstd)

theorem actualComplexHomeomorph_apply (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (P : ComplexProjective2) :
    actualComplexHomeomorph hRic hminus hdim W hstar hw hz e he hstd P =
      actualComplexProjectiveMap g o e P := rfl

end
end PositiveEinsteinFour.Geometry
end


section

/-! Arbitrarily sharp inverse metric bounds on neighborhoods of every actual point. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

def complexInverseDistortion (δ : ℝ) : ℝ := (Real.sqrt 2)⁻¹ * Real.sqrt (1+δ) * (1 / Real.sqrt (1-δ))

theorem actualComplexProjective_inverse_local_bound (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (hSc : Continuous S) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (c : M) :
    ∃ N ∈ 𝓝 c, ∀ x ∈ N, ∀ y ∈ N,
      fubiniStudyDistance (S x) (S y) ≤ complexInverseDistortion δ * metricDistance g x y := by
  obtain ⟨A,V,hV,hconv,hcenter,hVT,hup,hlo⟩ := exists_sharp_linear_chart_neighborhood g c δ hδ hδ1
  let Z := chartAt FourSpace c
  let k : M → FourSpace := fun x => A.symm (Z x)
  let N := Z.source ∩ k ⁻¹' V
  have hk : ContinuousAt k c := A.symm.continuous.continuousAt.comp
    (Z.continuousAt (mem_chart_source FourSpace c))
  have hN : N ∈ 𝓝 c := inter_mem (Z.open_source.mem_nhds (mem_chart_source FourSpace c))
    (hk (hV.mem_nhds hcenter))
  refine ⟨N,hN,?_⟩
  intro x hx y hy
  have hxinv : Z.symm (A (k x)) = x := by rw [A.apply_symm_apply,Z.left_inv hx.1]
  have hyinv : Z.symm (A (k y)) = y := by rw [A.apply_symm_apply,Z.left_inv hy.1]
  have h1 := actualComplexProjective_section_chart_all_distance_le hRic hminus hdim W hstar hw hz e he hstd
    S hS hSc c A V hV hconv hVT (Real.sqrt (1+δ)) (Real.sqrt_nonneg _) hup
    (k x) (k y) hx.2 hy.2
  change fubiniStudyDistance (S (Z.symm (A (k x)))) (S (Z.symm (A (k y)))) ≤ _ at h1
  rw [hxinv,hyinv] at h1
  have h2 := hlo (k x) hx.2 (k y) hy.2
  change dist (k x) (k y) ≤ (1 / Real.sqrt (1-δ))*metricDistance g (Z.symm (A (k x))) (Z.symm (A (k y))) at h2
  rw [hxinv,hyinv] at h2
  calc
    _ ≤ ((Real.sqrt 2)⁻¹*Real.sqrt (1+δ))*dist (k x) (k y) := h1
    _ ≤ ((Real.sqrt 2)⁻¹*Real.sqrt (1+δ))*((1 / Real.sqrt (1-δ))*metricDistance g x y) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by unfold complexInverseDistortion; ring

end
end PositiveEinsteinFour.Geometry
end


section

/-! The continuous actual inverse preserves the length bound along every unit geodesic. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjective_inverse_geodesic_le (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (S : M → ComplexProjective2) (hS : Function.RightInverse S (actualComplexProjectiveMap g o e))
    (hSc : Continuous S) (f : FrameBundle g) (d : ℝ) (hd : 0 ≤ d) :
    fubiniStudyDistance (S (frameGeodesic g 0 f 0)) (S (frameGeodesic g 0 f d)) ≤ (Real.sqrt 2)⁻¹*d := by
  let γ := frameGeodesic g 0 f
  have hγ : Continuous γ := (frameGeodesic_contMDiff g 0 f).continuous
  let q : ℝ → ℝ := fun t => fubiniStudyDistance (S (γ 0)) (S (γ t))
  have hq : Continuous q := continuous_dist.comp (continuous_const.prodMk (hSc.comp hγ))
  have hδbound (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) : q d ≤ complexInverseDistortion δ*d := by
    have hC : 0 ≤ complexInverseDistortion δ := by unfold complexInverseDistortion; positivity
    have hinc (t : ℝ) (_ht : t ∈ Ico (0 : ℝ) d) :
        ∀ᶠ s in 𝓝[>] t, q s-q t ≤ complexInverseDistortion δ*(s-t) := by
      obtain ⟨N,hN,hbound⟩ := actualComplexProjective_inverse_local_bound hRic hminus hdim
        W hstar hw hz e he hstd S hS hSc δ hδ hδ1 (γ t)
      have htN : γ t ∈ N := mem_of_mem_nhds hN
      have hev : ∀ᶠ s in 𝓝[>] t, γ s ∈ N :=
        (hγ.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hN
      filter_upwards [hev,self_mem_nhdsWithin] with s hs hts
      have htri : q s-q t ≤ fubiniStudyDistance (S (γ t)) (S (γ s)) := by
        dsimp [q]
        linarith [fubiniStudyDistance_triangle (S (γ 0)) (S (γ t)) (S (γ s))]
      have hg : metricDistance g (γ t) (γ s) ≤ s-t := by
        simpa only [γ,abs_of_nonneg (sub_nonneg.mpr (show t ≤ s from le_of_lt hts))] using frameGeodesic_metricDistance_le f t s
      exact htri.trans ((hbound _ htN _ hs).trans (mul_le_mul_of_nonneg_left hg hC))
    have hh := sub_le_of_local_increment q 0 d (complexInverseDistortion δ) hd hq.continuousOn hinc
    simpa only [q,fubiniStudyDistance_self,sub_zero] using hh
  have hc : ContinuousAt complexInverseDistortion 0 := by
    unfold complexInverseDistortion
    fun_prop (disch := norm_num)
  have hlim : Tendsto (fun δ => complexInverseDistortion δ*d) (𝓝[>] (0 : ℝ))
      (𝓝 ((Real.sqrt 2)⁻¹*d)) := by
    have hh := (hc.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)).mul_const d
    simpa [complexInverseDistortion] using hh
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with δ hδ hδ1
  exact hδbound δ hδ hδ1

end
end PositiveEinsteinFour.Geometry
end


section

/-! Global distance preservation of the actual complex projective parametrization. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actualComplexProjectiveMap_distance_ge (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (P Q : ComplexProjective2) :
    fubiniStudyDistance P Q ≤ (Real.sqrt 2)⁻¹ *
      metricDistance g (actualComplexProjectiveMap g o e P) (actualComplexProjectiveMap g o e Q) := by
  let H := actualComplexHomeomorph hRic hminus hdim W hstar hw hz e he hstd
  let f : FrameBundle g := ⟨H P,o.frame (H P)⟩
  have hf : f ∈ o.positive := o.frame_positive (H P)
  have hcover := frameExponential_complex_closedBall_image hRic hminus hdim f hf
  have hmem : H Q ∈ frameExponential g o f '' Metric.closedBall 0 complexJacobiRadius := by
    rw [hcover]
    trivial
  obtain ⟨v,hv,hend⟩ := hmem
  have hvR : ‖v‖ ≤ complexJacobiRadius := by simpa only [Metric.mem_closedBall,dist_zero_right] using hv
  have hdist : ‖v‖ = metricDistance g (H P) (H Q) := by
    have hh := frameExponential_complex_minimizing hRic hminus hdim f hf v hvR
    rw [hend] at hh
    exact hh.symm
  by_cases hv0 : v = 0
  · have hPQ : P = Q := by
      apply H.injective
      simpa only [hv0,frameExponential_zero] using hend
    subst Q
    rw [fubiniStudyDistance_self]
    exact mul_nonneg (by positivity) (metricDistance_nonneg g _ _)
  let q : Directions := ⟨‖v‖⁻¹ • v,by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]⟩
  let f' := f.rotate (orientedToOrthogonal (directionOrientedMatrix q))
  have hrad : ‖v‖ • q.val = v := by
    change ‖v‖ • (‖v‖⁻¹ • v) = v
    rw [smul_smul,mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0),one_smul]
  have hstart : frameGeodesic g 0 f' 0 = H P := by
    simp only [frameGeodesic,parallelFrameFlowMap_zero]
    rfl
  have hfinish : frameGeodesic g 0 f' ‖v‖ = H Q := by
    rw [← frameExponential_direction_ray g o f hf q ‖v‖,hrad,hend]
  have hS : Function.RightInverse H.symm (actualComplexProjectiveMap g o e) :=
    fun x => H.apply_symm_apply x
  have hh := actualComplexProjective_inverse_geodesic_le hRic hminus hdim W hstar hw hz e he hstd
    H.symm hS H.symm.continuous f' ‖v‖ (norm_nonneg _)
  rw [hstart,hfinish,H.symm_apply_apply,H.symm_apply_apply,hdist] at hh
  exact hh

theorem actualComplexProjectiveMap_distance_eq (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1)
    (W : smoothTwoForms o) (hstar : ∀ x, twoFormHodge (W.val x) = W.val x)
    (hw : ∀ x, ‖W.val x‖ ^ 2 = 2)
    (hz : ∀ f : FrameBundle g, twoFormFramedCovariantDerivative o W.val f = 0)
    (e : FrameBundle g) (he : e ∈ o.positive)
    (hstd : twoFormFrameValue o W.val e = standardSelfDualForm)
    (P Q : ComplexProjective2) :
    metricDistance g (actualComplexProjectiveMap g o e P) (actualComplexProjectiveMap g o e Q) =
      Real.sqrt 2 * fubiniStudyDistance P Q := by
  apply le_antisymm (actualComplexProjectiveMap_distance_le hRic hminus hdim W hstar hw hz e he hstd P Q)
  have h := mul_le_mul_of_nonneg_left
    (actualComplexProjectiveMap_distance_ge hRic hminus hdim W hstar hw hz e he hstd P Q)
    (Real.sqrt_nonneg 2)
  simpa only [← mul_assoc,mul_inv_cancel₀ (by positivity : Real.sqrt 2 ≠ 0),one_mul] using h

end
end PositiveEinsteinFour.Geometry
end


section

/-! The dimension-one branch is the actual Fubini--Study model after scaling by one half. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour Angular Jacobi Set Filter Bundle
open scoped Manifold ContDiff _root_.Topology ENNReal NNReal
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {o : FrameOrientation g}

attribute [local instance] complexProjectiveMetric

theorem actual_complex_projective_model (hRic : RicciThree g)
    (hminus : ∀ x, minusWeyl g x (o.frame x) = 0)
    (hdim : Module.finrank ℝ (smoothHarmonicPositive (o := o) hRic) = 1) :
    ScaledIsometricTo g (1/2) fubiniStudyDistance := by
  let x : M := Classical.choice inferInstance
  obtain ⟨W,hstar,hw,hz,e,_,he,hstd⟩ := halfFlat_dimension_one_standard_frame hRic hminus hdim x
  let H := actualComplexHomeomorph hRic hminus hdim W hstar hw hz e he hstd
  refine ⟨H.symm.toEquiv,?_⟩
  intro p q
  have hdist := actualComplexProjectiveMap_distance_eq hRic hminus hdim W hstar hw hz e he hstd
    (H.symm p) (H.symm q)
  change metricDistance g (H (H.symm p)) (H (H.symm q)) =
    Real.sqrt 2 * fubiniStudyDistance (H.symm p) (H.symm q) at hdist
  rw [H.apply_symm_apply,H.apply_symm_apply] at hdist
  have hsqrt : Real.sqrt (1/2 : ℝ) * Real.sqrt 2 = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
    norm_num
  change ENNReal.ofReal (fubiniStudyDistance (H.symm p) (H.symm q)) = scaledEDistance g (1/2) p q
  rw [scaledEDistance]
  change ENNReal.ofReal (fubiniStudyDistance (H.symm p) (H.symm q)) =
    ENNReal.ofReal (Real.sqrt (1/2 : ℝ)) * metricEDistance g p q
  rw [← ofReal_metricDistance g,← ENNReal.ofReal_mul (Real.sqrt_nonneg _),hdist]
  congr 1
  rw [← mul_assoc,hsqrt,one_mul]

end
end PositiveEinsteinFour.Geometry
end

end OAI
