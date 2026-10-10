import OAI.Geometry.Riemannian.HarmonicCore.SphericalMean
import OAI.Geometry.Riemannian.HarmonicCore.DirichletOperator

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution
open Matrix
open scoped RealInnerProductSpace

namespace HarmonicCounterexample.Main.SmoothMetric3

noncomputable def compactTrace (R : ℝ) :
    CompactSmoothData →ₗ[ℝ] C(Metric.sphere (0:E3) R,ℝ) where
  toFun H := ⟨fun x ↦ (H:E3 → ℝ) x,H.property.1.continuous.comp continuous_subtype_val⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl



lemma compactTrace_unit (R : ℝ) (hR : 0<R) :
    compactTrace R (boundaryUnit R hR)=1 := by
  ext p
  exact boundaryUnit_eq R hR p (by simpa only [Metric.mem_sphere,dist_zero_right] using p.property)



noncomputable def smoothTraceAlgebra (R : ℝ) (hR : 0<R) :
    Subalgebra ℝ C(Metric.sphere (0:E3) R,ℝ) where
  carrier := Set.range (compactTrace R)
  zero_mem' := ⟨0,(compactTrace R).map_zero⟩
  add_mem' := by
    rintro _ _ ⟨H,rfl⟩ ⟨K,rfl⟩
    exact ⟨H+K,(compactTrace R).map_add H K⟩
  one_mem' := ⟨boundaryUnit R hR,compactTrace_unit R hR⟩
  mul_mem' := by
    rintro _ _ ⟨H,rfl⟩ ⟨K,rfl⟩
    let HK : CompactSmoothData := ⟨(H:E3 → ℝ)*(K:E3 → ℝ),
      H.property.1.mul K.property.1,H.property.2.mul_right⟩
    exact ⟨HK,rfl⟩
  algebraMap_mem' c := by
    refine ⟨c • boundaryUnit R hR,?_⟩
    rw [(compactTrace R).map_smul,compactTrace_unit]
    simp only [Algebra.algebraMap_eq_smul_one]



lemma smoothTrace_separates (R : ℝ) (hR : 0<R) :
    (smoothTraceAlgebra R hR).SeparatesPoints := by
  intro x y hxy
  have hval : (x:E3) ≠ (y:E3) := fun h ↦ hxy (Subtype.ext h)
  obtain ⟨i,hi⟩ : ∃ i : Fin 3, (x:E3) i ≠ (y:E3) i := by
    by_contra hn
    push Not at hn
    exact hval (by ext i; exact hn i)
  let B := boundaryUnit R hR
  let H : CompactSmoothData := ⟨fun p ↦ (B:E3 → ℝ) p*p i,
    B.property.1.mul (EuclideanSpace.proj (𝕜:=ℝ) i).contDiff,B.property.2.mul_right⟩
  refine ⟨compactTrace R H,⟨compactTrace R H,⟨H,rfl⟩,rfl⟩,?_⟩
  change (B:E3 → ℝ) x*(x:E3) i ≠ (B:E3 → ℝ) y*(y:E3) i
  rw [boundaryUnit_eq R hR x (by simpa only [Metric.mem_sphere,dist_zero_right] using x.property),
    boundaryUnit_eq R hR y (by simpa only [Metric.mem_sphere,dist_zero_right] using y.property),one_mul,one_mul]
  exact hi



theorem compactTrace_dense (R : ℝ) (hR : 0<R) : DenseRange (compactTrace R) := by
  have h := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    (smoothTraceAlgebra R hR) (smoothTrace_separates R hR)
  change Dense (smoothTraceAlgebra R hR : Set C(Metric.sphere (0:E3) R,ℝ))
  rw [dense_iff_closure_eq]
  exact congrArg (fun A : Subalgebra ℝ C(Metric.sphere (0:E3) R,ℝ) ↦
    (A : Set C(Metric.sphere (0:E3) R,ℝ))) h



theorem compactTrace_L2_dense (R : ℝ) (hR : 0<R)
    (μ : Measure (Metric.sphere (0:E3) R)) [IsFiniteMeasure μ] [μ.WeaklyRegular] :
    DenseRange (fun H : CompactSmoothData ↦ ContinuousMap.toLp 2 μ ℝ (compactTrace R H)) := by
  exact (ContinuousMap.toLp_denseRange ℝ μ ℝ (by norm_num)).comp
    (compactTrace_dense R hR) (ContinuousMap.toLp 2 μ ℝ).continuous

end HarmonicCounterexample.Main.SmoothMetric3

namespace HarmonicCounterexample.Main

theorem smooth_source_boundary_dense :
    DenseRange (fun H : SmoothMetric3.CompactSmoothData ↦
      ContinuousMap.toLp 2 angularMeasure ℝ (SmoothMetric3.compactTrace 1 H)) :=
  SmoothMetric3.compactTrace_L2_dense 1 (by norm_num) angularMeasure

end HarmonicCounterexample.Main

namespace HarmonicCounterexample.Main.SmoothMetric3

noncomputable def radiusTrace (R : ℝ) : CompactSmoothData →ₗ[ℝ] C(UnitSphere3,ℝ) where
  toFun F := ⟨fun z ↦ (F:E3 → ℝ) (R • (z:E3)),
    F.property.1.continuous.comp (by fun_prop)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl



lemma radiusTrace_dense (R : ℝ) (hR : 0<R) : DenseRange (radiusTrace R) := by
  apply (compactTrace_dense 1 (by norm_num)).mono
  rintro _ ⟨F,rfl⟩
  let K : CompactSmoothData := ⟨fun x ↦ (F:E3 → ℝ) (R⁻¹ • x),
    F.property.1.comp (contDiff_id.const_smul (R⁻¹)),
    F.property.2.comp_smul (inv_ne_zero hR.ne')⟩
  refine ⟨K,?_⟩
  ext z
  change (F:E3 → ℝ) (R⁻¹ • (R • (z:E3)))=(F:E3 → ℝ) z
  rw [smul_smul,inv_mul_cancel₀ hR.ne',one_smul]



noncomputable def radiusTraceL2 (R : ℝ) : CompactSmoothData →ₗ[ℝ] Lp ℝ 2 angularMeasure :=
  (ContinuousMap.toLp 2 angularMeasure ℝ).toLinearMap.comp (radiusTrace R)



lemma radiusTraceL2_dense (R : ℝ) (hR : 0<R) : DenseRange (radiusTraceL2 R) :=
  (ContinuousMap.toLp_denseRange ℝ angularMeasure ℝ (by norm_num)).comp
    (radiusTrace_dense R hR) (ContinuousMap.toLp 2 angularMeasure ℝ).continuous

end HarmonicCounterexample.Main.SmoothMetric3

namespace HarmonicCounterexample.Main

lemma continuous_toL2_norm_sq (F : C(UnitSphere3,ℝ)) :
    ‖ContinuousMap.toLp 2 angularMeasure ℝ F‖^2 = ∫ z, (F z)^2 ∂angularMeasure := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℝ) angularMeasure F] with z hz
  simp only [hz,real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]



lemma radiusTraceL2_norm_sq (R : ℝ) (F : SmoothMetric3.CompactSmoothData) :
    ‖SmoothMetric3.radiusTraceL2 R F‖^2 =
      ∫ z : UnitSphere3, ((F:E3 → ℝ) (R • (z:E3)))^2 ∂angularMeasure :=
  continuous_toL2_norm_sq (SmoothMetric3.radiusTrace R F)

end HarmonicCounterexample.Main

end

end OAI
