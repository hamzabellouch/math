import OAI.Analysis.NodalLength.MetricFlux

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory
open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set
open scoped Topology ENNReal
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ENNReal ContDiff
open MeasureTheory Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ContDiff
open Filter Set
open scoped Topology ENNReal
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory TopologicalSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal ContDiff ComplexConjugate
open Filter Set MeasureTheory Laplacian
open scoped Topology ENNReal NNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ENNReal ContDiff CompactlySupported
open Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff Laplacian
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory Function
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open Filter Set MeasureTheory
open scoped BigOperators
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology ENNReal ContDiff BigOperators
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open Set MeasureTheory
open scoped BigOperators
open scoped Classical
open scoped BigOperators Topology ENNReal
open Set MeasureTheory
open scoped BigOperators
open scoped Topology ENNReal ContDiff
open Filter Set MeasureTheory InnerProductSpace
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators Classical Topology
open Filter Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators Topology
open Set MeasureTheory
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators
open Set
open scoped BigOperators symmDiff
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators
open Set
open scoped BigOperators Classical
open Set
open scoped BigOperators Classical
open Set
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology ContDiff
open Filter Set MeasureTheory ComplexConjugate
open scoped Topology NNReal BoundedContinuousFunction
open Filter Set Metric
open scoped Topology ContDiff
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators
open Filter Set MeasureTheory
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric
open scoped Topology ComplexConjugate BigOperators
open Filter Set Metric Complex MeromorphicOn
open scoped Topology
open Set Metric Complex
open scoped Topology
open Set Metric
open scoped Topology ContDiff ENNReal
open Set MeasureTheory Metric
open scoped Topology
open Set Metric Complex MeasureTheory
open scoped ENNReal Topology
open Set Metric MeasureTheory TopologicalSpace Function
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory Filter
open scoped Topology ENNReal
open Set Metric MeasureTheory
open scoped Topology ComplexConjugate BigOperators ENNReal
open Filter Set Metric Complex MeasureTheory MeromorphicOn
open scoped Topology ContDiff Convolution ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff Convolution
open Filter Set Metric MeasureTheory
open scoped Topology ContDiff
open Filter Set Metric
open scoped Matrix
open scoped Topology ContDiff
open Filter Set Metric
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold

namespace SharpNodal.Geometry
variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

lemma smoothOn_pullback_metric {f : Plane → M} {s : Set Plane} (hs : IsOpen s)
    (hf : ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ f s) (v w : Plane) :
    ContDiffOn ℝ ∞ (fun y=>inner ℝ
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y v)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y w)) s := by
  have hc (a : Plane) : ContMDiff 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) := by
    intro y
    exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have ht:=hf.contMDiffOn_tangentMapWithin (m:=∞) (by simp) hs.uniqueMDiffOn
  have hv (a : Plane) : ContMDiffOn 𝓘(ℝ,Plane) (𝓘(ℝ,Plane)).tangent ∞
      (fun y=> (⟨f y,mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y a⟩ : TangentBundle 𝓘(ℝ,Plane) M)) s := by
    have hh:=ht.comp (hc a).contMDiffOn (show MapsTo (fun y:Plane=>(⟨y,a⟩ : TangentBundle 𝓘(ℝ,Plane) Plane)) s (Bundle.TotalSpace.proj ⁻¹' s) from fun _ hy=>hy)
    apply hh.congr
    intro y hy
    simp only [Function.comp_apply,tangentMapWithin,
      mfderivWithin_of_mem_nhds (I:=𝓘(ℝ,Plane)) (I':=𝓘(ℝ,Plane)) (f:=f) (hs.mem_nhds hy)]
  exact ((hv v).inner_bundle (hv w)).contDiffOn

lemma smoothOn_coordinateMetric (x : M) (i j : Fin 2) :
    ContDiffOn ℝ ∞ (fun y=>coordinateMetric x y i j) (chartAt Plane x).target :=
  smoothOn_pullback_metric (chartAt Plane x).open_target contMDiffOn_chart_symm _ _

lemma gram_two_positive {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (D : Plane →L[ℝ] F) (hi : Function.Injective D) :
    0 < inner ℝ (D (EuclideanSpace.single 0 1)) (D (EuclideanSpace.single 0 1)) ∧
    0 < inner ℝ (D (EuclideanSpace.single 0 1)) (D (EuclideanSpace.single 0 1))*
      inner ℝ (D (EuclideanSpace.single 1 1)) (D (EuclideanSpace.single 1 1))-
      (inner ℝ (D (EuclideanSpace.single 0 1)) (D (EuclideanSpace.single 1 1)))^2 := by
  let v:=D (EuclideanSpace.single 0 1)
  let w:=D (EuclideanSpace.single 1 1)
  let a:=inner ℝ v v
  let b:=inner ℝ v w
  let c:=inner ℝ w w
  have hv : v≠0 := by
    intro hz
    have hh:=hi (hz.trans D.map_zero.symm)
    have := congrArg (fun z:Plane=>z 0) hh
    norm_num at this
  have ha : 0<a:=real_inner_self_pos.mpr hv
  have hw : a • w-b • v≠0 := by
    intro hz
    have he : D (a • EuclideanSpace.single 1 1-b • EuclideanSpace.single 0 1)=D 0 := by
      simpa only [map_sub,map_smul,map_zero] using hz
    have hh:=congrArg (fun z:Plane=>z 1) (hi he)
    norm_num at hh
    exact ha.ne' hh
  have hp:=real_inner_self_pos.mpr hw
  have hab : inner ℝ w v=b:=real_inner_comm _ _
  have he : inner ℝ (a • w-b • v) (a • w-b • v)=a*(a*c-b^2) := by
    simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
      RCLike.conj_to_real,hab]
    dsimp [a,b,c]; ring
  rw [he] at hp
  exact ⟨ha,(mul_pos_iff.mp hp).resolve_right (fun h=>not_lt_of_ge ha.le h.1) |>.2⟩

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma coordinateMetric_symm (x : M) (y : Plane) (i j : Fin 2) :
    coordinateMetric x y i j=coordinateMetric x y j i := real_inner_comm _ _

omit [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma coordinateMetric_positive (x : M) {y : Plane} (hy : y∈(chartAt Plane x).target) :
    0<coordinateMetric x y 0 0 ∧ 0<(coordinateMetric x y).det := by
  have hh:=gram_two_positive (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (chartAt Plane x).symm y)
    ((mdifferentiable_chart (I:=𝓘(ℝ,Plane)) x).symm.mfderiv_injective hy)
  refine ⟨hh.1,?_⟩
  rw [Matrix.det_fin_two,coordinateMetric_symm x y 1 0]
  convert hh.2 using 1
  simp only [coordinateMetric,pow_two]
  rfl

def pullMetric (f : Plane → M) (y : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j=>inner ℝ (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y (EuclideanSpace.single i 1))
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) f y (EuclideanSpace.single j 1))

def ChartSmooth (e : OpenPartialHomeomorph M Plane) : Prop :=
  ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (e : M → Plane) e.source ∧
  ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (e.symm : Plane → M) e.target

omit [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma chartSmooth_chartAt (x : M) : ChartSmooth (chartAt Plane x) :=
  ⟨contMDiffOn_chart,contMDiffOn_chart_symm⟩

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma ChartSmooth.mdiff {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e) :
    e.MDifferentiable 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) :=
  ⟨he.1.mdifferentiableOn (by simp),he.2.mdifferentiableOn (by simp)⟩

lemma ChartSmooth.metric_smooth {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    (i j : Fin 2) : ContDiffOn ℝ ∞ (fun y=>pullMetric (e.symm : Plane → M) y i j) e.target :=
  smoothOn_pullback_metric e.open_target he.2 _ _

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma ChartSmooth.metric_positive {e : OpenPartialHomeomorph M Plane} (he : ChartSmooth e)
    {y : Plane} (hy : y∈e.target) : 0<pullMetric (e.symm : Plane → M) y 0 0 ∧
      0<(pullMetric (e.symm : Plane → M) y).det := by
  have hh:=gram_two_positive (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) e.symm y)
    (he.mdiff.symm.mfderiv_injective hy)
  refine ⟨hh.1,?_⟩
  have hp : 0<pullMetric (e.symm : Plane → M) y 0 0*pullMetric (e.symm : Plane → M) y 1 1-
      (pullMetric (e.symm : Plane → M) y 0 1)^2:=hh.2
  have hc : pullMetric (e.symm : Plane → M) y 1 0=pullMetric (e.symm : Plane → M) y 0 1 :=
    real_inner_comm _ _
  rw [Matrix.det_fin_two,hc]
  nlinarith [hp]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma exists_normalized_chart (x : M) : ∃e : OpenPartialHomeomorph M Plane,
    x∈e.source ∧ e x=0 ∧ ChartSmooth e ∧ pullMetric (e.symm : Plane → M) 0=1 := by
  let c:=chartAt Plane x
  have hx : x∈c.source:=mem_chart_source Plane x
  let y₀:=c x
  have hy : y₀∈c.target:=c.map_source hx
  let D : Plane ≃L[ℝ] TangentSpace 𝓘(ℝ,Plane) (c.symm y₀):=
    (mdifferentiable_chart (I:=𝓘(ℝ,Plane)) x).symm.mfderiv hy
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Plane) (c.symm y₀)):=D.toLinearEquiv.finiteDimensional
  have hdim : Module.finrank ℝ (TangentSpace 𝓘(ℝ,Plane) (c.symm y₀))=2 := by
    rw [← D.toLinearEquiv.finrank_eq]
    simp [Plane]
  let B : OrthonormalBasis (Fin 2) ℝ (TangentSpace 𝓘(ℝ,Plane) (c.symm y₀)):=
    (stdOrthonormalBasis ℝ _).reindex (finCongr hdim)
  let L : Plane ≃L[ℝ] Plane:=B.repr.symm.toContinuousLinearEquiv.trans D.symm
  let a : Plane ≃ₜ Plane:=L.toHomeomorph.trans (Homeomorph.addLeft y₀)
  have ha (y : Plane) : a y=y₀+L y:=rfl
  have hai (y : Plane) : a.symm y=L.symm (y-y₀):=by
    change L.symm (-y₀+y)=L.symm (y-y₀)
    congr 1; abel
  have haC : ContDiff ℝ ∞ (a : Plane → Plane):=contDiff_const.add L.contDiff
  have haiC : ContDiff ℝ ∞ (a.symm : Plane → Plane):=by
    have hh : ContDiff ℝ ∞ (fun y:Plane=>L.symm (y-y₀)):=
      L.symm.contDiff.comp (contDiff_id.sub contDiff_const)
    rw [show (a.symm : Plane → Plane)=(fun y=>L.symm (y-y₀)) from funext hai]
    exact hh
  have haiM : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (a.symm : Plane → Plane):=haiC.contMDiff
  have haM : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (a : Plane → Plane):=haC.contMDiff
  let e:=c.trans a.symm.toOpenPartialHomeomorph
  have he (z : M) : e z=a.symm (c z):=rfl
  have hei (y : Plane) : e.symm y=c.symm (a y):=rfl
  have heS : e.source=c.source:=by simp [e]
  have heT : e.target=a ⁻¹' c.target:=by simp [e]
  refine ⟨e,by rwa [heS],?_,?_,?_⟩
  · simp only [he,hai,y₀,sub_self,map_zero]
  · constructor
    · rw [heS]
      exact haiM.comp_contMDiffOn (chartSmooth_chartAt x).1
    · have hh := (chartSmooth_chartAt x).2.comp haM.contMDiffOn
        (show MapsTo (a : Plane → Plane) e.target c.target from fun _ hy=>by rwa [heT] at hy)
      exact hh
  · have hdc : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (c.symm : Plane → M) (a 0) := by
      simpa only [ha,map_zero,add_zero] using (mdifferentiable_chart (I:=𝓘(ℝ,Plane)) x).mdifferentiableAt_symm hy
    have hda : HasFDerivAt (a : Plane → Plane) (L : Plane →L[ℝ] Plane) 0 :=
      L.hasFDerivAt.const_add y₀
    have hd : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (e.symm : Plane → M) 0=
        (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (c.symm : Plane → M) (a 0)).comp (L : Plane →L[ℝ] Plane) := by
      change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ((c.symm : Plane → M) ∘ (a : Plane → Plane)) 0=_
      have hh:=mfderiv_comp 0 hdc ((haM.mdifferentiable (by simp)).mdifferentiableAt)
      rw [mfderiv_eq_fderiv,hda.fderiv] at hh
      exact hh
    ext i j
    unfold pullMetric
    rw [hd]
    change inner ℝ ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (c.symm : Plane → M) (a 0)) (L (EuclideanSpace.single i 1)))
      ((mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (c.symm : Plane → M) (a 0)) (L (EuclideanSpace.single j 1)))=_
    erw [ha,map_zero,add_zero]
    change inner ℝ (D (L (EuclideanSpace.single i 1))) (D (L (EuclideanSpace.single j 1)))= _
    have hh (v : Plane) : D (L v)=B.repr.symm v:=by simp [L]
    rw [hh,hh]
    calc
      _ = inner ℝ (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
        B.repr.symm.inner_map_map _ _
      _ = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by simp [EuclideanSpace.inner_single_left,Matrix.one_apply]

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff Bundle
open Filter Set Metric Bundle Manifold
namespace SharpNodal.Geometry
open Carleman Profiles.Elliptic

lemma partial_eventuallyEq {f g : Plane → ℝ} {x : Plane} (h : f=ᶠ[𝓝 x]g) (i : Fin 2) :
    coordPartial f i=ᶠ[𝓝 x]coordPartial g i := by
  filter_upwards [h.fderiv (𝕜:=ℝ)] with y hy
  exact congrArg (fun L:Plane →L[ℝ] ℝ=>L (EuclideanSpace.single i 1)) hy

lemma scalarLaplace_congr {a b c U a' b' c' U' : Plane → ℝ} {x : Plane}
    (ha : a=ᶠ[𝓝 x]a') (hb : b=ᶠ[𝓝 x]b') (hc : c=ᶠ[𝓝 x]c') (hU : U=ᶠ[𝓝 x]U') :
    scalarLaplace a b c U x=scalarLaplace a' b' c' U' x := by
  have hρ : scalarDensity a b c=ᶠ[𝓝 x]scalarDensity a' b' c' := by
    filter_upwards [ha,hb,hc] with y hy0 hy1 hy2; simp only [scalarDensity,hy0,hy1,hy2]
  have hf0 : scalarFlux0 a b c U=ᶠ[𝓝 x]scalarFlux0 a' b' c' U' := by
    filter_upwards [hb,hc,hρ,partial_eventuallyEq hU 0,partial_eventuallyEq hU 1] with y hy0 hy1 hy2 hy3 hy4
    simp only [scalarFlux0,hy0,hy1,hy2,hy3,hy4]
  have hf1 : scalarFlux1 a b c U=ᶠ[𝓝 x]scalarFlux1 a' b' c' U' := by
    filter_upwards [ha,hb,hρ,partial_eventuallyEq hU 0,partial_eventuallyEq hU 1] with y hy0 hy1 hy2 hy3 hy4
    simp only [scalarFlux1,hy0,hy1,hy2,hy3,hy4]
  simp only [scalarLaplace,partial_congr_nhds hf0,partial_congr_nhds hf1,hρ.self_of_nhds]

variable {M : Type*} [MetricSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [RiemannianBundle (fun x : M=>TangentSpace 𝓘(ℝ,Plane) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)]

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma pullMetric_symm (F : Plane → M) (y : Plane) (i j : Fin 2) :
    pullMetric F y i j=pullMetric F y j i := real_inner_comm _ _

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma pullMetric_congr {F G : Plane → M} {x : Plane} (h : F=ᶠ[𝓝 x]G) :
    pullMetric F x=pullMetric G x := by
  have he:=h.self_of_nhds
  have hd:=h.mfderiv_eq (I:=𝓘(ℝ,Plane)) (I':=𝓘(ℝ,Plane))
  ext i j
  unfold pullMetric
  rw [he] at hd ⊢
  rw [hd]
  rfl

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma pullMetric_transform {F : Plane → M} {f g : Plane → ℝ} {x : Plane}
    (hF : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x))
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i j : Fin 2) :
    pullMetric (fun y=>F (coordMap f g y)) x i j=
      pullMetric F (coordMap f g x) 0 0*coordPartial f i x*coordPartial f j x+
      pullMetric F (coordMap f g x) 0 1*(coordPartial f i x*coordPartial g j x+
        coordPartial f j x*coordPartial g i x)+
      pullMetric F (coordMap f g x) 1 1*coordPartial g i x*coordPartial g j x := by
  have hp : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (coordMap f g) x:=
    (differentiableAt_coordMap hf hg).mdifferentiableAt
  have hd:=mfderiv_comp x hF hp
  rw [mfderiv_eq_fderiv,(hasFDerivAt_coordMap hf hg).fderiv] at hd
  have he (k : Fin 2) : mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) (fun y=>F (coordMap f g y)) x (EuclideanSpace.single k 1)=
      coordPartial f k x • mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (EuclideanSpace.single 0 1)+
      coordPartial g k x • mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (EuclideanSpace.single 1 1) := by
    erw [hd]
    change mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (_ + _) = _
    erw [map_add, map_smul, map_smul]
    rfl
  unfold pullMetric
  erw [he i,he j]
  simp only [inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,RCLike.conj_to_real]
  have hs:=real_inner_comm
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (EuclideanSpace.single 1 1))
    (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x) (EuclideanSpace.single 0 1))
  rw [hs]; ring

omit [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Plane) ∞ Plane (fun x:M=>TangentSpace 𝓘(ℝ,Plane) x)] in
lemma pullMetric_transform_three {F : Plane → M} {f g : Plane → ℝ} {x : Plane}
    (hF : MDifferentiableAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) F (coordMap f g x))
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    let a:=fun y=>pullMetric F y 0 0
    let b:=fun y=>pullMetric F y 0 1
    let c:=fun y=>pullMetric F y 1 1
    pullMetric (fun y=>F (coordMap f g y)) x 0 0=transformA a b c f g x ∧
    pullMetric (fun y=>F (coordMap f g y)) x 0 1=transformB a b c f g x ∧
    pullMetric (fun y=>F (coordMap f g y)) x 1 1=transformC a b c f g x := by
  dsimp
  rw [pullMetric_transform hF hf hg 0 0,pullMetric_transform hF hf hg 0 1,
    pullMetric_transform hF hf hg 1 1]
  unfold transformA transformB transformC
  exact ⟨by ring,by ring,by ring⟩

end SharpNodal.Geometry

noncomputable section
open scoped Topology ContDiff
open Filter Set Metric
namespace SharpNodal.Geometry

lemma smooth_mul_of_support {f a : Plane → ℝ} {s : Set Plane} (hs : IsOpen s)
    (hf : ContDiff ℝ ∞ f) (ha : ContDiffOn ℝ ∞ a s) (hsupp : tsupport f⊆s) :
    ContDiff ℝ ∞ (fun y=>f y*a y) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x∈tsupport f
  · exact hf.contDiffAt.mul (ha.contDiffAt (hs.mem_nhds (hsupp hx)))
  · apply (show ContDiffAt ℝ ∞ (fun _ : Plane => (0:ℝ)) x from contDiffAt_const).congr_of_eventuallyEq
    have hh : ∀ᶠy in 𝓝 x,y∉tsupport f:=(isClosed_tsupport f).isOpen_compl.mem_nhds hx
    filter_upwards [hh] with y hy
    simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]

lemma exists_smooth_local_extension {ι : Type*} (a : ι → Plane → ℝ) {s : Set Plane}
    (hs : IsOpen s) (h0 : (0:Plane)∈s) (ha : ∀i,ContDiffOn ℝ ∞ (a i) s) :
    ∃r : ℝ,∃A : ι → Plane → ℝ,0<r ∧ r<1 ∧ closedBall (0:Plane) r⊆s ∧
      (∀i,ContDiff ℝ ∞ (A i)) ∧ (∀i,EqOn (A i) (a i) (closedBall (0:Plane) r)) := by
  obtain ⟨d,hd,hdsub⟩:=Metric.mem_nhds_iff.mp (hs.mem_nhds h0)
  let R:=min (d/2) (1/2)
  have hR : 0<R:=lt_min (half_pos hd) (by norm_num)
  let χ : ContDiffBump (0:Plane):=⟨R/2,R,half_pos hR,half_lt_self hR⟩
  let A:=fun i y=>χ y*a i y
  refine ⟨R/2,A,half_pos hR,?_,?_,?_,?_⟩
  · exact lt_of_le_of_lt (by dsimp [R]; linarith [min_le_right (d/2) (1/2:ℝ)]) (by norm_num : (1/2:ℝ)<1)
  · intro y hy
    exact hdsub (mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hy).trans_lt (by change R/2 < d; dsimp [R]; linarith [min_le_left (d/2) (1/2:ℝ)])))
  · intro i
    apply smooth_mul_of_support hs χ.contDiff (ha i)
    rw [χ.tsupport_eq]
    intro y hy
    exact hdsub (mem_ball_zero_iff.mpr (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hy) (by change R < d; dsimp [R]; linarith [min_le_left (d/2) (1/2:ℝ)])))
  · intro i y hy
    dsimp [A]
    rw [χ.one_of_mem_closedBall hy,one_mul]

end SharpNodal.Geometry

end
end
end

end OAI
