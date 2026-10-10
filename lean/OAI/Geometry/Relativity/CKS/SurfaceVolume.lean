import OAI.Geometry.Relativity.CKS.ComparatorDefinitions
import OAI.Geometry.Relativity.CKS.VolumeUnique
import OAI.Geometry.Relativity.CKS.EmbeddingDerivative

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
variable [MeasurableSpace M] [BorelSpace M]

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

lemma chartFrame_eq_symmL (x : M) {y : E}
    (hy : y ∈ (extChartAt I x).target) :
    chartFrame x y = (trivializationAt E (TangentSpace I) x).symmL ℝ
      ((extChartAt I x).symm y) := by
  have hs : (extChartAt I x).symm y ∈ (chartAt H x).source := by
    simpa using (extChartAt I x).map_target hy
  rw [TangentBundle.symmL_trivializationAt hs, (extChartAt I x).right_inv hy]
  rfl

lemma chartFrame_continuousOn (x : M) (v : E) :
    ContinuousOn (fun y => (⟨(extChartAt I x).symm y, chartFrame x y v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target := by
  let e := trivializationAt E (TangentSpace I) x
  have h : ContinuousOn (fun y =>
      (⟨(extChartAt I x).symm y, e.symm ((extChartAt I x).symm y) v⟩ :
      TotalSpace E (TangentSpace I))) (extChartAt I x).target :=
    e.continuousOn_symm.comp
      ((continuousOn_extChartAt_symm x).prodMk continuousOn_const)
      (fun y hy => ⟨by simpa [e] using (extChartAt I x).map_target hy, mem_univ _⟩)
  apply h.congr
  intro y hy
  dsimp only
  congr 1
  rw [chartFrame_eq_symmL x hy, Trivialization.symmL_apply]
  simpa using (extChartAt I x).map_target hy

lemma chartMatrix_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartMatrix g x) (extChartAt I x).target := by
  let : RiemannianBundle (fun x : M => TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  exact (chartFrame_continuousOn x (basis i)).inner_bundle
    (chartFrame_continuousOn x (basis j))

lemma chartDensity_continuousOn (g : Metric (M := M)) (x : M) :
    ContinuousOn (chartDensity g x) (extChartAt I x).target := by
  exact ((continuous_id.matrix_det : Continuous (Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ)).comp_continuousOn (chartMatrix_continuousOn g x)).sqrt

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

abbrev stdBasis : Module.Basis (Fin 2) ℝ E := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis

lemma sqrt_gram_det_comp (B : LinearMap.BilinForm ℝ E) (L : E →L[ℝ] E) :
    Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis
      (B.comp L.toLinearMap L.toLinearMap)).det =
      |L.det| * Real.sqrt (LinearMap.BilinForm.toMatrix stdBasis B).det := by
  rw [LinearMap.BilinForm.toMatrix_comp stdBasis stdBasis,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix]
  change Real.sqrt (L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det) = _
  rw [show L.det * (LinearMap.BilinForm.toMatrix stdBasis B).det * L.det =
    L.det ^ 2 * (LinearMap.BilinForm.toMatrix stdBasis B).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def pullbackInner (g : Metric (M := M)) (x : M) (y : E) : LinearMap.BilinForm ℝ E :=
  (g.inner ((extChartAt I x).symm y)).toBilinForm.comp
    (chartFrame x y).toLinearMap (chartFrame x y).toLinearMap

lemma chartMatrix_eq_toMatrix (g : Metric (M := M)) (x : M) (y : E) :
    chartMatrix g x y = LinearMap.BilinForm.toMatrix stdBasis (pullbackInner g x y) := by
  rfl

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem real_id_compTriple :
    RingHomCompTriple (RingHom.id ℝ) (RingHom.id ℝ) (RingHom.id ℝ) := inferInstance
attribute [local instance] real_id_compTriple

def chartTransition (x z : M) : E → E := (extChartAt I x) ∘ (extChartAt I z).symm

def transitionDeriv (x z : M) (y : E) : E →L[ℝ] E :=
  (mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp (chartFrame z y)

lemma hasFDerivWithinAt_chartTransition (x z : M) {y : E}
    (hz : y ∈ (extChartAt I z).target)
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y) (range I) y := by
  have hxs : (extChartAt I z).symm y ∈ (chartAt H x).source := by simpa using hx
  exact ((mdifferentiableAt_extChartAt hxs).hasMFDerivAt.comp_hasMFDerivWithinAt y
    (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt).hasFDerivWithinAt

lemma chartFrame_comp_transitionDeriv (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    (chartFrame x (chartTransition x z y)).comp (transitionDeriv x z y) = chartFrame z y := by
  unfold transitionDeriv
  change (mfderivWithin 𝓘(ℝ,E) I (extChartAt I x).symm (range I)
    (extChartAt I x ((extChartAt I z).symm y))).comp
    ((mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp
    (chartFrame z y)) = chartFrame z y
  rw [← ContinuousLinearMap.comp_assoc,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx]
  rfl

lemma pullbackInner_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    pullbackInner g z y = (pullbackInner g x (chartTransition x z y)).comp
      (transitionDeriv x z y).toLinearMap (transitionDeriv x z y).toLinearMap := by
  ext v w
  change g.inner ((extChartAt I z).symm y) (chartFrame z y v) (chartFrame z y w) =
    g.inner ((extChartAt I x).symm (chartTransition x z y))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y v))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y w))
  have hv := congrArg (fun L : E →L[ℝ] E => L v) (chartFrame_comp_transitionDeriv x z hx)
  have hw := congrArg (fun L : E →L[ℝ] E => L w) (chartFrame_comp_transitionDeriv x z hx)
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y v) = _ at hv
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y w) = _ at hw
  rw [hv, hw]
  have heq : (extChartAt I x).symm (chartTransition x z y) = (extChartAt I z).symm y :=
    (extChartAt I x).left_inv hx
  rw [heq]
  rfl

lemma chartDensity_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    chartDensity g z y = |(transitionDeriv x z y).det| *
      chartDensity g x (chartTransition x z y) := by
  simp only [chartDensity, chartMatrix_eq_toMatrix]
  rw [pullbackInner_transition g x z hx, sqrt_gram_det_comp]

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

omit [IsManifold I 1 M] in
lemma chart_target_measurable [IsManifold I 1 M] (x : M) :
    MeasurableSet (extChartAt I x).target := by
  rw [extChartAt_target]
  exact ((chartAt H x).open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

variable [MeasurableSpace M] [BorelSpace M]

def chartPreimage (x : M) (s : Set M) : Set E :=
  (extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target

lemma chartPreimage_measurable (x : M) {s : Set M} (hs : MeasurableSet s) :
    MeasurableSet (chartPreimage x s) := by
  have h : Measurable ((extChartAt I x).target.domRestrict (extChartAt I x).symm) :=
    (continuousOn_iff_continuous_domRestrict.mp (continuousOn_extChartAt_symm x)).measurable
  have hm := (chart_target_measurable x).subtype_image (hs.preimage h)
  convert hm using 1
  ext y
  simp [chartPreimage]

lemma localVolume_apply (g : Metric (M := M)) (x : M) {s : Set M} (hs : MeasurableSet s) :
    localVolume g x s = ∫⁻ y in chartPreimage x s, ENNReal.ofReal (chartDensity g x y) := by
  have hf := (continuousOn_extChartAt_symm x).aemeasurable
    (μ := (volume : Measure E)) (chart_target_measurable x)
  rw [localVolume, Measure.map_apply_of_aemeasurable
    (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hs, withDensity_apply']
  rw [← Measure.restrict_comm (chart_target_measurable x),
    Measure.restrict_restrict (chart_target_measurable x)]
  congr 1
  exact congrArg ((volume : Measure E).restrict) (inter_comm _ _)

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]

omit [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M] in
lemma chartTransition_image [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    chartTransition x z '' chartPreimage z (s ∩ (extChartAt I x).source) =
      chartPreimage x (s ∩ (extChartAt I z).source) := by
  ext y
  constructor
  · rintro ⟨u, ⟨⟨hs,hx⟩,hu⟩,rfl⟩
    have heq : (extChartAt I x).symm (chartTransition x z u) = (extChartAt I z).symm u :=
      (extChartAt I x).left_inv hx
    refine ⟨?_, (extChartAt I x).map_source hx⟩
    change (extChartAt I x).symm (chartTransition x z u) ∈ s ∩ (extChartAt I z).source
    rw [heq]
    exact ⟨hs, (extChartAt I z).map_target hu⟩
  · rintro ⟨⟨hs,hz⟩,hy⟩
    refine ⟨extChartAt I z ((extChartAt I x).symm y), ?_, ?_⟩
    · refine ⟨?_, (extChartAt I z).map_source hz⟩
      change (extChartAt I z).symm (extChartAt I z ((extChartAt I x).symm y)) ∈
        s ∩ (extChartAt I x).source
      rw [(extChartAt I z).left_inv hz]
      exact ⟨hs, (extChartAt I x).map_target hy⟩
    · change extChartAt I x ((extChartAt I z).symm
        (extChartAt I z ((extChartAt I x).symm y))) = y
      rw [(extChartAt I z).left_inv hz, (extChartAt I x).right_inv hy]

omit [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M] in
lemma chartTransition_injOn [IsManifold I 1 M] [MeasurableSpace M] [BorelSpace M]
    (x z : M) (s : Set M) :
    InjOn (chartTransition x z) (chartPreimage z (s ∩ (extChartAt I x).source)) := by
  intro u hu v hv heq
  apply (extChartAt I z).symm.injOn hu.2 hv.2
  exact (extChartAt I x).injOn hu.1.2 hv.1.2 heq

lemma localVolume_compatible (g : Metric (M := M)) (x z : M) :
    (localVolume g x).restrict (extChartAt I z).source =
      (localVolume g z).restrict (extChartAt I x).source := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    localVolume_apply g x (hs.inter (isOpen_extChartAt_source z).measurableSet),
    localVolume_apply g z (hs.inter (isOpen_extChartAt_source x).measurableSet),
    ← chartTransition_image x z s]
  have hd : ∀ y ∈ chartPreimage z (s ∩ (extChartAt I x).source),
      HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y)
        (chartPreimage z (s ∩ (extChartAt I x).source)) y := by
    intro y hy
    exact (hasFDerivWithinAt_chartTransition x z hy.2 hy.1.2).mono
      (fun u hu => extChartAt_target_subset_range z hu.2)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
    hd (chartTransition_injOn x z s)]
  apply setLIntegral_congr_fun
    (chartPreimage_measurable z (hs.inter (isOpen_extChartAt_source x).measurableSet))
  intro y hy
  dsimp only
  rw [chartDensity_transition g x z hy.1.2, ENNReal.ofReal_mul (abs_nonneg _)]

end CKSSurfaceVolume

end

noncomputable section
open Set MeasureTheory
namespace CKSSurfaceVolume

lemma exists_measure_of_compatible {X ι : Type*} [MeasurableSpace X]
    (U : ι → Set X) (hU : ∀ i, MeasurableSet (U i)) (μ : ι → Measure X)
    (hc : ∀ i j, (μ i).restrict (U j) = (μ j).restrict (U i))
    (f : ℕ → ι) (hf : ⋃ n, U (f n) = univ) :
    ∃ ν : Measure X, ∀ i, ν.restrict (U i) = μ i := by
  let D := disjointed (U ∘ f)
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed (fun n => hU (f n))
  refine ⟨Measure.sum (fun n => (μ (f n)).restrict (D n)), fun i => ?_⟩
  rw [Measure.restrict_sum _ (hU i)]
  have heq : ∀ n, ((μ (f n)).restrict (D n)).restrict (U i) = (μ i).restrict (D n) := by
    intro n
    rw [Measure.restrict_comm (hU i), hc (f n) i]
    exact Measure.restrict_restrict_of_subset (disjointed_subset (U ∘ f) n)
  simp_rw [heq]
  rw [← Measure.restrict_iUnion (disjoint_disjointed (U ∘ f)) hD,
    show (⋃ n, D n) = univ from (iUnion_disjointed.trans hf), Measure.restrict_univ]

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem exists_volume (g : Metric (M := M)) : ∃ ν : Measure M, IsVolume g ν := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact ⟨0, fun x => isEmptyElim x⟩
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    exact exists_measure_of_compatible (fun x : M => (extChartAt I x).source)
      (fun x => (isOpen_extChartAt_source x).measurableSet) (localVolume g)
      (localVolume_compatible g) f (eq_univ_of_univ_subset hf)

omit [SecondCountableTopology M] in
lemma volume_on_subset [SecondCountableTopology M] (g : Metric (M := M))
    {ν : Measure M} (hν : IsVolume g ν)
    (x : M) {s : Set M} (hs : s ⊆ (extChartAt I x).source) :
    ν s = (localVolume g x) s := by
  rw [← hν x, Measure.restrict_apply' (isOpen_extChartAt_source x).measurableSet,
    inter_eq_left.mpr hs]

lemma volume_locallyFinite (g : Metric (M := M)) {ν : Measure M} (hν : IsVolume g ν) :
    IsLocallyFiniteMeasure ν := by
  constructor
  intro x
  have hx : extChartAt I x x ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source (mem_extChartAt_source x)
  obtain ⟨δ,hδ,hbound⟩ := (Metric.continuousWithinAt_iff.mp
    (chartDensity_continuousOn g x _ hx)) 1 zero_lt_one
  let V := (extChartAt I x).source ∩ extChartAt I x ⁻¹' Metric.ball (extChartAt I x x) δ
  have hVo : IsOpen V := (continuousOn_extChartAt x).isOpen_inter_preimage
    (isOpen_extChartAt_source x) Metric.isOpen_ball
  have hxV : x ∈ V := ⟨mem_extChartAt_source x, by simpa using hδ⟩
  refine ⟨V, hVo.mem_nhds hxV, ?_⟩
  rw [volume_on_subset g hν x (inter_subset_left), localVolume_apply g x hVo.measurableSet]
  let C := chartDensity g x (extChartAt I x x) + 1
  have hpre : chartPreimage x V ⊆ Metric.ball (extChartAt I x x) δ := by
    intro y hy
    have he : extChartAt I x ((extChartAt I x).symm y) = y := (extChartAt I x).right_inv hy.2
    simpa only [mem_preimage,he] using hy.1.2
  have hden : ∀ y ∈ chartPreimage x V, chartDensity g x y ≤ C := by
    intro y hy
    have hb := hbound hy.2 (hpre hy)
    rw [Real.dist_eq] at hb
    exact le_of_lt (by linarith [(abs_lt.mp hb).2])
  calc
    ∫⁻ y in chartPreimage x V, ENNReal.ofReal (chartDensity g x y) ≤
        ∫⁻ _y in chartPreimage x V, ENNReal.ofReal C :=
      setLIntegral_mono measurable_const (fun y hy => ENNReal.ofReal_le_ofReal (hden y hy))
    _ = ENNReal.ofReal C * volume (chartPreimage x V) := by simp
    _ ≤ ENNReal.ofReal C * volume (Metric.ball (extChartAt I x x) δ) :=
      mul_le_mul_right (measure_mono hpre) _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (Metric.isBounded_ball.measure_lt_top)

theorem exists_volume_locallyFinite (g : Metric (M := M)) :
    ∃ ν : Measure M, IsVolume g ν ∧ IsLocallyFiniteMeasure ν := by
  obtain ⟨ν,hν⟩ := exists_volume g
  exact ⟨ν,hν,volume_locallyFinite g hν⟩

end CKSSurfaceVolume

end

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSSurfaceVolume

lemma measure_eq_of_restrict_cover {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (hcover : ⋃ n, U n = univ) (heq : ∀ n, μ.restrict (U n) = ν.restrict (U n)) : μ = ν := by
  let D := disjointed U
  have hD : ∀ n, MeasurableSet (D n) := MeasurableSet.disjointed hU
  have hDc : ⋃ n, D n = univ := iUnion_disjointed.trans hcover
  have hrestr : ∀ n, μ.restrict (D n) = ν.restrict (D n) := by
    intro n
    rw [← Measure.restrict_restrict_of_subset (disjointed_subset U n),heq n,
      Measure.restrict_restrict_of_subset (disjointed_subset U n)]
  calc
    μ = μ.restrict (⋃ n, D n) := by rw [hDc,Measure.restrict_univ]
    _ = Measure.sum (fun n => μ.restrict (D n)) :=
      Measure.restrict_iUnion (disjoint_disjointed U) hD
    _ = Measure.sum (fun n => ν.restrict (D n)) := by simp_rw [hrestr]
    _ = ν.restrict (⋃ n, D n) := (Measure.restrict_iUnion (disjoint_disjointed U) hD).symm
    _ = ν := by rw [hDc,Measure.restrict_univ]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

omit [IsManifold I 1 M] in
lemma measure_eq_of_chart_restrict [IsManifold I 1 M] {μ ν : Measure M}
    (heq : ∀ x : M, μ.restrict (extChartAt I x).source = ν.restrict (extChartAt I x).source) :
    μ = ν := by
  cases isEmpty_or_nonempty M with
  | inl h =>
    let := h
    exact Subsingleton.elim _ _
  | inr h =>
    let := h
    obtain ⟨f,hf⟩ := isLindelof_univ.indexed_countable_subcover
      (fun x : M => (extChartAt I x).source) (fun x => isOpen_extChartAt_source x)
      (fun x _ => mem_iUnion.mpr ⟨x, mem_extChartAt_source x⟩)
    exact measure_eq_of_restrict_cover μ ν (fun n => (extChartAt I (f n)).source)
      (fun n => (isOpen_extChartAt_source (f n)).measurableSet)
      (eq_univ_of_univ_subset hf) (fun n => heq (f n))

lemma volume_unique (g : Metric (M := M)) {μ ν : Measure M}
    (hμ : IsVolume g μ) (hν : IsVolume g ν) : μ = ν :=
  measure_eq_of_chart_restrict (fun x => (hμ x).trans (hν x).symm)

lemma riemannianVolume_isVolume (g : Metric (M := M)) : IsVolume g (riemannianVolume g) :=
  Classical.epsilon_spec (exists_volume g)
instance riemannianVolume_locallyFinite (g : Metric (M := M)) :
    IsLocallyFiniteMeasure (riemannianVolume g) := volume_locallyFinite g (riemannianVolume_isVolume g)

end CKSSurfaceVolume

end

end OAI
