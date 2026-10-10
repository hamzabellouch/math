import Mathlib
import OAI.Geometry.SmoothYau.Estimates.SphericalPinFormNorm

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
section IntrinsicForwardLipschitz
variable {E M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) 1 M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

private local instance intrinsicForwardMapNorm (x : M) (y : F) :
    NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] TangentSpace 𝓘(ℝ,F) y) :=
  inferInstanceAs (NormedAddCommGroup (TangentSpace 𝓘(ℝ,E) x →L[ℝ] F))

omit [IsManifold 𝓘(ℝ,E) 1 M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma map_edist_le_pathELength {f : M → F}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f) {C : ℝ≥0}
    (hC : ∀ x, ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x‖ₑ ≤ C)
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ,ℝ) 𝓘(ℝ,E) 1 γ (Icc 0 1)) :
    edist (f (γ 0)) (f (γ 1)) ≤ C*pathELength 𝓘(ℝ,E) γ 0 1 := by
  let η := f ∘ γ
  have hη : ContDiffOn ℝ 1 η (Icc 0 1) := by
    rw [←contMDiffOn_iff_contDiffOn]
    exact hf.comp_contMDiffOn hγ
  calc
    _ = ‖η 1-η 0‖ₑ := by rw [edist_comm,edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hη zero_le_one
    _ = ∫⁻ t in Icc (0:ℝ) 1, ‖mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,F) η (Icc 0 1) t 1‖ₑ := by
      simp_rw [←fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t in Icc (0:ℝ) 1, C*‖mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ (Icc 0 1) t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hc : mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,F) η (Icc 0 1) t =
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f (γ t)).comp
            (mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ (Icc 0 1) t) := by
        apply mfderiv_comp_mfderivWithin
        · exact (hf.mdifferentiable one_ne_zero) (γ t)
        · exact hγ.mdifferentiableOn one_ne_zero t ht
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht
      have hc' : mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,F) η (Icc 0 1) t 1 =
          (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f (γ t))
            (mfderivWithin 𝓘(ℝ,ℝ) 𝓘(ℝ,E) γ (Icc 0 1) t 1) := congr($hc 1)
      rw [hc']
      apply (ContinuousLinearMap.le_opENorm _ _).trans
      gcongr
      exact hC (γ t)
    _ = _ := by rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
      pathELength_eq_lintegral_mfderivWithin_Icc]

omit [IsManifold 𝓘(ℝ,E) 1 M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
theorem map_edist_le_riemannianEDist {f : M → F}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f) {C : ℝ≥0} (hCpos : 0 < C)
    (hC : ∀ x, ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x‖ₑ ≤ C) (x y : M) :
    edist (f x) (f y) ≤ C*riemannianEDist 𝓘(ℝ,E) x y := by
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by exact_mod_cast hCpos.ne'
  have hd : edist (f x) (f y)/(C : ℝ≥0∞) ≤ riemannianEDist 𝓘(ℝ,E) x y := by
    apply le_of_forall_gt
    intro r hr
    obtain ⟨γ,hγ0,hγ1,hγ,hγr⟩ := exists_lt_of_riemannianEDist_lt hr
    have he := map_edist_le_pathELength hf hC hγ
    rw [hγ0,hγ1,mul_comm] at he
    exact ((ENNReal.div_le_iff hC0 ENNReal.coe_ne_top).mpr he).trans_lt hγr
  simpa only [mul_comm] using (ENNReal.div_le_iff hC0 ENNReal.coe_ne_top).mp hd

lemma eventually_norm_mfderiv_lt {f : M → F}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f) (x : M) :
    ∃ C > (0 : ℝ), ∀ᶠ y in 𝓝 x, ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y‖ < C := by
  let c := chartAt E x
  let φ := f ∘ c.symm
  have hφ (y : E) (hy : y ∈ c.target) : ContDiffAt ℝ 1 φ y := by
    rw [←contMDiffAt_iff_contDiffAt]
    exact (hf (c.symm y)).comp y (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas x) hy)
  have hcx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  obtain ⟨C,hC,hCloc⟩ := eventually_norm_mfderiv_extChartAt_lt 𝓘(ℝ,E) x
  have hD : ContinuousAt (fun y => ‖fderiv ℝ φ (c y)‖) x :=
    ((hφ (c x) hcx).continuousAt_fderiv one_ne_zero).norm.comp
      (c.continuousAt (mem_chart_source E x))
  have hDloc : ∀ᶠ y in 𝓝 x, ‖fderiv ℝ φ (c y)‖ < ‖fderiv ℝ φ (c x)‖+1 :=
    hD (Iio_mem_nhds (lt_add_one _))
  refine ⟨(‖fderiv ℝ φ (c x)‖+1)*C, by positivity, ?_⟩
  filter_upwards [hCloc,hDloc,chart_source_mem_nhds E x] with y hCy hDy hy
  have he : f =ᶠ[𝓝 y] φ ∘ c := by
    filter_upwards [(chartAt E x).open_source.mem_nhds hy] with z hz
    simp only [φ,Function.comp_apply,c.left_inv hz]
  have hd : mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y =
      (fderiv ℝ φ (c y)).comp (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c y) := by
    rw [he.mfderiv_eq]
    rw [mfderiv_comp y ((hφ (c y) (c.map_source hy)).differentiableAt one_ne_zero).mdifferentiableAt
      (mdifferentiableAt_extChartAt hy)]
    rw [mfderiv_eq_fderiv]
    rfl
  rw [hd]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans_lt
  exact (mul_le_mul_of_nonneg_left hCy.le (norm_nonneg _)).trans_lt
    (mul_lt_mul_of_pos_right hDy hC)

lemma exists_global_mfderiv_bound [CompactSpace M] {f : M → F}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x, ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f x‖ₑ ≤ C := by
  classical
  choose C hC hnear using eventually_norm_mfderiv_lt hf
  obtain ⟨t,_,ht⟩ := isCompact_univ.elim_nhds_subcover
    (fun x => {y | ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y‖ < C x}) (fun x _ => hnear x)
  let B := 1+∑ x ∈ t, C x
  have hB : 0 < B := by
    dsimp [B]
    have := Finset.sum_nonneg (s:=t) (fun x _ => (hC x).le)
    linarith
  refine ⟨⟨B,hB.le⟩,hB,?_⟩
  intro y
  obtain ⟨x,hxt,hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  have hle : ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y‖ ≤ B := by
    have hc := Finset.single_le_sum (f:=C) (fun z _ => (hC z).le) hxt
    change ‖mfderiv 𝓘(ℝ,E) 𝓘(ℝ,F) f y‖ < C x at hy
    dsimp [B]
    linarith
  exact enorm_le_coe.mpr hle

theorem compact_map_riemannian_lipschitz [CompactSpace M] {f : M → F}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) 1 f) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x y, edist (f x) (f y) ≤ C*riemannianEDist 𝓘(ℝ,E) x y := by
  obtain ⟨C,hC,hbound⟩ := exists_global_mfderiv_bound hf
  exact ⟨C,hC,map_edist_le_riemannianEDist hf hC hbound⟩

end IntrinsicForwardLipschitz
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M] [CompactSpace M] [T2Space M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

omit [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x)] in
lemma exists_smooth_chart_extension (p : M) {K : Set M} (hK : IsCompact K)
    (hKc : K ⊆ (chartAt E p).source) :
    ∃ f : M → E, ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ f ∧ EqOn f (chartAt E p) K := by
  let c := chartAt E p
  have hd : Disjoint c.sourceᶜ K := by
    rw [disjoint_left]
    exact fun x hx hxK => hx (hKc hxK)
  obtain ⟨ψ,hzero,hone,_⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ,E) c.open_source.isClosed_compl hK.isClosed hd (n:=(⊤ : ℕ∞))
  have hsupport : tsupport (fun x => ψ x) ⊆ c.source := by
    intro x hx
    by_contra hn
    have he : (fun y => ψ y) =ᶠ[𝓝 x] 0 := hzero.filter_mono (nhds_le_nhdsSet hn)
    exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx
  refine ⟨fun x => ψ x • c x, ?_, ?_⟩
  · apply contMDiff_of_tsupport
    intro x hx
    have hxc : x ∈ c.source := hsupport (tsupport_smul_subset_left _ _ hx)
    exact ψ.contMDiff.contMDiffAt.smul
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas p) hxc)
  · intro x hx
    change ψ x • c x = c x
    rw [hone.self_of_nhdsSet x hx, one_smul]

theorem compact_chart_riemannian_lipschitz (p : M) {K : Set M} (hK : IsCompact K)
    (hKc : K ⊆ (chartAt E p).source) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ x ∈ K, ∀ y ∈ K,
      edist (chartAt E p x) (chartAt E p y) ≤ C*riemannianEDist 𝓘(ℝ,E) x y := by
  obtain ⟨f,hf,hfc⟩ := exists_smooth_chart_extension p hK hKc
  obtain ⟨C,hC,hbound⟩ := compact_map_riemannian_lipschitz (hf.of_le (by simp))
  refine ⟨C,hC,?_⟩
  intro x hx y hy
  simpa only [hfc hx,hfc hy] using hbound x y

theorem compact_chart_hausdorff_comparison
    [MeasurableSpace E] [BorelSpace E]
    (p : M) {K : Set M} (hK : IsCompact K) (hKc : K ⊆ (chartAt E p).source) :
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ,E) M
    letI : MeasurableSpace M := borel M
    letI : BorelSpace M := ⟨rfl⟩
    ∃ C : ℝ≥0, 0 < C ∧ ∀ S ⊆ K, ∀ d : ℝ, 0 ≤ d →
      Measure.hausdorffMeasure d (chartAt E p '' S) ≤
        (C : ℝ≥0∞)^d * Measure.hausdorffMeasure d S := by
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ,E) M
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨C,hC,hbound⟩ := compact_chart_riemannian_lipschitz p hK hKc
  refine ⟨C,hC,?_⟩
  intro S hSK d hd
  have hlip : LipschitzOnWith C (chartAt E p) S := by
    intro x hx y hy
    exact hbound x (hSK hx) y (hSK hy)
  exact hlip.hausdorffMeasure_image_le hd


end

section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff NNReal ENNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [CompactSpace M] [T2Space M]

theorem nodalMeasure_chart_lower_bound (g : SmoothMetric E M)
    (p : M) {K : Set M} (hK : IsCompact K) (hKc : K ⊆ (chartAt E p).source) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ u : M → ℝ, ∀ d : ℝ, 0 ≤ d →
      Measure.hausdorffMeasure d (chartAt E p '' (K ∩ {x | u x = 0})) ≤
        (C : ℝ≥0∞)^d * nodalMeasure g d u := by
  let : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace 𝓘(ℝ,E) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric 𝓘(ℝ,E) M
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨C,hC,hbound⟩ := compact_chart_hausdorff_comparison p hK hKc
  refine ⟨C,hC,?_⟩
  intro u d hd
  change Measure.hausdorffMeasure d (chartAt E p '' (K ∩ {x | u x = 0})) ≤
    (C : ℝ≥0∞)^d * Measure.hausdorffMeasure d {x | u x = 0}
  exact (hbound (K ∩ {x | u x = 0}) inter_subset_left d hd).trans
    (mul_le_mul' le_rfl (measure_mono inter_subset_right))

theorem nodalMeasure_coordinates_lower_bound (g : SmoothMetric E M)
    (p : M) {K : Set E} (hK : IsCompact K) (hKc : K ⊆ (chartAt E p).target) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ u : M → ℝ, ∀ d : ℝ, 0 ≤ d →
      Measure.hausdorffMeasure d (K ∩ {y | u ((chartAt E p).symm y) = 0}) ≤
        (C : ℝ≥0∞)^d * nodalMeasure g d u := by
  let c := chartAt E p
  have hL : IsCompact (c.symm '' K) :=
    hK.image_of_continuousOn (c.continuousOn_symm.mono hKc)
  have hLc : c.symm '' K ⊆ c.source := by
    rintro x ⟨y,hy,rfl⟩
    exact c.map_target (hKc hy)
  obtain ⟨C,hC,hbound⟩ := nodalMeasure_chart_lower_bound g p hL hLc
  refine ⟨C,hC,?_⟩
  intro u d hd
  have he : c '' ((c.symm '' K) ∩ {x | u x = 0}) =
      K ∩ {y | u (c.symm y) = 0} := by
    ext y
    constructor
    · rintro ⟨x,⟨⟨z,hz,hzx⟩,hx⟩,hxy⟩
      have hzy : z = y := by
        rw [←hzx,c.right_inv (hKc hz)] at hxy
        exact hxy
      refine ⟨hzy ▸ hz, ?_⟩
      change u (c.symm y) = 0
      rw [←hzy,hzx]
      exact hx
    · rintro ⟨hy,hu⟩
      exact ⟨c.symm y,⟨⟨y,hy,rfl⟩,hu⟩,c.right_inv (hKc hy)⟩
  rw [←he]
  exact hbound u d hd


end


open Set Filter Function Manifold Bundle TopologicalSpace BoxIntegral MeasureTheory
open scoped Topology ContDiff Distributions ENNReal NNReal
lemma spherical_nodal_finite (g : SmoothMetric (Euclidean 3) (Sphere 3))
    (u : Sphere 3 → ℝ) (hu : ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u)
    (hreg : SphericalRegular u) : nodalMeasure g 2 u ≠ (∞ : ℝ≥0∞) := by
  let : RiemannianBundle (fun x : Sphere 3 => TangentSpace 𝓘(ℝ,Euclidean 3) x) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (Euclidean 3) (fun x : Sphere 3 => TangentSpace 𝓘(ℝ,Euclidean 3) x) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  let : EMetricSpace (Sphere 3) := EMetricSpace.ofRiemannianMetric 𝓘(ℝ,Euclidean 3) (Sphere 3)
  let : MeasurableSpace (Sphere 3) := borel (Sphere 3)
  let : BorelSpace (Sphere 3) := ⟨rfl⟩
  have hh := compact_regular_level_intrinsic_finite hu (K:=univ) isCompact_univ (fun x _ => hreg x)
  change Measure.hausdorffMeasure 2 {x | u x=0}≠(∞ : ℝ≥0∞)
  apply ne_of_lt
  simpa [Euclidean] using hh

lemma spherical_signCertificate_bound (g : SmoothMetric (Euclidean 3) (Sphere 3)) :
    ∃ D : ℝ≥0, 0<D ∧ ∀ (u : Sphere 3 → ℝ),
      Continuous u → ∀ (partition : TaggedPrepartition sourceSignBox)
      (d : {J : Box (Fin 3) // J∈partition.boxes} → ℝ), (∀ j, 0<d j) →
      SignTests.signCertificate (fun j => Box.Ioo j.val) d
        ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv) ≤
          (D:ℝ≥0∞)*nodalMeasure g 2 u := by
  classical
  let K : Set (Euclidean 3) := normalWaveEquiv '' Box.Icc sourceSignBox
  have hK : IsCompact K := sourceSignBox.isCompact_Icc.image normalWaveEquiv.continuous
  obtain ⟨C,hC,hCbound⟩ := nodalMeasure_coordinates_lower_bound g sourcePole hK
    (by rw [sphere_chart_target]; exact subset_univ _)
  let L : ℝ≥0 := max ‖normalWaveEquiv.symm.toContinuousLinearMap‖₊ 1
  have hL : 0<L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlip : LipschitzWith L normalWaveEquiv.symm :=
    normalWaveEquiv.symm.toContinuousLinearMap.lipschitzWith.weaken (le_max_left _ _)
  refine ⟨36*L^2*(C:ℝ≥0)^2,by positivity,?_⟩
  intro u hu partition d hd
  let f := ((u ∘ (chartAt (Euclidean 3) sourcePole).symm) ∘ normalWaveEquiv)
  have hf : Continuous f := hu.comp ((sphere_chart_symm_continuous sourcePole).comp normalWaveEquiv.continuous)
  let Z := (⋃ j : {J : Box (Fin 3) // J∈partition.boxes}, Box.Ioo j.val) ∩ {z | f z=0}
  have hsign : SignTests.signCertificate (fun j => Box.Ioo j.val) d f ≤
      36*Measure.hausdorffMeasure 2 Z := by
    have hh := SignTests.signCertificate_le_hausdorff_on_union
      (fun j : {J : Box (Fin 3) // J∈partition.boxes} => Box.Ioo j.val) d hd
      (fun j => isOpen_set_pi finite_univ (fun _ _ => isOpen_Ioo))
      (fun j => convex_pi (fun i _ => convex_Ioo _ _))
      (fun j k hjk => (partition.toPrepartition.disjoint_coe_of_mem j.property k.property
        (fun hh => hjk (Subtype.ext hh))).mono j.val.Ioo_subset_coe k.val.Ioo_subset_coe)
      f hf.continuousOn
    norm_num [Z] at hh ⊢
    exact hh
  have hZsub : Z ⊆ normalWaveEquiv.symm '' (K ∩ {y | u ((chartAt (Euclidean 3) sourcePole).symm y)=0}) := by
    rintro x ⟨hx,hfx⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    refine ⟨normalWaveEquiv x,⟨⟨x,?_,rfl⟩,hfx⟩,normalWaveEquiv.symm_apply_apply x⟩
    exact Box.coe_subset_Icc (partition.toPrepartition.le_of_mem j.property (j.val.Ioo_subset_coe hj))
  have hmeasure : Measure.hausdorffMeasure 2 Z ≤ (L:ℝ≥0∞)^2*(C:ℝ≥0∞)^2*nodalMeasure g 2 u := by
    calc
      _ ≤ Measure.hausdorffMeasure 2 (normalWaveEquiv.symm ''
        (K ∩ {y | u ((chartAt (Euclidean 3) sourcePole).symm y)=0})) := measure_mono hZsub
      _ ≤ (L:ℝ≥0∞)^(2:ℝ)*Measure.hausdorffMeasure 2
        (K ∩ {y | u ((chartAt (Euclidean 3) sourcePole).symm y)=0}) :=
          hlip.hausdorffMeasure_image_le (by norm_num : (0:ℝ)≤2) _
      _ ≤ (L:ℝ≥0∞)^(2:ℝ)*((C:ℝ≥0∞)^(2:ℝ)*nodalMeasure g 2 u) :=
          mul_le_mul' le_rfl (hCbound u 2 (by norm_num))
      _ = _ := by rw [ENNReal.rpow_two,ENNReal.rpow_two,mul_assoc]
  apply hsign.trans
  calc
    _ ≤ 36*((L:ℝ≥0∞)^2*(C:ℝ≥0∞)^2*nodalMeasure g 2 u) := mul_le_mul' le_rfl hmeasure
    _ = _ := by simp only [ENNReal.coe_mul,ENNReal.coe_pow,ENNReal.coe_ofNat]; ring

lemma spherical_sign_nodal_real (g : SmoothMetric (Euclidean 3) (Sphere 3)) :
    ∃ D : ℝ, 0<D ∧ ∀ (u : Sphere 3 → ℝ),
      ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ u → SphericalRegular u →
      ∀ L : ℝ, 0≤L → SphericalSignAbove u L → L < D*(nodalMeasure g 2 u).toReal := by
  obtain ⟨D,hD,hbound⟩ := spherical_signCertificate_bound g
  refine ⟨D,hD,?_⟩
  intro u hu hr L hL hs
  obtain ⟨partition,_,d,hd,hscore⟩ := hs
  have hh := hscore.trans_le (hbound u hu.continuous partition d hd)
  have hfin := spherical_nodal_finite g u hu hr
  have hr := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)).mpr hh
  simpa only [ENNReal.toReal_ofReal hL,ENNReal.toReal_mul,ENNReal.coe_toReal] using hr

end YauCounterexamples
end

end OAI
