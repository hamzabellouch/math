import OAI.Geometry.Perimeter.Regularity.ExistsLocalVariationExtension

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem totallyBounded_range_of_uniform_approximation
    {α X : Type*} [PseudoMetricSpace X] (f : α → X) (a : ℕ → α → X)
    (ha : ∀ j, TotallyBounded (range (a j)))
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ j, ∀ x, dist (f x) (a j x) < ε) :
    TotallyBounded (range f) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨j, hj⟩ := happrox (ε / 2) (half_pos hε)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp (ha j) (ε / 2) (half_pos hε)
  refine ⟨t, ht, ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover (mem_range_self x))
  apply mem_iUnion₂.mpr
  refine ⟨y, hy, ?_⟩
  change dist (f x) y < ε
  calc
    dist (f x) y ≤ dist (f x) (a j x) + dist (a j x) y := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hj x) hxy
    _ = ε := by ring

theorem totallyBounded_toLp_of_lipschitz
    {α ι : Type*} [MetricSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : ι → α →ᵇ ℝ) (L : NNReal)
    (hf : ∀ i, LipschitzWith L (f i))
    (hrange : ∀ i x, f i x ∈ Icc (0 : ℝ) 1) :
    TotallyBounded (range (fun i ↦ BoundedContinuousFunction.toLp 1 μ ℝ (f i))) := by
  have hc : IsCompact (closure (range f)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Icc (0 : ℝ) 1) isCompact_Icc
    · rintro g x ⟨i, rfl⟩
      exact hrange i x
    · apply UniformEquicontinuous.equicontinuous
      apply LipschitzWith.uniformEquicontinuous _ L
      intro g
      obtain ⟨i, hi⟩ := g.property
      simpa only [← hi] using hf i
  have hc' := hc.image (BoundedContinuousFunction.toLp 1 μ ℝ).continuous
  apply hc'.totallyBounded.subset
  rintro _ ⟨i, rfl⟩
  exact ⟨f i, subset_closure (mem_range_self i), rfl⟩

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem isClosed_lp_ae_mem {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (s : Set ℝ) (hs : IsClosed s) :
    IsClosed {f : Lp ℝ 1 μ | ∀ᵐ x ∂μ, f x ∈ s} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨σ, hσ, hconv⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  filter_upwards [ae_all_iff.mpr hf, hconv] with x hx hc
  exact hs.mem_of_tendsto hc (Eventually.of_forall (fun j ↦ hx (σ j)))

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack
open RPI.Boundary
open scoped BoundedContinuousFunction

theorem compact_subtype_volume_finite {n : ℕ} {K : Set (Euc n)} (hK : IsCompact K) :
    IsFiniteMeasure (volume.comap (Subtype.val : K → Euc n)) := by
  constructor
  rw [(MeasurableEmbedding.subtype_coe hK.measurableSet).comap_apply]
  simpa only [Set.image_univ, Subtype.range_coe] using hK.measure_lt_top

noncomputable def compactIndicatorLp {n : ℕ} (K : Set (Euc n)) (hK : IsCompact K)
    (E : Set (Euc n)) (hE : MeasurableSet E) :
    Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n)) := by
  letI := compact_subtype_volume_finite hK
  exact ((memLp_const (1 : ℝ)).indicator (hE.preimage measurable_subtype_coe)).toLp _

theorem compactIndicatorLp_ae {n : ℕ} (K : Set (Euc n)) (hK : IsCompact K)
    (E : Set (Euc n)) (hE : MeasurableSet E) :
    compactIndicatorLp K hK E hE =ᵐ[volume.comap (Subtype.val : K → Euc n)]
      fun x : K ↦ E.indicator (fun _ ↦ (1 : ℝ)) x := by
  let := compact_subtype_volume_finite hK
  have hm : MemLp ((Subtype.val ⁻¹' E : Set K).indicator (fun _ ↦ (1 : ℝ))) 1
      (volume.comap (Subtype.val : K → Euc n)) :=
    (memLp_const (1 : ℝ)).indicator (hE.preimage measurable_subtype_coe)
  unfold compactIndicatorLp
  filter_upwards [hm.coeFn_toLp] with x hx
  change (hm.toLp _) x = _
  exact hx.trans (by rfl)

theorem compactIndicatorLp_edist_mollified_le {n : ℕ}
    (K : Set (Euc n)) (hK : IsCompact K) (E : Set (Euc n))
    (hE : MeasurableSet E) (hEK : E ⊆ K) (hP : perimeter E univ ≠ ⊤)
    (j : ℕ) (g : K →ᵇ ℝ)
    (hg : ∀ x : K, g x = c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j x) :
    letI := compact_subtype_volume_finite hK
    edist (compactIndicatorLp K hK E hE)
      (BoundedContinuousFunction.toLp 1
        (volume.comap (Subtype.val : K → Euc n)) ℝ g) ≤
      ENNReal.ofReal (c1Mollifier (n := n) j).rOut * perimeter E univ := by
  let μ : Measure K := volume.comap (Subtype.val : K → Euc n)
  let : IsFiniteMeasure μ := compact_subtype_volume_finite hK
  rw [Lp.edist_def, eLpNorm_one_eq_lintegral_enorm
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))]
  calc
    _ = ∫⁻ x : K, ‖E.indicator (fun _ ↦ (1 : ℝ)) x -
        c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j x‖ₑ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [compactIndicatorLp_ae K hK E hE,
        BoundedContinuousFunction.coeFn_toLp 1 μ ℝ g] with x hx hy
      change ‖(compactIndicatorLp K hK E hE) x -
        (BoundedContinuousFunction.toLp 1 μ ℝ g) x‖ₑ = _
      rw [hx, hy, hg x]
    _ = ∫⁻ x in K, ‖E.indicator (fun _ ↦ (1 : ℝ)) x -
        c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j x‖ₑ :=
      lintegral_subtype_comap (μ := volume) hK.measurableSet
        (fun x : Euc n ↦ ‖E.indicator (fun _ ↦ (1 : ℝ)) x -
          c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j x‖ₑ)
    _ ≤ ∫⁻ x, ‖E.indicator (fun _ ↦ (1 : ℝ)) x -
        c1Mollify (E.indicator (fun _ ↦ (1 : ℝ))) j x‖ₑ :=
      setLIntegral_le_lintegral _ _
    _ ≤ ENNReal.ofReal (c1Mollifier (n := n) j).rOut * perimeter E univ := by
      simpa only [enorm_sub_rev] using c1Mollify_indicator_lintegral_error_le hE
        (hK.isBounded.subset hEK) hP j

theorem bounded_perimeter_indicator_totallyBounded {n : ℕ}
    (K : Set (Euc n)) (hK : IsCompact K) (C : ℝ≥0∞) (hC : C ≠ ⊤) :
    TotallyBounded (range (fun E : {E : Set (Euc n) //
      MeasurableSet E ∧ E ⊆ K ∧ perimeter E univ ≤ C} ↦
        compactIndicatorLp K hK E E.property.1)) := by
  let μ : Measure K := volume.comap (Subtype.val : K → Euc n)
  let : IsFiniteMeasure μ := compact_subtype_volume_finite hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ι := {E : Set (Euc n) // MeasurableSet E ∧ E ⊆ K ∧ perimeter E univ ≤ C}
  let f : ι → Lp ℝ 1 μ := fun E ↦ compactIndicatorLp K hK E E.property.1
  have hm (E : ι) (j : ℕ) : Continuous
      (c1Mollify ((E : Set (Euc n)).indicator (fun _ ↦ (1 : ℝ))) j) := by
    obtain ⟨hi, -⟩ := indicator_one_integrable_compact E.property.1
      (hK.isBounded.subset E.property.2.1)
    exact ((c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left (n := (⊤ : ℕ∞)) _
      (c1Mollifier j).contDiff_normed hi.locallyIntegrable).continuous
  let a : ℕ → ι → K →ᵇ ℝ := fun j E ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ c1Mollify ((E : Set (Euc n)).indicator (fun _ ↦ (1 : ℝ))) j x,
      (hm E j).comp continuous_subtype_val⟩
  apply totallyBounded_range_of_uniform_approximation f
    (fun j E ↦ BoundedContinuousFunction.toLp 1 μ ℝ (a j E))
  · intro j
    obtain ⟨L, hL⟩ := c1Mollify_indicator_uniform_lipschitz K hK.isBounded j
    apply totallyBounded_toLp_of_lipschitz μ (a j) L
    · intro E
      apply LipschitzWith.of_dist_le_mul
      intro x y
      exact (hL E E.property.1 E.property.2.1).dist_le_mul x y
    · intro E x
      exact c1Mollify_indicator_mem_Icc E.property.1 j x
  · intro ε hε
    have ht : Tendsto (fun j ↦ ENNReal.ofReal (c1Mollifier (n := n) j).rOut * C)
        atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero, zero_mul] using
        ENNReal.Tendsto.mul_const
          (ENNReal.tendsto_ofReal c1Mollifier_radius_tendsto) (Or.inr hC)
    obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
    refine ⟨j, fun E ↦ edist_lt_ofReal.mp ?_⟩
    refine (compactIndicatorLp_edist_mollified_le K hK E E.property.1 E.property.2.1
      (ne_top_of_le_ne_top hC E.property.2.2) j (a j E) (fun _ ↦ rfl)).trans_lt ?_
    exact (mul_le_mul' le_rfl E.property.2.2).trans_lt hj

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack
open RPI.Boundary
open scoped BoundedContinuousFunction

theorem compactIndicatorLp_edist {n : ℕ} (K : Set (Euc n)) (hK : IsCompact K)
    (E F : Set (Euc n)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEK : E ⊆ K) (hFK : F ⊆ K) :
    edist (compactIndicatorLp K hK E hE) (compactIndicatorLp K hK F hF) =
      ∫⁻ x, ‖E.indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ := by
  let μ : Measure K := volume.comap (Subtype.val : K → Euc n)
  rw [Lp.edist_def, eLpNorm_one_eq_lintegral_enorm
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))]
  calc
    _ = ∫⁻ x : K, ‖E.indicator (fun _ ↦ (1 : ℝ)) x -
        F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [compactIndicatorLp_ae K hK E hE,
        compactIndicatorLp_ae K hK F hF] with x hx hy
      change ‖(compactIndicatorLp K hK E hE) x - (compactIndicatorLp K hK F hF) x‖ₑ = _
      rw [hx, hy]
    _ = ∫⁻ x in K, ‖E.indicator (fun _ ↦ (1 : ℝ)) x -
        F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ :=
      lintegral_subtype_comap (μ := volume) hK.measurableSet
        (fun x : Euc n ↦ ‖E.indicator (fun _ ↦ (1 : ℝ)) x -
          F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ)
    _ = _ := by
      rw [← lintegral_indicator hK.measurableSet]
      apply lintegral_congr
      intro x
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx]
      · have hxE : x ∉ E := fun h ↦ hx (hEK h)
        have hxF : x ∉ F := fun h ↦ hx (hFK h)
        simp only [indicator_of_notMem hx, indicator_of_notMem hxE,
          indicator_of_notMem hxF, sub_self, enorm_zero]

theorem exists_indicator_L1_subsequence {n : ℕ} (K : Set (Euc n)) (hK : IsCompact K)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (E : ℕ → Set (Euc n))
    (hE : ∀ i, MeasurableSet (E i)) (hEK : ∀ i, E i ⊆ K)
    (hP : ∀ i, perimeter (E i) univ ≤ C) :
    ∃ F : Set (Euc n), MeasurableSet F ∧ F ⊆ K ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun i ↦ ∫⁻ x, ‖(E (σ i)).indicator (fun _ ↦ (1 : ℝ)) x -
          F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ) atTop (𝓝 0) := by
  let μ : Measure K := volume.comap (Subtype.val : K → Euc n)
  let f : ℕ → Lp ℝ 1 μ := fun i ↦ compactIndicatorLp K hK (E i) (hE i)
  let S : Set (Lp ℝ 1 μ) := range (fun H : {H : Set (Euc n) //
    MeasurableSet H ∧ H ⊆ K ∧ perimeter H univ ≤ C} ↦
      compactIndicatorLp K hK H H.property.1)
  have hfS (i : ℕ) : f i ∈ S := ⟨⟨E i, hE i, hEK i, hP i⟩, rfl⟩
  have hc : IsCompact (closure S) :=
    (bounded_perimeter_indicator_totallyBounded K hK C hC).closure.isCompact_of_isClosed
      isClosed_closure
  obtain ⟨g, hg, σ, hσ, hconv⟩ := hc.isSeqCompact (fun i ↦ subset_closure (hfS i))
  have hclosed : IsClosed {g : Lp ℝ 1 μ | ∀ᵐ x ∂μ, g x ∈ ({0, 1} : Set ℝ)} :=
    isClosed_lp_ae_mem μ _ (isClosed_singleton.union isClosed_singleton)
  have hS01 : S ⊆ {g : Lp ℝ 1 μ | ∀ᵐ x ∂μ, g x ∈ ({0, 1} : Set ℝ)} := by
    rintro _ ⟨H, rfl⟩
    filter_upwards [compactIndicatorLp_ae K hK H H.property.1] with x hx
    rw [hx]
    by_cases hxH : (x : Euc n) ∈ (H : Set (Euc n)) <;> simp [hxH]
  have hg01 : ∀ᵐ x ∂μ, g x = 0 ∨ g x = 1 := by
    simpa only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff] using
      (closure_minimal hS01 hclosed hg)
  let A : Set K := {x | g x = 1}
  have hA : MeasurableSet A := measurableSet_eq_fun (Lp.stronglyMeasurable g).measurable measurable_const
  let F : Set (Euc n) := Subtype.val '' A
  have hF : MeasurableSet F :=
    (MeasurableEmbedding.subtype_coe hK.measurableSet).measurableSet_image.mpr hA
  have hFK : F ⊆ K := Subtype.coe_image_subset K A
  have hFg : compactIndicatorLp K hK F hF = g := by
    apply Lp.ext
    filter_upwards [compactIndicatorLp_ae K hK F hF, hg01] with x hx hx01
    rw [hx]
    by_cases hx1 : g x = 1
    · have hxF : (x : Euc n) ∈ F := ⟨x, hx1, rfl⟩
      simp only [indicator_of_mem hxF, hx1]
    · have hxF : (x : Euc n) ∉ F := by
        rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        subst y
        exact hx1 hy
      simp only [indicator_of_notMem hxF, hx01.resolve_right hx1]
  refine ⟨F, hF, hFK, σ, hσ, ?_⟩
  have ht : Tendsto (fun i ↦ edist (f (σ i)) g) atTop (𝓝 0) := by
    simpa only [Function.comp_def, edist_self] using
      hconv.edist (tendsto_const_nhds (x := g))
  rw [← hFg] at ht
  simpa only [f, compactIndicatorLp_edist K hK _ F _ hF (hEK _) hFK] using ht

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem tendsto_setIntegral_of_indicator_L1 {n : ℕ}
    (E : ℕ → Set (Euc n)) (F : Set (Euc n))
    (hE : ∀ i, MeasurableSet (E i)) (hF : MeasurableSet F)
    (hconv : Tendsto (fun i ↦ ∫⁻ x,
      ‖(E i).indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ)
      atTop (𝓝 0))
    {f : Euc n → ℝ} (hf : Integrable f volume)
    (hbound : ∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) :
    Tendsto (fun i ↦ ∫ x in E i, f x) atTop (𝓝 (∫ x in F, f x)) := by
  obtain ⟨M, hM⟩ := hbound
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  have hib (i : ℕ) :
      edist (∫ x in E i, f x) (∫ x in F, f x) ≤
      ENNReal.ofReal M * ∫⁻ x,
        ‖(E i).indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ := by
    rw [edist_eq_enorm_sub, ← integral_indicator (hE i), ← integral_indicator hF,
      ← integral_sub (hf.indicator (hE i)) (hf.indicator hF)]
    apply (enorm_integral_le_lintegral_enorm _).trans
    rw [← lintegral_const_mul' _ _]
    · apply lintegral_mono
      intro x
      have he : (E i).indicator f x - F.indicator f x =
          ((E i).indicator (fun _ ↦ (1 : ℝ)) x -
            F.indicator (fun _ ↦ (1 : ℝ)) x) * f x := by
        by_cases hx : x ∈ E i <;> by_cases hy : x ∈ F <;> simp [hx,hy]
      dsimp only
      rw [he, enorm_mul, mul_comm]
      exact mul_le_mul' (by simpa only [ofReal_norm] using
        ENNReal.ofReal_le_ofReal (hM x)) le_rfl
    · exact ENNReal.ofReal_ne_top
  apply tendsto_iff_edist_tendsto_0.mpr
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero, bot_eq_zero] using
      ENNReal.Tendsto.const_mul hconv (Or.inr ENNReal.ofReal_ne_top))
    (fun _ ↦ show (0 : ℝ≥0∞) ≤ _ from bot_le) hib

theorem perimeter_le_of_indicator_L1 {n : ℕ}
    (E : ℕ → Set (Euc n)) (F U : Set (Euc n)) (C : ℝ≥0∞)
    (hE : ∀ i, MeasurableSet (E i)) (hF : MeasurableSet F)
    (hconv : Tendsto (fun i ↦ ∫⁻ x,
      ‖(E i).indicator (fun _ ↦ (1 : ℝ)) x - F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ)
      atTop (𝓝 0))
    (hP : ∀ i, perimeter (E i) U ≤ C) : perimeter F U ≤ C := by
  rw [perimeter_eq_iSup_tests]
  apply iSup_le
  intro V
  apply iSup_le
  intro hV
  have hd := integrable_divergence hV.1 hV.2.1
  have hc : HasCompactSupport (divergence V) :=
    hV.2.1.of_isClosed_subset (isClosed_tsupport _) (tsupport_divergence_subset V)
  have ht := tendsto_setIntegral_of_indicator_L1 E F hE hF hconv hd
    (hc.exists_bound_of_continuous (continuous_divergence hV.1))
  apply le_of_tendsto (ENNReal.continuous_ofReal.tendsto _ |>.comp ht)
  filter_upwards [] with i
  have hb : ENNReal.ofReal (∫ x in E i, divergence V x) ≤ perimeter (E i) U := by
    rw [perimeter_eq_iSup_tests]
    exact le_iSup_of_le V (le_iSup_of_le hV le_rfl)
  exact hb.trans (hP i)

theorem exists_bounded_perimeter_L1_subsequence {n : ℕ}
    (K : Set (Euc n)) (hK : IsCompact K) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (E : ℕ → Set (Euc n)) (hE : ∀ i, MeasurableSet (E i))
    (hEK : ∀ i, E i ⊆ K) (hP : ∀ i, perimeter (E i) univ ≤ C) :
    ∃ F : Set (Euc n), MeasurableSet F ∧ F ⊆ K ∧ perimeter F univ ≤ C ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun i ↦ ∫⁻ x, ‖(E (σ i)).indicator (fun _ ↦ (1 : ℝ)) x -
          F.indicator (fun _ ↦ (1 : ℝ)) x‖ₑ) atTop (𝓝 0) := by
  obtain ⟨F, hF, hFK, σ, hσ, ht⟩ := exists_indicator_L1_subsequence K hK C hC E hE hEK hP
  exact ⟨F, hF, hFK, perimeter_le_of_indicator_L1 (E ∘ σ) F univ C
    (fun i ↦ hE (σ i)) hF ht (fun i ↦ hP (σ i)), σ, hσ, ht⟩

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem ae_tendsto_scaled_polar_oscillation {n k : ℕ}
    (μ : Measure (Euc n)) [IsFiniteMeasure μ] (G : Euc n → Euc n)
    (hG : Integrable G μ) {C : ℝ} (hC : 0 < C)
    (hgrowth : ∀ x (r : ℝ), 0 < r →
      μ (Metric.ball x r) ≤ ENNReal.ofReal (C * r ^ k)) :
    ∀ᵐ x ∂μ, Tendsto (fun r : ℝ ↦ (r ^ k)⁻¹ *
      ∫ y in Metric.closedBall x r, ‖G y - G x‖ ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  filter_upwards [(Besicovitch.vitaliFamily μ).ae_tendsto_average_norm_sub hG.locallyIntegrable]
    with x hx
  have ht := hx.comp (Besicovitch.tendsto_filterAt μ x)
  let A : ℝ → ℝ := fun r ↦ ⨍ y in Metric.closedBall x r, ‖G y - G x‖ ∂μ
  have ha (r : ℝ) : 0 ≤ A r := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hb : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      (r ^ k)⁻¹ * ∫ y in Metric.closedBall x r, ‖G y - G x‖ ∂μ ≤
        (C * 2 ^ k) * A r := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    change 0 < r at hr
    have hμb : μ (Metric.closedBall x r) ≤ ENNReal.ofReal (C * (2 * r) ^ k) :=
      (measure_mono (Metric.closedBall_subset_ball (by linarith))).trans
        (hgrowth x (2 * r) (by positivity))
    have hreal : μ.real (Metric.closedBall x r) ≤ C * (2 * r) ^ k := by
      simpa only [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ C * (2 * r) ^ k)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hμb
    have hi := measure_smul_setAverage (μ := μ) (fun y ↦ ‖G y - G x‖)
      (measure_ne_top μ (Metric.closedBall x r))
    simp only [smul_eq_mul] at hi
    rw [← hi]
    calc
      _ ≤ (r ^ k)⁻¹ * ((C * (2 * r) ^ k) * A r) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hreal (ha r))
          (by positivity)
      _ = _ := by rw [mul_pow]; field_simp [hr.ne']
  have hnonneg : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 ≤ (r ^ k)⁻¹ *
      ∫ y in Metric.closedBall x r, ‖G y - G x‖ ∂μ := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (le_of_lt hr) k))
      (integral_nonneg fun _ ↦ norm_nonneg _)
  refine squeeze_zero' hnonneg hb ?_
  simpa only [mul_zero, Function.comp_def, A] using ht.const_mul (C * 2 ^ k)

theorem exists_differentiating_unit_polar {n : ℕ} (hn : 0 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (U : Set (Euc n)) (hU : IsOpen U) (hP : perimeter E U ≠ ⊤) :
    ∃ G : Euc n → Euc n,
      StronglyMeasurable G ∧ MemLp G 2 ((perimeterMeasure E).restrict U) ∧
      (∀ᵐ x ∂(perimeterMeasure E).restrict U, ‖G x‖ = 1) ∧
      (∀ᵐ x ∂(perimeterMeasure E).restrict U,
        Tendsto (fun r : ℝ ↦ (r ^ (n - 1))⁻¹ * ∫ y in Metric.closedBall x r,
          ‖G y - G x‖ ∂(perimeterMeasure E).restrict U) (𝓝[>] (0 : ℝ)) (𝓝 0)) ∧
      ∀ V : Euc n → Euc n, ContDiff ℝ ∞ V → HasCompactSupport V → tsupport V ⊆ U →
        (∫ x in E, divergence V x) = ∫ x in U, inner ℝ (G x) (V x) ∂perimeterMeasure E := by
  let μ := (perimeterMeasure E).restrict U
  let : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E hU]; exact hP.lt_top⟩
  obtain ⟨G, hG, hGp, hGn, hrep⟩ := exists_local_unit_variation_polar E U hU hP
  obtain ⟨C, hC, hgrowth⟩ := exists_locallyMinimizing_perimeter_growth_constant n hn
  have hlocal : ∀ x (r : ℝ), 0 < r → μ (Metric.ball x r) ≤
      ENNReal.ofReal (C * r ^ (n - 1)) := by
    intro x r hr
    exact ((Measure.restrict_le_self (μ := perimeterMeasure E) (s := U)) _).trans
      (by simpa only [perimeterMeasure_open E Metric.isOpen_ball] using hgrowth E hmin x r hr)
  exact ⟨G, hG, hGp, hGn,
    ae_tendsto_scaled_polar_oscillation μ G (MemLp.integrable (by norm_num) hGp) hC hlocal,
    hrep⟩

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem ae_inner_ne_value {n : ℕ} {v : Euc n} (hv : ‖v‖ = 1) (t : ℝ) :
    ∀ᵐ x ∂(volume : Measure (Euc n)), inner ℝ x v ≠ t := by
  let L : Euc n →L[ℝ] ℝ := innerSL ℝ v
  have hLv : L v = 1 := by simp [L, hv]
  have hL : L ≠ 0 := by intro hz; simp [hz] at hLv
  have hk : L.ker ≠ ⊤ := by
    intro hk
    apply hL
    ext z
    have hz : z ∈ L.ker := hk ▸ Submodule.mem_top
    exact hz
  have hn : (volume : Measure (Euc n)) {z | L z = 0} = 0 :=
    Measure.addHaar_submodule (volume : Measure (Euc n)) L.ker hk
  have ha : ∀ᵐ z ∂(volume : Measure (Euc n)), L z ≠ 0 := by
    simpa only [ae_iff, not_not] using hn
  have ht := (measurePreserving_add_right (volume : Measure (Euc n)) (-t • v)).quasiMeasurePreserving.ae ha
  filter_upwards [ht] with x hx
  change L (x + -t • v) ≠ 0 at hx
  simp only [map_add, map_smul, hLv, smul_eq_mul, mul_one] at hx
  intro heq
  apply hx
  change inner ℝ v x + -t = 0
  rw [real_inner_comm, heq]
  ring

theorem ordered_indicator_halfspace {n : ℕ} (E S : Set (Euc n))
    (hS : ∀ᵐ x ∂(volume : Measure (Euc n)), x ∈ S)
    {v : Euc n} (hv : ‖v‖ = 1) {R : ℝ} (hR : 0 < R)
    (horder : ∀ x ∈ S ∩ Metric.ball (0 : Euc n) R,
      ∀ y ∈ S ∩ Metric.ball (0 : Euc n) R,
        inner ℝ x v < inner ℝ y v → y ∈ E → x ∈ E) :
    ∃ t ∈ Icc (-R) R, ∀ᵐ x ∂volume.restrict (Metric.ball (0 : Euc n) R),
      x ∈ E ↔ inner ℝ x v < t := by
  let A : Set ℝ := (fun x : Euc n ↦ inner ℝ x v) '' (E ∩ S ∩ Metric.ball 0 R)
  have hb (x : Euc n) (hx : x ∈ Metric.ball (0 : Euc n) R) :
      -R < inner ℝ x v ∧ inner ℝ x v < R := by
    apply abs_lt.mp
    apply (abs_real_inner_le_norm x v).trans_lt
    simpa only [hv, mul_one, Metric.mem_ball, dist_zero_right] using hx
  have hbA : ∀ a ∈ A, -R < a ∧ a < R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hb x hx.2
  by_cases hA : A.Nonempty
  · have hAb : BddAbove A := ⟨R, fun a ha ↦ (hbA a ha).2.le⟩
    let t := sSup A
    have htl : -R ≤ t := by
      obtain ⟨a, ha⟩ := hA
      exact (hbA a ha).1.le.trans (le_csSup hAb ha)
    have htu : t ≤ R := csSup_le hA (fun a ha ↦ (hbA a ha).2.le)
    refine ⟨t, ⟨htl, htu⟩, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball,
      hS.filter_mono (ae_mono Measure.restrict_le_self),
      (ae_inner_ne_value hv t).filter_mono (ae_mono Measure.restrict_le_self)] with x hx hxS hxne
    constructor
    · intro hxE
      have ha : inner ℝ x v ∈ A := ⟨x, ⟨⟨hxE, hxS⟩, hx⟩, rfl⟩
      exact (le_csSup hAb ha).lt_of_ne hxne
    · intro hxt
      obtain ⟨a, ha, hxa⟩ := exists_lt_of_lt_csSup hA hxt
      obtain ⟨y, hy, rfl⟩ := ha
      exact horder x ⟨hxS, hx⟩ y ⟨hy.1.2, hy.2⟩ hxa hy.1.1
  · refine ⟨-R, ⟨le_rfl, by linarith⟩, ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_ball,
      hS.filter_mono (ae_mono Measure.restrict_le_self)] with x hx hxS
    have hxE : x ∉ E := by
      intro hxE
      exact hA ⟨inner ℝ x v, x, ⟨⟨hxE, hxS⟩, hx⟩, rfl⟩
    simp only [hxE, false_iff]
    exact not_lt.mpr (hb x hx).1.le

end RPISingularHarnack

end

end OAI
