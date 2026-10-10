import OAI.Geometry.Perimeter.Regularity.GeoAlgebra

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Convolution BoundedContinuousFunction
namespace RPISingularHarnack
open RPI.Boundary ContinuousLinearMap

theorem c1Mollify_lintegral_error_of_translation {n : ℕ} {f : Euc n → ℝ}
    (hf : Measurable f) (hi : Integrable f volume) (D : ℝ≥0∞)
    (ht : ∀ w : Euc n, (∫⁻ x, ‖f (x+w)-f x‖ₑ) ≤ ‖w‖ₑ * D) (j : ℕ) :
    (∫⁻ x, ‖c1Mollify f j x-f x‖ₑ) ≤
      ENNReal.ofReal (c1Mollifier (n := n) j).rOut * D := by
  let k : Euc n → ℝ := (c1Mollifier j).normed volume
  have hkc : Continuous k := (c1Mollifier j).continuous_normed
  have hk : Integrable k volume := hkc.integrable_of_hasCompactSupport
    (c1Mollifier j).hasCompactSupport_normed
  have hk1 : ∫ x, k x = 1 := (c1Mollifier j).integral_normed
  obtain ⟨B,hB⟩ := ((c1Mollifier (n := n) j).hasCompactSupport_normed (μ := volume)).exists_bound_of_continuous hkc
  have hp (x : Euc n) : ‖c1Mollify f j x-f x‖ₑ ≤
      ∫⁻ y, ‖k y‖ₑ * ‖f (x-y)-f x‖ₑ := by
    have hif : Integrable (fun y ↦ f (x-y)) volume :=
      hi.comp_sub_left x
    have hib : Integrable (fun y ↦ k y * f (x-y)) volume := by
      apply (hif.norm.const_mul B).mono'
      · exact (hkc.measurable.mul (hf.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
      · exact ae_of_all _ fun y ↦ by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _)
    have he : c1Mollify f j x-f x = ∫ y, k y * (f (x-y)-f x) := by
      simp only [c1Mollify, convolution_def, lsmul_apply, smul_eq_mul]
      simp_rw [mul_sub]
      rw [integral_sub hib (hk.mul_const _), integral_mul_const, hk1, one_mul]
    rw [he]
    apply (enorm_integral_le_lintegral_enorm _).trans_eq
    exact lintegral_congr (fun _ ↦ enorm_mul _ _)
  have hm : Measurable (fun p : Euc n × Euc n ↦
      ‖k p.2‖ₑ * ‖f (p.1-p.2)-f p.1‖ₑ) :=
    (hkc.measurable.comp measurable_snd).enorm.mul
      ((hf.comp (measurable_fst.sub measurable_snd)).sub (hf.comp measurable_fst)).enorm
  calc
    _ ≤ ∫⁻ x, ∫⁻ y, ‖k y‖ₑ * ‖f (x-y)-f x‖ₑ := lintegral_mono hp
    _ = ∫⁻ y, ∫⁻ x, ‖k y‖ₑ * ‖f (x-y)-f x‖ₑ := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ y, ‖k y‖ₑ * ∫⁻ x, ‖f (x-y)-f x‖ₑ := by
      apply lintegral_congr
      intro y
      exact lintegral_const_mul _ ((hf.comp (measurable_id.sub measurable_const)).sub hf).enorm
    _ ≤ ∫⁻ y, ‖k y‖ₑ * (‖y‖ₑ * D) := by
      apply lintegral_mono
      intro y
      exact mul_le_mul_right (by simpa only [sub_eq_add_neg, enorm_neg] using ht (-y)) _
    _ ≤ ∫⁻ y, ‖k y‖ₑ * (ENNReal.ofReal (c1Mollifier (n := n) j).rOut * D) := by
      apply lintegral_mono
      intro y
      by_cases hy : k y = 0
      · simp only [hy, enorm_zero, zero_mul, le_refl]
      · have hys : y ∈ Function.support k := hy
        rw [(c1Mollifier j).support_normed_eq] at hys
        have hyb : ‖y‖ₑ ≤ ENNReal.ofReal (c1Mollifier (n := n) j).rOut := by
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by
            have hylt : ‖y‖ < (c1Mollifier (n := n) j).rOut := by
              simpa only [Metric.mem_ball, dist_zero_right] using hys
            exact hylt.le)
        exact mul_le_mul_right (mul_le_mul_left hyb _) _
    _ = _ := by
      rw [lintegral_mul_const _ hkc.measurable.enorm]
      have hki : (∫⁻ y, ‖k y‖ₑ) = 1 := by
        have heq : ∀ y, ‖k y‖ₑ = ENNReal.ofReal (k y) := by
          intro y
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ((c1Mollifier j).nonneg_normed y)]
        simp_rw [heq]
        rw [← ofReal_integral_eq_lintegral_ofReal hk (ae_of_all _ (c1Mollifier j).nonneg_normed), hk1, ENNReal.ofReal_one]
      rw [hki, one_mul]

theorem c1Mollify_uniform_bounds_of_integral_norm {n : ℕ} (A : ℝ) (hA : 0 ≤ A)
    (j : ℕ) : ∃ L : ℝ≥0, ∃ B : ℝ, ∀ f : Euc n → ℝ,
      Measurable f → Integrable f volume → (∫ x, ‖f x‖) ≤ A →
      LipschitzWith L (c1Mollify f j) ∧ ∀ x, ‖c1Mollify f j x‖ ≤ B := by
  let k : Euc n → ℝ := (c1Mollifier j).normed volume
  have hc : HasCompactSupport k := (c1Mollifier j).hasCompactSupport_normed
  have hk : ContDiff ℝ ∞ k := (c1Mollifier j).contDiff_normed
  obtain ⟨C,hC⟩ := hk.lipschitzWith_of_hasCompactSupport hc (by simp)
  obtain ⟨B,hB⟩ := hc.exists_bound_of_continuous hk.continuous
  have hB0 : 0 ≤ B := (norm_nonneg (k 0)).trans (hB 0)
  refine ⟨C * ⟨A,hA⟩, B*A, ?_⟩
  intro f hf hi hbound
  have hflip : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip = lsmul ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm b a
  have he : c1Mollify f j = f ⋆[lsmul ℝ ℝ,volume] k := by
    change k ⋆[lsmul ℝ ℝ,volume] f = _
    rw [← convolution_flip,hflip]
  have hib (x : Euc n) : Integrable (fun z ↦ f z*k (x-z)) volume := by
    apply (hi.norm.mul_const B).mono'
    · exact (hf.mul (hk.continuous.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    · exact ae_of_all _ fun z ↦ by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm,he]
    change ‖(∫ z, f z*k (x-z))-(∫ z, f z*k (y-z))‖ ≤ _
    rw [← integral_sub (hib x) (hib y)]
    calc
      _ ≤ ∫ z, ‖f z*k (x-z)-f z*k (y-z)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, ‖f z‖*((C:ℝ)*dist x y) := by
        apply integral_mono ((hib x).sub (hib y)).norm (hi.norm.mul_const _)
        intro z
        change ‖f z*k (x-z)-f z*k (y-z)‖ ≤ ‖f z‖*((C:ℝ)*dist x y)
        rw [← mul_sub,norm_mul]
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        simpa only [← dist_eq_norm,dist_sub_right] using hC.dist_le_mul (x-z) (y-z)
      _ = (∫ z, ‖f z‖)*((C:ℝ)*dist x y) := integral_mul_const _ _
      _ ≤ A*((C:ℝ)*dist x y) := mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = _ := by change A*((C:ℝ)*dist x y) = ((C:ℝ)*A)*dist x y; ring
  · intro x
    rw [he]
    change ‖∫ z, f z*k (x-z)‖ ≤ _
    calc
      _ ≤ ∫ z, ‖f z*k (x-z)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, ‖f z‖*B := by
        apply integral_mono (hib x).norm (hi.norm.mul_const B)
        intro z
        change ‖f z*k (x-z)‖ ≤ ‖f z‖*B
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
      _ = (∫ z, ‖f z‖)*B := integral_mul_const _ _
      _ ≤ A*B := mul_le_mul_of_nonneg_right hbound hB0
      _ = B*A := mul_comm _ _

theorem totallyBounded_toLp_of_lipschitz_norm
    {α ι : Type*} [MetricSpace α] [CompactSpace α]
    [MeasurableSpace α] [BorelSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : ι → α →ᵇ ℝ) (L : NNReal) (B : ℝ)
    (hf : ∀ i, LipschitzWith L (f i)) (hb : ∀ i x, ‖f i x‖ ≤ B) :
    TotallyBounded (range (fun i ↦ BoundedContinuousFunction.toLp 1 μ ℝ (f i))) := by
  have hc : IsCompact (closure (range f)) := by
    apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0:ℝ) B)
      (isCompact_closedBall _ _)
    · rintro g x ⟨i,rfl⟩
      simpa only [Metric.mem_closedBall,dist_zero_right] using hb i x
    · apply UniformEquicontinuous.equicontinuous
      apply LipschitzWith.uniformEquicontinuous _ L
      intro g
      obtain ⟨i,hi⟩ := g.property
      simpa only [← hi] using hf i
  exact (hc.image (BoundedContinuousFunction.toLp 1 μ ℝ).continuous).totallyBounded.subset
    (by rintro _ ⟨i,rfl⟩; exact ⟨f i,subset_closure (mem_range_self i),rfl⟩)

noncomputable def compactFunctionLp {n : ℕ} (K : Set (Euc n)) (hK : IsCompact K)
    (f : Euc n → ℝ) (hi : Integrable f volume) :
    Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n)) :=
  (memLp_one_iff_integrable.mpr ((integrableOn_iff_comap_subtypeVal hK.measurableSet).mp hi.integrableOn)).toLp _

theorem compactFunctionLp_ae {n : ℕ} (K : Set (Euc n)) (hK : IsCompact K)
    (f : Euc n → ℝ) (hi : Integrable f volume) :
    compactFunctionLp K hK f hi =ᵐ[volume.comap (Subtype.val : K → Euc n)]
      fun x : K ↦ f x :=
  by unfold compactFunctionLp; exact MemLp.coeFn_toLp _

theorem compactFunctionLp_totallyBounded_of_translation {n : ℕ} {ι : Type*}
    (K : Set (Euc n)) (hK : IsCompact K) (f : ι → Euc n → ℝ)
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (f i) volume)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ i, (∫ x, ‖f i x‖) ≤ A)
    (D : ℝ≥0∞) (hD : D ≠ ⊤)
    (ht : ∀ i w, (∫⁻ x, ‖f i (x+w)-f i x‖ₑ) ≤ ‖w‖ₑ * D) :
    TotallyBounded (range (fun i ↦ compactFunctionLp K hK (f i) (hi i))) := by
  let μ : Measure K := volume.comap (Subtype.val : K → Euc n)
  let : IsFiniteMeasure μ := compact_subtype_volume_finite hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hmc (i : ι) (j : ℕ) : Continuous (c1Mollify (f i) j) :=
    ((c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left (n := (⊤:ℕ∞)) _
      (c1Mollifier j).contDiff_normed (hi i).locallyIntegrable).continuous
  let a : ℕ → ι → K →ᵇ ℝ := fun j i ↦ BoundedContinuousFunction.mkOfCompact
    ⟨fun x ↦ c1Mollify (f i) j x, (hmc i j).comp continuous_subtype_val⟩
  apply totallyBounded_range_of_uniform_approximation
    (fun i ↦ compactFunctionLp K hK (f i) (hi i))
    (fun j i ↦ BoundedContinuousFunction.toLp 1 μ ℝ (a j i))
  · intro j
    obtain ⟨L,B,hLB⟩ := c1Mollify_uniform_bounds_of_integral_norm (n := n) A hA j
    apply totallyBounded_toLp_of_lipschitz_norm μ (a j) L B
    · intro i
      apply LipschitzWith.of_dist_le_mul
      intro x y
      exact (hLB (f i) (hm i) (hi i) (hb i)).1.dist_le_mul x y
    · intro i x
      exact (hLB (f i) (hm i) (hi i) (hb i)).2 x
  · intro ε hε
    have htend : Tendsto (fun j ↦ ENNReal.ofReal (c1Mollifier (n := n) j).rOut * D)
        atTop (𝓝 0) := by
      simpa only [ENNReal.ofReal_zero,zero_mul] using
        ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal c1Mollifier_radius_tendsto) (Or.inr hD)
    obtain ⟨j,hj⟩ := (htend.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hε))).exists
    refine ⟨j,fun i ↦ edist_lt_ofReal.mp ?_⟩
    apply lt_of_le_of_lt _ hj
    rw [Lp.edist_def, eLpNorm_one_eq_lintegral_enorm
      ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _))]
    calc
      _ = ∫⁻ x : K, ‖f i x-c1Mollify (f i) j x‖ₑ ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [compactFunctionLp_ae K hK (f i) (hi i),
          BoundedContinuousFunction.coeFn_toLp 1 μ ℝ (a j i)] with x hx hy
        change ‖(compactFunctionLp K hK (f i) (hi i)) x-
          (BoundedContinuousFunction.toLp 1 μ ℝ (a j i)) x‖ₑ = _
        rw [hx,hy]
        rfl
      _ = ∫⁻ x in K, ‖f i x-c1Mollify (f i) j x‖ₑ :=
        lintegral_subtype_comap (μ := volume) hK.measurableSet
          (fun x : Euc n ↦ ‖f i x-c1Mollify (f i) j x‖ₑ)
      _ ≤ ∫⁻ x, ‖f i x-c1Mollify (f i) j x‖ₑ := setLIntegral_le_lintegral _ _
      _ ≤ _ := by
        simpa only [enorm_sub_rev] using
          c1Mollify_lintegral_error_of_translation (hm i) (hi i) D (ht i) j

theorem compactFunctionLp_subsequence_of_translation {n : ℕ}
    (K : Set (Euc n)) (hK : IsCompact K) (f : ℕ → Euc n → ℝ)
    (hm : ∀ i, Measurable (f i)) (hi : ∀ i, Integrable (f i) volume)
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ i, (∫ x, ‖f i x‖) ≤ A)
    (D : ℝ≥0∞) (hD : D ≠ ⊤)
    (ht : ∀ i w, (∫⁻ x, ‖f i (x+w)-f i x‖ₑ) ≤ ‖w‖ₑ * D) :
    ∃ g : Lp ℝ 1 (volume.comap (Subtype.val : K → Euc n)),
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun i ↦ compactFunctionLp K hK (f (σ i)) (hi (σ i))) atTop (𝓝 g) := by
  have hc := (compactFunctionLp_totallyBounded_of_translation K hK f hm hi A hA hb D hD ht).closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨g,-,σ,hσ,hg⟩ := hc.tendsto_subseq (fun i ↦ subset_closure
    (mem_range_self (f := fun i ↦ compactFunctionLp K hK (f i) (hi i)) i))
  exact ⟨g,σ,hσ,hg⟩

end RPISingularHarnack

end

end OAI
