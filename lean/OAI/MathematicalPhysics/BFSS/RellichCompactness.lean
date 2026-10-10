import Mathlib
import OAI.MathematicalPhysics.BFSS.RellichSmoothing

namespace OAI

/-! Totally bounded smoothing families and local Rellich compactness. -/

namespace BFSSRellich
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {ι : Type*} [Fintype ι]
variable (φ : ContDiffBump (0 : Euclidean (ι := ι)))
theorem lipschitz_family_totallyBounded {α J : Type*} [PseudoMetricSpace α]
    [CompactSpace α] [FiniteDimensional ℝ F] (g : J → α →ᵇ F)
    (L : ℝ≥0) (C : ℝ) (hL : ∀ j, LipschitzWith L (g j))
    (hC : ∀ j x, ‖g j x‖ ≤ C) : TotallyBounded (range g) := by
  have hA : IsCompact (closure (range g)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : F) C)
      (isCompact_closedBall _ _) (range g) (by
        intro f x hf
        obtain ⟨j, rfl⟩ := hf
        simpa only [Metric.mem_closedBall, dist_zero_right] using hC j x) (by
        apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => (L : ℝ) * r)
          (by
            have hc : Continuous (fun r : ℝ => (L : ℝ) * r) := by fun_prop
            simpa only [mul_zero] using hc.tendsto (0 : ℝ))
        intro x y i
        rcases i with ⟨_, j, rfl⟩
        exact (hL j).dist_le_mul x y)
  exact hA.totallyBounded.subset subset_closure

theorem kernel_family_totallyBounded {J : Type*} [FiniteDimensional ℝ F]
    {K : Set (Euclidean (ι := ι))} [CompactSpace K]
    {κ : Euclidean (ι := ι) → ℝ} {L : ℝ≥0} (hκ : LipschitzWith L κ)
    {C : ℝ} (hC : ∀ x, ‖κ x‖ ≤ C) (f : J → Euclidean (ι := ι) → F)
    (hf : ∀ j, Integrable (f j) volume) {B : ℝ≥0}
    (hB : ∀ j, (∫ y, ‖f j y‖) ≤ B) :
    let g : J → K →ᵇ F := fun j => ContinuousMap.equivBoundedOfCompact K F
      ⟨fun x => kernelAverage κ (f j) x,
        (kernelAverage_lipschitz hκ hC (hf j) (hB j)).continuous.comp continuous_subtype_val⟩
    TotallyBounded (range g) := by
  dsimp only
  apply lipschitz_family_totallyBounded _ (L * B) (|C| * B)
  · intro j
    change LipschitzWith (L * B) (kernelAverage κ (f j) ∘ Subtype.val)
    simpa only [mul_one] using (kernelAverage_lipschitz hκ hC (hf j) (hB j)).comp
      (LipschitzWith.subtype_val K)
  · intro j x
    change ‖kernelAverage κ (f j) x‖ ≤ |C| * B
    calc
      _ ≤ C * ∫ y, ‖f j y‖ := kernelAverage_bound hκ.continuous hC (hf j) x
      _ ≤ |C| * ∫ y, ‖f j y‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (integral_nonneg fun _ => norm_nonneg _)
      _ ≤ |C| * B := mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)

lemma totallyBounded_of_uniform_approximation {X J : Type*} [PseudoMetricSpace X]
    (f : J → X)
    (h : ∀ ε > 0, ∃ g : J → X, TotallyBounded (range g) ∧ ∀ j, dist (f j) (g j) < ε) :
    TotallyBounded (range f) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨g, hg, hfg⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨s, hs, hgs⟩ := Metric.totallyBounded_iff.mp hg (ε / 2) (half_pos hε)
  refine ⟨s, hs, ?_⟩
  rintro _ ⟨j, rfl⟩
  obtain ⟨y, hys, hy⟩ := mem_iUnion₂.mp (hgs (mem_range_self j))
  apply mem_iUnion₂.mpr
  refine ⟨y, hys, ?_⟩
  exact (dist_triangle (f j) (g j) y).trans_lt
    (by simpa only [add_halves] using add_lt_add (hfg j) hy)

lemma opNorm_sq_le_coordinate_sum [DecidableEq ι] (T : Euclidean (ι := ι) →L[ℝ] F) :
    ‖T‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖T (EuclideanSpace.single i 1)‖ ^ 2 := by
  have hb : ‖T‖ ≤ ∑ i, ‖T (EuclideanSpace.single i 1)‖ := by
    apply T.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    intro v
    have hv : v = ∑ i, (v i) • EuclideanSpace.single i 1 := by
      ext j
      simp [Pi.single_apply]
    calc
      ‖T v‖ = ‖∑ i, (v i) • T (EuclideanSpace.single i 1)‖ := by
        conv_lhs => rw [hv, map_sum]
        simp only [map_smul]
      _ ≤ ∑ i, ‖(v i) • T (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ‖T (EuclideanSpace.single i 1)‖ * ‖v‖ := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul, mul_comm]
        exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le v i) (norm_nonneg _)
      _ = _ := (Finset.sum_mul _ _ _).symm
  calc
    _ ≤ (∑ i, ‖T (EuclideanSpace.single i 1)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ ≤ _ := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
          (fun _ : ι => (1 : ℝ)) (fun i => ‖T (EuclideanSpace.single i 1)‖)

omit [NormedSpace ℝ F] in
lemma integral_norm_le_volume_add_square {f : Euclidean (ι := ι) → F}
    (hf : Continuous f) (hfK : HasCompactSupport f) {K : Set (Euclidean (ι := ι))}
    (hK : IsCompact K) (hsupp : Function.support f ⊆ K) :
    (∫ x, ‖f x‖) ≤ volume.real K + ∫ x, ‖f x‖ ^ 2 := by
  have hi : Integrable f volume := hf.integrable_of_hasCompactSupport hfK
  have hs := continuous_norm_sq_integrable hf hfK
  have he (x : Euclidean (ι := ι)) (hx : x ∉ K) : f x = 0 := by
    by_contra hn
    exact hx (hsupp hn)
  have h1 : IntegrableOn (fun _ : Euclidean (ι := ι) => (1 : ℝ)) K :=
    integrableOn_const hK.measure_lt_top.ne
  calc
    _ = ∫ x in K, ‖f x‖ := (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [he x hx, norm_zero])).symm
    _ ≤ ∫ x in K, (1 + ‖f x‖ ^ 2) := by
      apply integral_mono hi.norm.integrableOn (h1.add hs.integrableOn)
      intro x
      change ‖f x‖ ≤ 1 + ‖f x‖ ^ 2
      nlinarith [sq_nonneg (‖f x‖ - 1)]
    _ = volume.real K + ∫ x, ‖f x‖ ^ 2 := by
      have hsK : (∫ x in K, ‖f x‖ ^ 2) = ∫ x, ‖f x‖ ^ 2 :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => by rw [he x hx, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)])
      rw [integral_add h1 hs.integrableOn, hsK]
      simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
        Measure.real]

section Hilbert
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

lemma continuousLp_dist_square {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [BorelSpace α] [CompactSpace α] [SecondCountableTopologyEither α H]
    (μ : Measure α) [IsFiniteMeasure μ] (f g : C(α, H)) :
    dist ((ContinuousMap.toLp 2 μ ℝ) f) ((ContinuousMap.toLp 2 μ ℝ) g) ^ 2 =
      ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub ((ContinuousMap.toLp 2 μ ℝ) f) ((ContinuousMap.toLp 2 μ ℝ) g),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ g] with x hs hf hg
  rw [hs, Pi.sub_apply, hf, hg, real_inner_self_eq_norm_sq]

instance compact_comap_finite {K : Set (Euclidean (ι := ι))} [CompactSpace K] :
    IsFiniteMeasure (volume.comap (Subtype.val : K → Euclidean (ι := ι))) where
  measure_univ_lt_top := by
    have hK : IsCompact K := isCompact_iff_compactSpace.mpr inferInstance
    rw [comap_subtype_coe_apply hK.measurableSet]
    simpa only [image_univ, Subtype.range_coe] using hK.measure_lt_top (μ := volume)

def localLp {K : Set (Euclidean (ι := ι))} [CompactSpace K]
    (f : Euclidean (ι := ι) → H) (hf : Continuous f) :
    Lp H 2 (volume.comap (Subtype.val : K → Euclidean (ι := ι))) :=
  (ContinuousMap.toLp 2 _ ℝ) ⟨fun x => f x, hf.comp continuous_subtype_val⟩

lemma localLp_dist_square {K : Set (Euclidean (ι := ι))} [CompactSpace K]
    (f g : Euclidean (ι := ι) → H) (hf : Continuous f) (hg : Continuous g) :
    dist (localLp (K := K) f hf) (localLp (K := K) g hg) ^ 2 =
      ∫ x in K, ‖f x - g x‖ ^ 2 := by
  rw [localLp, localLp, continuousLp_dist_square]
  exact integral_subtype_comap
    (show IsCompact K from isCompact_iff_compactSpace.mpr inferInstance).measurableSet
    (fun x => ‖f x - g x‖ ^ 2)

theorem localRellich {J : Type*} [FiniteDimensional ℝ H]
    {K : Set (Euclidean (ι := ι))} [CompactSpace K]
    (f : J → Euclidean (ι := ι) → H) (hf : ∀ j, ContDiff ℝ 1 (f j))
    (hfK : ∀ j, HasCompactSupport (f j)) (A B : ℝ≥0)
    (hA : ∀ j, (∫ x, ‖fderiv ℝ (f j) x‖ ^ 2) ≤ (A : ℝ) ^ 2)
    (hB : ∀ j, (∫ x, ‖f j x‖) ≤ B) :
    TotallyBounded (range (fun j => localLp (K := K) (f j) (hf j).continuous)) := by
  apply totallyBounded_of_uniform_approximation
  intro ε hε
  let r : ℝ := ε / (2 * ((A : ℝ) + 1))
  have hr : 0 < r := div_pos hε (by positivity)
  let φ : ContDiffBump (0 : Euclidean (ι := ι)) :=
    ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (φ.hasCompactSupport_normed (μ := volume))
    (show ContDiff ℝ 1 (φ.normed volume) from φ.contDiff_normed) (by norm_num)
  obtain ⟨C, hC⟩ := (φ.hasCompactSupport_normed.isCompact_range
    (φ.continuous_normed (μ := volume))).isBounded.exists_norm_le
  have hC' : ∀ x, ‖φ.normed volume x‖ ≤ C := fun x => hC _ (mem_range_self x)
  have hi (j : J) : Integrable (f j) volume :=
    (hf j).continuous.integrable_of_hasCompactSupport (hfK j)
  have hc (j : J) : Continuous (kernelAverage (φ.normed volume) (f j)) :=
    (kernelAverage_lipschitz hL hC' (hi j) (hB j)).continuous
  let g : J → K →ᵇ H := fun j => ContinuousMap.equivBoundedOfCompact K H
    ⟨fun x => kernelAverage (φ.normed volume) (f j) x,
      (hc j).comp continuous_subtype_val⟩
  let μ : Measure K := volume.comap Subtype.val
  let T := BoundedContinuousFunction.toLp (E := H) 2 μ ℝ
  refine ⟨fun j => T (g j), ?_, ?_⟩
  · have h := (kernel_family_totallyBounded hL hC' f hi hB (K := K)).image T.uniformContinuous
    apply h.subset
    rintro _ ⟨j, rfl⟩
    exact ⟨g j, ⟨j, rfl⟩, rfl⟩
  · intro j
    have he : T (g j) = localLp (K := K) (kernelAverage (φ.normed volume) (f j)) (hc j) := rfl
    change dist (localLp (K := K) (f j) (hf j).continuous) (T (g j)) < ε
    rw [he]
    have hb : dist (localLp (K := K) (f j) (hf j).continuous)
        (localLp (K := K) (kernelAverage (φ.normed volume) (f j)) (hc j)) ^ 2 ≤
        (r * (A : ℝ)) ^ 2 := by
      rw [dist_comm, localLp_dist_square]
      have hint : Integrable (fun x => ‖kernelAverage (φ.normed volume) (f j) x - f j x‖ ^ 2)
          volume := by
        simpa only [kernelAverage_eq_smoothAverage] using
          smoothAverage_sub_square_integrable (hf j).continuous (hfK j) (μ := bumpMeasure φ)
      calc
        _ ≤ ∫ x, ‖kernelAverage (φ.normed volume) (f j) x - f j x‖ ^ 2 :=
          integral_mono_measure Measure.restrict_le_self
            (Filter.Eventually.of_forall fun _ => sq_nonneg _) hint
        _ ≤ r ^ 2 * ∫ x, ‖fderiv ℝ (f j) x‖ ^ 2 := kernelAverage_error φ (hf j) (hfK j)
        _ ≤ r ^ 2 * (A : ℝ) ^ 2 := mul_le_mul_of_nonneg_left (hA j) (sq_nonneg _)
        _ = _ := (mul_pow r (A : ℝ) 2).symm
    have hdist := (sq_le_sq₀ dist_nonneg (mul_nonneg hr.le A.coe_nonneg)).mp hb
    apply hdist.trans_lt
    dsimp [r]
    have hd : 0 < 2 * ((A : ℝ) + 1) := by positivity
    rw [div_mul_eq_mul_div, div_lt_iff₀ hd]
    nlinarith [A.coe_nonneg]

end Hilbert

end
end BFSSRellich

end OAI
