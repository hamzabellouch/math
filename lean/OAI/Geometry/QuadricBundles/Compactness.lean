import OAI.Geometry.QuadricBundles.WeakLimits

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27

noncomputable section

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
theorem bounded_hilbert_weak_subsequence
    {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    {u : ℕ → E} {R : ℝ} (hu : ∀ k, ‖u k‖ ≤ R) :
    ∃ w : E, ‖w‖ ≤ R ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ v : E, Tendsto (fun k ↦ inner ℂ (u (φ k)) v) atTop (𝓝 (inner ℂ w v)) := by
  let d : ℕ → WeakDual ℂ E := fun k ↦
    StrongDual.toWeakDual ((InnerProductSpace.toDual ℂ E) (u k))
  have hd (k : ℕ) : d k ∈ WeakDual.toStrongDual ⁻¹'
      Metric.closedBall (0 : StrongDual ℂ E) R := by
    simpa [d, Metric.mem_closedBall, dist_zero_right] using hu k
  obtain ⟨w', hw', φ, hφ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℂ E (0 : StrongDual ℂ E) R).subseq_of_frequently_in
      (Filter.Frequently.of_forall hd)
  let w := (InnerProductSpace.toDual ℂ E).symm (WeakDual.toStrongDual w')
  refine ⟨w, ?_, φ, hφ, ?_⟩
  · change ‖(InnerProductSpace.toDual ℂ E).symm (WeakDual.toStrongDual w')‖ ≤ R
    simpa only [LinearIsometryEquiv.norm_map, mem_preimage, Metric.mem_closedBall,
      dist_zero_right] using hw'
  · intro v
    have hv := (WeakDual.eval_continuous (𝕜 := ℂ) v).continuousAt.tendsto.comp hlim
    simpa [d, w, Function.comp_def] using hv

lemma isClosed_bounded_positive_coefficients {n : Type u2} [Fintype n] [DecidableEq n]
    (R : ℝ) : IsClosed {v : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R} := by
  exact (isClosed_matrix_positive_semidefinite.preimage continuous_coefficientsToMatrix).inter
    (isClosed_le continuous_norm continuous_const)

lemma convex_bounded_positive_coefficients {n : Type u3} [Fintype n] [DecidableEq n]
    (R : ℝ) : Convex ℝ {v : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R} := by
  have hc : Convex ℝ {v : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix v).PosSemidef} :=
    convex_matrix_positive_semidefinite.linear_preimage
      (coefficientsToMatrix.restrictScalars ℝ)
  refine hc.inter ?_
  intro x hx y hy a b ha hb hab
  change ‖a • x + b • y‖ ≤ R
  calc
    ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
    _ = a * ‖x‖ + b * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = R := by rw [← add_mul, hab, one_mul]

lemma bounded_hilbert_weak_subsequence_in
    {E : Type u4} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {C : Set E} (hc : IsClosed C) (hv : Convex ℝ C)
    {u : ℕ → E} {R : ℝ} (hu : ∀ k, ‖u k‖ ≤ R) (hmem : ∀ k, u k ∈ C) :
    ∃ w ∈ C, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ v : E, Tendsto (fun k ↦ inner ℂ (u (φ k)) v) atTop (𝓝 (inner ℂ w v)) := by
  obtain ⟨w, _, φ, hφ, hlim⟩ := bounded_hilbert_weak_subsequence hu
  exact ⟨w, mem_closed_convex_of_weak_limit hc hv (fun k ↦ hmem (φ k)) hlim,
    φ, hφ, hlim⟩

lemma isClosed_ae_variable_mem_Lp {α : Type u5} {E : Type u6} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : α → Set E} (hC : ∀ x, IsClosed (C x)) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C x} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, f n x ∈ C x := ae_all_iff.mpr hf
  filter_upwards [hall, hφ] with x hx hlim
  exact (hC x).mem_of_tendsto hlim (Eventually.of_forall fun n ↦ hx (φ n))

lemma convex_ae_variable_mem_Lp {α : Type u7} {E : Type u8} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : α → Set E} (hC : ∀ x, Convex ℝ (C x)) :
    Convex ℝ {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C x} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g),
    Lp.coeFn_smul a f, Lp.coeFn_smul b g] with x hx hy hadd hsmul₁ hsmul₂
  change (a • f + b • g) x ∈ C x
  rw [hadd, Pi.add_apply, hsmul₁, hsmul₂]
  exact hC x hx hy ha hb hab

lemma L2_integrable_of_finite_support {α : Type u9} {E : Type u10} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : Lp E 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) : Integrable (fun x ↦ f x) μ := by
  have hi : Integrable (s.indicator (fun x ↦ f x)) μ :=
    (integrable_indicator_iff hs).mpr (integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs)
  apply hi.congr
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [indicator_of_mem hxs]
  · simp only [indicator_of_notMem hxs, hx hxs]

theorem supported_positive_coefficients_weak_subsequence
    {α : Type u11} {n : Type u12} [MeasurableSpace α] [Fintype n] [DecidableEq n]
    {μ : Measure α} [IsSeparable μ]
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {u : ℕ → Lp (EuclideanSpace ℂ (n × n)) 2 μ} {R : ℝ}
    (hR : 0 ≤ R)
    (hu : ∀ k, ∀ᵐ x ∂μ, (coefficientsToMatrix (u k x)).PosSemidef ∧
      ‖u k x‖ ≤ R ∧ (x ∉ s → u k x = 0)) :
    ∃ w : Lp (EuclideanSpace ℂ (n × n)) 2 μ,
      (∀ᵐ x ∂μ, (coefficientsToMatrix (w x)).PosSemidef ∧
        ‖w x‖ ≤ R ∧ (x ∉ s → w x = 0)) ∧
      Integrable (fun x ↦ w x) μ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ v,
        Tendsto (fun k ↦ inner ℂ (u (φ k)) v) atTop (𝓝 (inner ℂ w v)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let C : α → Set (EuclideanSpace ℂ (n × n)) := fun x ↦
    {v | (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R ∧ (x ∉ s → v = 0)}
  have hclosed (x : α) : IsClosed (C x) := by
    have he : C x = {v | (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R} ∩
        {v | x ∉ s → v = 0} := by ext v; simp only [C, mem_ofPred_eq, mem_inter_iff, and_assoc]
    rw [he]
    apply (isClosed_bounded_positive_coefficients R).inter
    by_cases hx : x ∈ s
    · simpa only [hx, not_true_eq_false, IsEmpty.forall_iff, ofPred_true] using
        (isClosed_univ : IsClosed (univ : Set (EuclideanSpace ℂ (n × n))))
    · simpa only [hx, not_false_eq_true, forall_true_left, ofPred_eq_eq_singleton] using
        (isClosed_singleton : IsClosed ({0} : Set (EuclideanSpace ℂ (n × n))))
  have hconvex (x : α) : Convex ℝ (C x) := by
    have he : C x = {v | (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R} ∩
        {v | x ∉ s → v = 0} := by ext v; simp only [C, mem_ofPred_eq, mem_inter_iff, and_assoc]
    rw [he]
    apply (convex_bounded_positive_coefficients R).inter
    by_cases hx : x ∈ s
    · simpa only [hx, not_true_eq_false, IsEmpty.forall_iff, ofPred_true] using
        (convex_univ : Convex ℝ (univ : Set (EuclideanSpace ℂ (n × n))))
    · simpa only [hx, not_false_eq_true, forall_true_left, ofPred_eq_eq_singleton] using
        (convex_singleton (0 : EuclideanSpace ℂ (n × n)) : Convex ℝ ({0} : Set (EuclideanSpace ℂ (n × n))))
  let g : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs R
  have hn (k : ℕ) : ‖u k‖ ≤ ‖g‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hu k, (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := R))] with x hx hg
    change ‖u k x‖ ≤ ‖(indicatorConstLp 2 hs hμs R) x‖
    rw [hg]
    by_cases hxs : x ∈ s
    · simpa only [indicator_of_mem hxs, Real.norm_eq_abs, abs_of_nonneg hR] using hx.2.1
    · simp only [indicator_of_notMem hxs, hx.2.2 hxs, norm_zero, le_refl]
  obtain ⟨w, hw, φ, hφ, hlim⟩ := bounded_hilbert_weak_subsequence_in
    (isClosed_ae_variable_mem_Lp hclosed) (convex_ae_variable_mem_Lp hconvex) hn hu
  change (∀ᵐ x ∂μ, (coefficientsToMatrix (w x)).PosSemidef ∧ ‖w x‖ ≤ R ∧ (x ∉ s → w x = 0)) at hw
  exact ⟨w, hw, L2_integrable_of_finite_support hs hμs w (hw.mono fun _ h ↦ h.2.2),
    φ, hφ, hlim⟩

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

local instance {n : Type u13} [Fintype n] : ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))

noncomputable def matrixToCoefficients {n : Type u14} [Fintype n] :
    Matrix n n ℂ →ₗ[ℂ] EuclideanSpace ℂ (n × n) where
  toFun H := WithLp.toLp 2 (fun ij ↦ H ij.1 ij.2)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma coefficients_matrix_inverse {n : Type u15} [Fintype n] (H : Matrix n n ℂ) :
    coefficientsToMatrix (matrixToCoefficients H) = H := rfl

lemma matrix_coefficients_memLp {α : Type u16} {n : Type u17} [MeasurableSpace α]
    [Fintype n] {μ : Measure α} {H : α → Matrix n n ℂ} {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (hH : AEStronglyMeasurable H μ)
    {R : ℝ} (_hR : 0 ≤ R)
    (hb : ∀ᵐ x ∂μ, ‖matrixToCoefficients (H x)‖ ≤ R ∧ (x ∉ s → H x = 0)) :
    MemLp (fun x ↦ matrixToCoefficients (H x)) 2 μ := by
  apply (memLp_indicator_const 2 hs R (Or.inr hμs)).mono'
    ((LinearMap.continuous_of_finiteDimensional matrixToCoefficients).comp_aestronglyMeasurable hH)
  filter_upwards [hb] with x hx
  by_cases hxs : x ∈ s
  · simpa only [indicator_of_mem hxs] using hx.1
  · simp only [indicator_of_notMem hxs, hx.2 hxs, map_zero, norm_zero, le_refl]

local instance : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

theorem local_quadratic_compactness {n : Type u18} [Fintype n] [DecidableEq n]
    {Hm : ℕ → (ℂ × ℂ) → Matrix n n ℂ} {Ω U s : Set (ℂ × ℂ)}
    (hΩ : IsOpen Ω) (hU : IsOpen U) (hs : MeasurableSet s) (hμs : volume s ≠ ∞)
    (hmeas : ∀ m, AEStronglyMeasurable (Hm m))
    (hposm : ∀ m, ∀ᵐ x ∂volume, (Hm m x).PosSemidef)
    (hc : ∀ m, ContinuousOn (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2)
      (Ω ×ˢ univ))
    (hp : ∀ m, DiskPshOn (Ω ×ˢ univ)
      (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2))
    {R C : ℝ} (hR : 0 ≤ R)
    (hcoef : ∀ m, ∀ᵐ x ∂volume, ‖matrixToCoefficients (Hm m x)‖ ≤ R ∧
      (x ∉ s → Hm m x = 0))
    {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hb : ∀ k, ∀ x ∈ U, closedBall x (r k) ⊆ Ω)
    (hbound : ∀ m, ∀ x ∈ Ω, ∀ v, quadraticValue (Hm m x) v ≤ C * ‖v‖ ^ 2) :
    ∃ (M : (ℂ × ℂ) → Matrix n n ℂ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ x ∈ U, (M x).PosSemidef) ∧
      DiskPshOn (U ×ˢ univ)
        (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (M p.1) p.2) ∧
      ∀ x ρ v, ball x ρ ⊆ U →
        Tendsto (fun m ↦ ⨍ y in ball x ρ, quadraticValue (Hm (φ m) y) v) atTop
          (𝓝 (⨍ y in ball x ρ, quadraticValue (M y) v)) := by
  have hLp (m : ℕ) := matrix_coefficients_memLp hs hμs (hmeas m) hR (hcoef m)
  let f (m : ℕ) := (hLp m).toLp (fun x ↦ matrixToCoefficients (Hm m x))
  have hf (m : ℕ) : (fun x ↦ coefficientsToMatrix (f m x)) =ᵐ[volume] Hm m := by
    filter_upwards [(hLp m).coeFn_toLp] with x hx
    exact congrArg coefficientsToMatrix hx
  have hfb (m : ℕ) : ∀ᵐ x ∂volume, (coefficientsToMatrix (f m x)).PosSemidef ∧
      ‖f m x‖ ≤ R ∧ (x ∉ s → f m x = 0) := by
    filter_upwards [(hLp m).coeFn_toLp, hposm m, hcoef m] with x hx hp hb
    rw [hx]
    exact ⟨hp, hb.1, fun hxs ↦ by rw [hb.2 hxs, map_zero]⟩
  obtain ⟨w, hw, hwL1, φ, hφ, hlim⟩ :=
    supported_positive_coefficients_weak_subsequence hs hμs hR hfb
  have hHm (m : ℕ) : Integrable (Hm m) := by
    have hf1 := L2_integrable_of_finite_support hs hμs (f m) ((hfb m).mono fun _ h ↦ h.2.2)
    exact (coefficientsToMatrix.toContinuousLinearMap.integrable_comp hf1).congr (hf m)
  obtain ⟨M, hM, hae, hpsh⟩ := weak_quadratic_psh_representative hΩ hU
    (fun m ↦ hf (φ m)) hlim hwL1 (fun m ↦ hHm (φ m))
    (fun m ↦ hposm (φ m)) (fun m ↦ hc (φ m)) (fun m ↦ hp (φ m)) hr hr0 hb
    (fun m ↦ hbound (φ m))
  refine ⟨M, φ, hφ, hM, hpsh, ?_⟩
  intro x ρ v hball
  have hh := weak_quadratic_averages (fun m ↦ hf (φ m)) hlim x ρ v
  convert hh using 1
  congr 1
  apply average_congr
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball hae] with y hy
  exact congrArg (fun H ↦ quadraticValue H v) hy

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
local instance : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

lemma DiskPshOn.moving_base_mass {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {q : (ℂ × ℂ) → ℝ} (hq : DiskPshOn Ω q) {x y : ℂ × ℂ} {r a : ℝ}
    (hr : 0 < r) (hxy : dist y x < r) (hb : closedBall x (3*r) ⊆ Ω)
    (hpos : ∀ z ∈ ball x (2*r), 0 ≤ q z)
    (hi : IntegrableOn q (ball x (2*r))) (ha : a ≤ q y) :
    (volume (ball (0 : ℂ × ℂ) r)).toReal * a ≤ ∫ z in ball x (2*r), q z := by
  have hsub : ball y r ⊆ ball x (2*r) :=
    ball_subset_ball' (by linarith)
  have hcb : closedBall y r ⊆ Ω := by
    apply Subset.trans _ hb
    exact closedBall_subset_closedBall' (by linarith)
  have hy : y ∈ Ω := hcb (mem_closedBall_self hr.le)
  have hs := hq.base_submean hΩ hy hr hcb (hi.mono_set hsub)
  calc
    (volume (ball (0 : ℂ × ℂ) r)).toReal * a = (volume (ball y r)).toReal * a := by
      rw [Measure.addHaar_ball_center _ y, Measure.addHaar_ball_center _ (0 : ℂ × ℂ)]
    _ ≤ (volume (ball y r)).toReal * q y :=
      mul_le_mul_of_nonneg_left ha ENNReal.toReal_nonneg
    _ ≤ ∫ z in ball y r, q z := hs
    _ ≤ ∫ z in ball x (2*r), q z :=
      setIntegral_mono_set hi ((ae_restrict_mem measurableSet_ball).mono fun z hz ↦ hpos z hz) (Eventually.of_forall hsub)

lemma nonzero_of_average_limit {α : Type u19} [MeasurableSpace α] {μ : Measure α}
    {f : ℕ → α → ℝ} {q : α → ℝ} {s : Set α} (hs : MeasurableSet s) {a : ℝ} (ha : 0 < a)
    (hlim : Tendsto (fun m ↦ ⨍ x in s, f m x ∂μ) atTop (𝓝 (⨍ x in s, q x ∂μ)))
    (hmass : ∀ᶠ m in atTop, a ≤ ⨍ x in s, f m x ∂μ) :
    ∃ x ∈ s, q x ≠ 0 := by
  have h := ge_of_tendsto hlim hmass
  by_contra hn
  push Not at hn
  have hz : (⨍ x in s, q x ∂μ) = 0 := by
    rw [setAverage_eq]
    have hi : (∫ x in s, q x ∂μ) = 0 := integral_eq_zero_of_ae
      ((ae_restrict_mem hs).mono fun x hx ↦ hn x hx)
    rw [hi, smul_zero]
  rw [hz] at h
  exact (not_le_of_gt ha) h

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
theorem bounded_hilbert_countable_weak_subsequence
    {ι : Type u20} [Countable ι] {E : ι → Type u27}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
    [∀ i, CompleteSpace (E i)] [∀ i, TopologicalSpace.SeparableSpace (E i)]
    {u : ℕ → ∀ i, E i} {R : ι → ℝ} (hu : ∀ k i, ‖u k i‖ ≤ R i) :
    ∃ (w : ∀ i, E i) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, ‖w i‖ ≤ R i) ∧
      ∀ i (v : E i), Tendsto (fun k ↦ inner ℂ (u (φ k) i) v) atTop
        (𝓝 (inner ℂ (w i) v)) := by
  let K (i : ι) : Set (WeakDual ℂ (E i)) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ (E i)) (R i)
  have hc (i : ι) : IsCompact (K i) := WeakDual.isCompact_closedBall (0 : StrongDual ℂ (E i)) (R i)
  let (i : ι) : CompactSpace (K i) := isCompact_iff_compactSpace.mp (hc i)
  let (i : ι) : TopologicalSpace.MetrizableSpace (K i) :=
    WeakDual.metrizable_of_isCompact ℂ (E i) (K i) (hc i)
  let d (k : ℕ) (i : ι) : K i :=
    ⟨StrongDual.toWeakDual ((InnerProductSpace.toDual ℂ (E i)) (u k i)), by
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hu k i⟩
  obtain ⟨w', _, φ, hφ, hlim⟩ :=
    (isCompact_univ (X := ∀ i, K i)).isSeqCompact.subseq_of_frequently_in
      (Filter.Frequently.of_forall (fun k ↦ mem_univ (d k)))
  let w (i : ι) : E i := (InnerProductSpace.toDual ℂ (E i)).symm
    (WeakDual.toStrongDual (w' i))
  refine ⟨w, φ, hφ, ?_, ?_⟩
  · intro i
    change ‖(InnerProductSpace.toDual ℂ (E i)).symm (WeakDual.toStrongDual (w' i))‖ ≤ R i
    simpa only [LinearIsometryEquiv.norm_map, K, mem_preimage, Metric.mem_closedBall,
      dist_zero_right] using (w' i).property
  · intro i v
    have hi := ((continuous_apply i).continuousAt.tendsto.comp hlim)
    have hv := (WeakDual.eval_continuous (𝕜 := ℂ) v).continuousAt.tendsto.comp
      (continuous_subtype_val.continuousAt.tendsto.comp hi)
    simpa [d, w, Function.comp_def] using hv

theorem countable_supported_positive_weak_subsequence
    {ι : Type u21} {α : Type u22} {n : Type u23} [Countable ι] [MeasurableSpace α] [Fintype n] [DecidableEq n]
    {μ : Measure α} [IsSeparable μ]
    {s : ι → Set α} (hs : ∀ i, MeasurableSet (s i)) (hμs : ∀ i, μ (s i) ≠ ∞)
    {u : ℕ → ι → Lp (EuclideanSpace ℂ (n × n)) 2 μ} {R : ι → ℝ}
    (hR : ∀ i, 0 ≤ R i)
    (hu : ∀ k i, ∀ᵐ x ∂μ, (coefficientsToMatrix (u k i x)).PosSemidef ∧
      ‖u k i x‖ ≤ R i ∧ (x ∉ s i → u k i x = 0)) :
    ∃ (w : ι → Lp (EuclideanSpace ℂ (n × n)) 2 μ) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ i, (∀ᵐ x ∂μ, (coefficientsToMatrix (w i x)).PosSemidef ∧
        ‖w i x‖ ≤ R i ∧ (x ∉ s i → w i x = 0)) ∧
        Integrable (fun x ↦ w i x) μ ∧ ∀ v,
          Tendsto (fun k ↦ inner ℂ (u (φ k) i) v) atTop (𝓝 (inner ℂ (w i) v)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let g (i : ι) : Lp ℝ 2 μ := indicatorConstLp 2 (hs i) (hμs i) (R i)
  have hn (k : ℕ) (i : ι) : ‖u k i‖ ≤ ‖g i‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hu k i, (indicatorConstLp_coeFn (p := 2) (hs := hs i)
      (hμs := hμs i) (c := R i))] with x hx hg
    change ‖u k i x‖ ≤ ‖(indicatorConstLp 2 (hs i) (hμs i) (R i)) x‖
    rw [hg]
    by_cases hxs : x ∈ s i
    · simpa only [indicator_of_mem hxs, Real.norm_eq_abs, abs_of_nonneg (hR i)] using hx.2.1
    · simp only [indicator_of_notMem hxs, hx.2.2 hxs, norm_zero, le_refl]
  obtain ⟨w,φ,hφ,_,hlim⟩ := bounded_hilbert_countable_weak_subsequence hn
  refine ⟨w,φ,hφ,?_⟩
  intro i
  let C : α → Set (EuclideanSpace ℂ (n × n)) := fun x ↦
    {v | (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R i ∧ (x ∉ s i → v = 0)}
  have hclosed (x : α) : IsClosed (C x) := by
    have he : C x = {v | (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R i} ∩
        {v | x ∉ s i → v = 0} := by ext v; simp only [C, mem_ofPred_eq, mem_inter_iff, and_assoc]
    rw [he]
    apply (isClosed_bounded_positive_coefficients (R i)).inter
    by_cases hx : x ∈ s i
    · simpa only [hx, not_true_eq_false, IsEmpty.forall_iff, ofPred_true] using
        (isClosed_univ : IsClosed (univ : Set (EuclideanSpace ℂ (n × n))))
    · simpa only [hx, not_false_eq_true, forall_true_left, ofPred_eq_eq_singleton] using
        (isClosed_singleton : IsClosed ({0} : Set (EuclideanSpace ℂ (n × n))))
  have hconvex (x : α) : Convex ℝ (C x) := by
    have he : C x = {v | (coefficientsToMatrix v).PosSemidef ∧ ‖v‖ ≤ R i} ∩
        {v | x ∉ s i → v = 0} := by ext v; simp only [C, mem_ofPred_eq, mem_inter_iff, and_assoc]
    rw [he]
    apply (convex_bounded_positive_coefficients (R i)).inter
    by_cases hx : x ∈ s i
    · simpa only [hx, not_true_eq_false, IsEmpty.forall_iff, ofPred_true] using
        (convex_univ : Convex ℝ (univ : Set (EuclideanSpace ℂ (n × n))))
    · simpa only [hx, not_false_eq_true, forall_true_left, ofPred_eq_eq_singleton] using
        (convex_singleton (0 : EuclideanSpace ℂ (n × n)) : Convex ℝ ({0} : Set (EuclideanSpace ℂ (n × n))))
  have hw := mem_closed_convex_of_weak_limit
    (isClosed_ae_variable_mem_Lp hclosed) (convex_ae_variable_mem_Lp hconvex)
    (fun k ↦ hu (φ k) i) (hlim i)
  change (∀ᵐ x ∂μ, (coefficientsToMatrix (w i x)).PosSemidef ∧
    ‖w i x‖ ≤ R i ∧ (x ∉ s i → w i x = 0)) at hw
  exact ⟨hw,L2_integrable_of_finite_support (hs i) (hμs i) (w i)
    (hw.mono fun _ h ↦ h.2.2), hlim i⟩

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise
local instance : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

local instance {n : Type u24} [Fintype n] : ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))

theorem countable_local_quadratic_compactness_with_weak
    {ι : Type u25} {n : Type u26} [Countable ι] [Fintype n] [DecidableEq n]
    {Hm : ℕ → ι → (ℂ × ℂ) → Matrix n n ℂ}
    {Ω U s : ι → Set (ℂ × ℂ)}
    (hΩ : ∀ i, IsOpen (Ω i)) (hU : ∀ i, IsOpen (U i))
    (hs : ∀ i, MeasurableSet (s i)) (hμs : ∀ i, volume (s i) ≠ ∞)
    (hmeas : ∀ m i, AEStronglyMeasurable (Hm m i))
    (hposm : ∀ m i, ∀ᵐ x ∂volume, (Hm m i x).PosSemidef)
    (hc : ∀ m i, ContinuousOn
      (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m i p.1) p.2) (Ω i ×ˢ univ))
    (hp : ∀ m i, DiskPshOn (Ω i ×ˢ univ)
      (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m i p.1) p.2))
    {R C : ι → ℝ} (hR : ∀ i, 0 ≤ R i)
    (hcoef : ∀ m i, ∀ᵐ x ∂volume, ‖matrixToCoefficients (Hm m i x)‖ ≤ R i ∧
      (x ∉ s i → Hm m i x = 0))
    {r : ι → ℕ → ℝ} (hr : ∀ i k, 0 < r i k)
    (hr0 : ∀ i, Tendsto (r i) atTop (𝓝 0))
    (hb : ∀ i k, ∀ x ∈ U i, closedBall x (r i k) ⊆ Ω i)
    (hbound : ∀ m i, ∀ x ∈ Ω i, ∀ v,
      quadraticValue (Hm m i x) v ≤ C i * ‖v‖ ^ 2) :
    ∃ (M : ι → (ℂ × ℂ) → Matrix n n ℂ)
      (f : ℕ → ι → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ)))
      (w : ι → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ)))
      (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ m i, (fun x ↦ coefficientsToMatrix (f m i x)) =ᵐ[volume] Hm m i) ∧
      (∀ m i, ∀ᵐ x ∂volume, ‖f m i x‖ ≤ R i ∧ (x ∉ s i → f m i x = 0)) ∧
      ∀ i, (M i =ᵐ[volume.restrict (U i)] fun x ↦ coefficientsToMatrix (w i x)) ∧
        (∀ v, Tendsto (fun m ↦ inner ℂ (f (φ m) i) v) atTop (𝓝 (inner ℂ (w i) v))) ∧
        (∀ x ∈ U i, (M i x).PosSemidef) ∧
        DiskPshOn (U i ×ˢ univ)
          (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (M i p.1) p.2) ∧
        ∀ x ρ v, ball x ρ ⊆ U i →
          Tendsto (fun m ↦ ⨍ y in ball x ρ, quadraticValue (Hm (φ m) i y) v) atTop
            (𝓝 (⨍ y in ball x ρ, quadraticValue (M i y) v)) := by
  have hLp (m : ℕ) (i : ι) := matrix_coefficients_memLp
    (hs i) (hμs i) (hmeas m i) (hR i) (hcoef m i)
  let f (m : ℕ) (i : ι) := (hLp m i).toLp (fun x ↦ matrixToCoefficients (Hm m i x))
  have hf (m : ℕ) (i : ι) :
      (fun x ↦ coefficientsToMatrix (f m i x)) =ᵐ[volume] Hm m i := by
    filter_upwards [(hLp m i).coeFn_toLp] with x hx
    exact congrArg coefficientsToMatrix hx
  have hfb (m : ℕ) (i : ι) : ∀ᵐ x ∂volume,
      (coefficientsToMatrix (f m i x)).PosSemidef ∧ ‖f m i x‖ ≤ R i ∧
      (x ∉ s i → f m i x = 0) := by
    filter_upwards [(hLp m i).coeFn_toLp, hposm m i, hcoef m i] with x hx hp hb
    rw [hx]
    exact ⟨hp, hb.1, fun hxs ↦ by rw [hb.2 hxs, map_zero]⟩
  obtain ⟨w,φ,hφ,hw⟩ := countable_supported_positive_weak_subsequence hs hμs hR hfb
  have hHm (m : ℕ) (i : ι) : Integrable (Hm m i) := by
    have hf1 := L2_integrable_of_finite_support (hs i) (hμs i) (f m i)
      ((hfb m i).mono fun _ h ↦ h.2.2)
    exact (coefficientsToMatrix.toContinuousLinearMap.integrable_comp hf1).congr (hf m i)
  have hex (i : ι) := weak_quadratic_psh_representative (hΩ i) (hU i)
    (fun m ↦ hf (φ m) i) (hw i).2.2 (hw i).2.1 (fun m ↦ hHm (φ m) i)
    (fun m ↦ hposm (φ m) i) (fun m ↦ hc (φ m) i) (fun m ↦ hp (φ m) i)
    (hr i) (hr0 i) (hb i) (fun m ↦ hbound (φ m) i)
  choose M hM hae hpsh using hex
  refine ⟨M,f,w,φ,hφ,hf,fun m i ↦ (hfb m i).mono (fun _ h ↦ h.2),
    fun i ↦ ⟨hae i,(hw i).2.2,hM i,hpsh i,?_⟩⟩
  intro x ρ v hball
  have hh := weak_quadratic_averages (fun m ↦ hf (φ m) i) (hw i).2.2 x ρ v
  convert hh using 1
  congr 1
  apply average_congr
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hball (hae i)] with y hy
  exact congrArg (fun H ↦ quadraticValue H v) hy

end QuadricCounterexample

end

end OAI
