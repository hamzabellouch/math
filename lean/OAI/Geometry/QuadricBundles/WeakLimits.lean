import OAI.Geometry.QuadricBundles.MatrixRepresentative

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27 u28 u29 u30 u31

noncomputable section

namespace QuadricCounterexample
open Filter Topology Set MeasureTheory
open scoped ENNReal

lemma tendsto_dual_of_tendsto_inner
    {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {f : ℕ → E} {w : E}
    (h : ∀ v : E, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v)))
    (d : StrongDual ℂ E) : Tendsto (fun k ↦ d (f k)) atTop (𝓝 (d w)) := by
  let v := (InnerProductSpace.toDual ℂ E).symm d
  have h' := (h v).star
  have he (z : E) : star (inner ℂ z v) = d z := by
    change (starRingEnd ℂ) (inner ℂ z v) = d z
    rw [inner_conj_symm]
    exact InnerProductSpace.toDual_symm_apply
  simpa only [he] using h'

lemma tendsto_real_dual_of_tendsto_inner
    {E : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {f : ℕ → E} {w : E}
    (h : ∀ v : E, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v)))
    (d : StrongDual ℝ E) : Tendsto (fun k ↦ d (f k)) atTop (𝓝 (d w)) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_dual_of_tendsto_inner h (StrongDual.extendRCLike d))
  have he (y : E) : ((StrongDual.extendRCLike d) y : ℂ).re = d y :=
    StrongDual.re_extendRCLike_apply (𝕜 := ℂ) d y
  simpa only [Function.comp_def, he] using ht

lemma mem_closed_convex_of_weak_limit
    {E : Type u3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {C : Set E} (hclosed : IsClosed C) (hconvex : Convex ℝ C)
    {f : ℕ → E} {w : E} (hf : ∀ k, f k ∈ C)
    (hlim : ∀ v : E, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v))) :
    w ∈ C := by
  by_contra hw
  obtain ⟨d, r, hr, hw⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hconvex hclosed hw
  have hl := Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_dual_of_tendsto_inner hlim d)
  have he : ∀ᶠ k in atTop, (d (f k)).re ≤ r :=
    Eventually.of_forall fun k ↦ (hr (f k) (hf k)).le
  exact hw.not_ge (le_of_tendsto hl he)

lemma isClosed_ae_linear_constraint {α : Type u4} {E : Type u5} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] (Ω : Set α)
    (ℓ : E →L[ℝ] ℝ) (A : α → Lp E p μ →L[ℝ] ℝ) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ.restrict Ω, ℓ (f x) ≤ A x f} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨φ, hφmono, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  have hall := ae_all_iff.mpr hf
  filter_upwards [hall, ae_restrict_of_ae hφ] with x hx hlim
  have hleft := ℓ.continuous.continuousAt.tendsto.comp hlim
  have hright := (A x).continuous.continuousAt.tendsto.comp
    (hfg.comp hφmono.tendsto_atTop)
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun n ↦ hx (φ n))

lemma convex_ae_linear_constraint {α : Type u6} {E : Type u7} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)] (Ω : Set α)
    (ℓ : E →L[ℝ] ℝ) (A : α → Lp E p μ →L[ℝ] ℝ) :
    Convex ℝ {f : Lp E p μ | ∀ᵐ x ∂μ.restrict Ω, ℓ (f x) ≤ A x f} := by
  intro f hf g hg a b ha hb _
  filter_upwards [hf, hg, ae_restrict_of_ae (Lp.coeFn_add (a • f) (b • g)),
    ae_restrict_of_ae (Lp.coeFn_smul a f),
    ae_restrict_of_ae (Lp.coeFn_smul b g)] with x hx hy hadd hsmul₁ hsmul₂
  rw [hadd, Pi.add_apply, hsmul₁, hsmul₂]
  simp only [Pi.smul_apply, map_add, map_smul, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

theorem ae_linear_constraint_of_weak_limit {α : Type u8} {E : Type u9} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (Ω : Set α) (ℓ : E →L[ℝ] ℝ)
    (A : α → Lp E 2 μ →L[ℝ] ℝ)
    {f : ℕ → Lp E 2 μ} {w : Lp E 2 μ}
    (hf : ∀ k, ∀ᵐ x ∂μ.restrict Ω, ℓ (f k x) ≤ A x (f k))
    (hw : ∀ v, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v))) :
    ∀ᵐ x ∂μ.restrict Ω, ℓ (w x) ≤ A x w :=
  mem_closed_convex_of_weak_limit (isClosed_ae_linear_constraint Ω ℓ A)
    (convex_ae_linear_constraint Ω ℓ A) hf hw

noncomputable def setAverageL2Functional {α : Type u10} {E : Type u11} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (ℓ : E →L[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) : Lp E 2 μ →L[ℝ] ℝ :=
  (μ s).toReal⁻¹ • Complex.reCLM.comp
    ((innerSL ℂ (indicatorConstLp 2 hs hμs
      ((InnerProductSpace.toDual ℂ E).symm (StrongDual.extendRCLike ℓ)))).restrictScalars ℝ)

lemma setAverageL2Functional_apply {α : Type u12} {E : Type u13} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (ℓ : E →L[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (f : Lp E 2 μ) :
    setAverageL2Functional ℓ hs hμs f = ⨍ x in s, ℓ (f x) ∂μ := by
  let z := (InnerProductSpace.toDual ℂ E).symm (StrongDual.extendRCLike ℓ)
  have hz (y : E) : inner ℂ z y = StrongDual.extendRCLike ℓ y :=
    InnerProductSpace.toDual_symm_apply
  change (μ s).toReal⁻¹ * (inner ℂ (indicatorConstLp 2 hs hμs z) f).re = _
  rw [L2.inner_indicatorConstLp_eq_setIntegral_inner ℂ f hs z hμs]
  simp_rw [hz]
  have hg : (∫ x in s, (StrongDual.extendRCLike (𝕜 := ℂ) ℓ) (f x) ∂μ).re =
      ∫ x in s, ((StrongDual.extendRCLike (𝕜 := ℂ) ℓ) (f x)).re ∂μ :=
    (integral_re ((StrongDual.extendRCLike (𝕜 := ℂ) ℓ).integrable_comp
      (integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs))).symm
  rw [hg]
  have he (y : E) : ((StrongDual.extendRCLike ℓ) y : ℂ).re = ℓ y :=
    StrongDual.re_extendRCLike_apply (𝕜 := ℂ) ℓ y
  simp only [he, setAverage_eq, smul_eq_mul, measureReal_def]

lemma tendsto_setAverage_of_tendsto_inner {α : Type u14} {E : Type u15} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (ℓ : E →L[ℝ] ℝ) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {f : ℕ → Lp E 2 μ} {w : Lp E 2 μ}
    (hw : ∀ v, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v))) :
    Tendsto (fun k ↦ ⨍ x in s, ℓ (f k x) ∂μ) atTop (𝓝 (⨍ x in s, ℓ (w x) ∂μ)) := by
  simpa only [setAverageL2Functional_apply] using
    tendsto_real_dual_of_tendsto_inner hw (setAverageL2Functional ℓ hs hμs)

theorem ae_submean_of_weak_limit {α : Type u16} {E : Type u17} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {μ : Measure α} (Ω : Set α) (ℓ : E →L[ℝ] ℝ)
    (S : α → Set α) (hS : ∀ x, MeasurableSet (S x)) (hμS : ∀ x, μ (S x) ≠ ∞)
    {f : ℕ → Lp E 2 μ} {w : Lp E 2 μ}
    (hf : ∀ k, ∀ᵐ x ∂μ.restrict Ω, ℓ (f k x) ≤ ⨍ y in S x, ℓ (f k y) ∂μ)
    (hw : ∀ v, Tendsto (fun k ↦ inner ℂ (f k) v) atTop (𝓝 (inner ℂ w v))) :
    ∀ᵐ x ∂μ.restrict Ω, ℓ (w x) ≤ ⨍ y in S x, ℓ (w y) ∂μ := by
  have hc := ae_linear_constraint_of_weak_limit Ω ℓ
    (fun x ↦ setAverageL2Functional ℓ (hS x) (hμS x))
    (fun k ↦ by simpa only [setAverageL2Functional_apply] using hf k) hw
  simpa only [setAverageL2Functional_apply] using hc

end QuadricCounterexample

namespace QuadricCounterexample
open Set Filter Topology MeasureTheory Metric

theorem DiskPshOn.base_submean
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) {q : ℂ × ℂ → ℝ}
    (hq : DiskPshOn Ω q) {x : ℂ × ℂ} (hx : x ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hb : closedBall x r ⊆ Ω) (hi : IntegrableOn q (ball x r)) :
    (volume (ball x r)).toReal * q x ≤ ∫ y in ball x r, q y := by
  have hprod : Integrable q
      ((volume.restrict (ball x.1 r)).prod (volume.restrict (ball x.2 r))) := by
    rw [Measure.prod_restrict, ball_prod_same]
    exact hi
  have h1 : DiskSubharmonicOn ((fun z : ℂ ↦ (z,x.2)) ⁻¹' Ω)
      (fun z ↦ q (z,x.2)) :=
    hq.2 _ (hΩ.preimage (by fun_prop)) _ (by fun_prop) (fun _ h ↦ h)
  have hb1 : closedBall x.1 r ⊆ (fun z : ℂ ↦ (z,x.2)) ⁻¹' Ω := by
    intro z hz
    apply hb
    simpa only [mem_closedBall, Prod.dist_eq, dist_self, max_le_iff] using
      And.intro (show dist z x.1 ≤ r from hz) hr.le
  have hs1 := h1.2 x.1 hx r hr hb1
  have h2 (z : ℂ) (hz : z ∈ ball x.1 r) :
      (volume (ball x.2 r)).toReal * q (z,x.2) ≤ ∫ w in ball x.2 r, q (z,w) := by
    have hh : DiskSubharmonicOn ((fun w : ℂ ↦ (z,w)) ⁻¹' Ω) (fun w ↦ q (z,w)) :=
      hq.2 _ (hΩ.preimage (by fun_prop)) _ (by fun_prop) (fun _ h ↦ h)
    have hbs : closedBall x.2 r ⊆ (fun w : ℂ ↦ (z,w)) ⁻¹' Ω := by
      intro w hw
      apply hb
      simpa only [mem_closedBall, Prod.dist_eq, max_le_iff] using
        And.intro (le_of_lt (show dist z x.1 < r from hz)) (show dist w x.2 ≤ r from hw)
    exact (hh.2 x.2 (hbs (mem_closedBall_self hr.le)) r hr hbs).2
  have hmeasure : (volume (ball x r)).toReal =
      (volume (ball x.1 r)).toReal * (volume (ball x.2 r)).toReal := by
    rw [← ball_prod_same]
    change ((volume.prod volume) (ball x.1 r ×ˢ ball x.2 r)).toReal = _
    rw [Measure.prod_prod, ENNReal.toReal_mul]
  rw [hmeasure]
  calc
    (volume (ball x.1 r)).toReal * (volume (ball x.2 r)).toReal * q x =
        (volume (ball x.2 r)).toReal * ((volume (ball x.1 r)).toReal * q x) := by ring
    _ ≤ (volume (ball x.2 r)).toReal * (∫ z in ball x.1 r, q (z,x.2)) :=
      mul_le_mul_of_nonneg_left hs1.2 ENNReal.toReal_nonneg
    _ = ∫ z in ball x.1 r, (volume (ball x.2 r)).toReal * q (z,x.2) :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ z in ball x.1 r, ∫ w in ball x.2 r, q (z,w) :=
      integral_mono_ae (hs1.1.const_mul _) hprod.integral_prod_left
        ((ae_restrict_mem measurableSet_ball).mono h2)
    _ = ∫ y in ball x r, q y := by
      rw [← integral_prod q hprod, Measure.prod_restrict, ball_prod_same]
      rfl

end QuadricCounterexample

namespace QuadricCounterexample
open Filter Topology Set MeasureTheory Metric
open scoped ENNReal ComplexOrder Matrix.Norms.Elementwise

lemma isClosed_ae_mem_Lp {α : Type u18} {E : Type u19} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : Set E} (hC : IsClosed C) :
    IsClosed {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  apply IsSeqClosed.isClosed
  intro f g hf hfg
  obtain ⟨φ, _, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hfg).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, f n x ∈ C := ae_all_iff.mpr hf
  filter_upwards [hall, hφ] with x hx hlim
  exact hC.mem_of_tendsto hlim (Eventually.of_forall fun n ↦ hx (φ n))

lemma convex_ae_mem_Lp {α : Type u20} {E : Type u21} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {C : Set E} (hC : Convex ℝ C) :
    Convex ℝ {f : Lp E p μ | ∀ᵐ x ∂μ, f x ∈ C} := by
  intro f hf g hg a b ha hb hab
  filter_upwards [hf, hg, Lp.coeFn_add (a • f) (b • g),
    Lp.coeFn_smul a f, Lp.coeFn_smul b g] with x hx hy hadd hsmul₁ hsmul₂
  change (a • f + b • g) x ∈ C
  rw [hadd, Pi.add_apply, hsmul₁, hsmul₂]
  exact hC hx hy ha hb hab

noncomputable def coefficientsToMatrix {n : Type u22} [Fintype n] :
    EuclideanSpace ℂ (n × n) →ₗ[ℂ] Matrix n n ℂ where
  toFun v i j := v (i,j)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

lemma continuous_coefficientsToMatrix {n : Type u23} [Fintype n] :
    Continuous (coefficientsToMatrix (n := n)) :=
  LinearMap.continuous_of_finiteDimensional _

noncomputable def coefficientsQuadraticCLM {n : Type u24} [Fintype n]
    (v : n → ℂ) : EuclideanSpace ℂ (n × n) →L[ℝ] ℝ :=
  (quadraticValueCLM v).comp
    ((coefficientsToMatrix (n := n)).toContinuousLinearMap.restrictScalars ℝ)

lemma coefficientsQuadraticCLM_apply {n : Type u25} [Fintype n]
    (v : n → ℂ) (c : EuclideanSpace ℂ (n × n)) :
    coefficientsQuadraticCLM v c = quadraticValue (coefficientsToMatrix c) v := rfl

lemma weak_coefficients_positive {α : Type u26} {n : Type u27} [MeasurableSpace α]
    [Fintype n] [DecidableEq n] {μ : Measure α}
    {f : ℕ → Lp (EuclideanSpace ℂ (n × n)) 2 μ}
    {w : Lp (EuclideanSpace ℂ (n × n)) 2 μ}
    (hf : ∀ m, ∀ᵐ x ∂μ, (coefficientsToMatrix (f m x)).PosSemidef)
    (hw : ∀ v, Tendsto (fun m ↦ inner ℂ (f m) v) atTop (𝓝 (inner ℂ w v))) :
    ∀ᵐ x ∂μ, (coefficientsToMatrix (w x)).PosSemidef := by
  have hclosed : IsClosed {c : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix c).PosSemidef} :=
    isClosed_matrix_positive_semidefinite.preimage continuous_coefficientsToMatrix
  have hconvex : Convex ℝ {c : EuclideanSpace ℂ (n × n) |
      (coefficientsToMatrix c).PosSemidef} :=
    convex_matrix_positive_semidefinite.linear_preimage (coefficientsToMatrix.restrictScalars ℝ)
  exact mem_closed_convex_of_weak_limit (isClosed_ae_mem_Lp hclosed)
    (convex_ae_mem_Lp hconvex) hf hw

lemma DiskPshOn.base_average_submean
    {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) {q : ℂ × ℂ → ℝ}
    (hq : DiskPshOn Ω q) {x : ℂ × ℂ} (hx : x ∈ Ω) {r : ℝ} (hr : 0 < r)
    (hb : closedBall x r ⊆ Ω) (hi : IntegrableOn q (ball x r)) :
    q x ≤ ⨍ y in ball x r, q y := by
  have hm : 0 < (volume (ball x r)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (Metric.measure_ball_pos volume x hr)) measure_ball_lt_top.ne
  rw [setAverage_eq, smul_eq_mul, measureReal_def, ← div_eq_inv_mul, le_div_iff₀ hm]
  simpa only [mul_comm] using hq.base_submean hΩ hx hr hb hi

local instance {n : Type u28} [Fintype n] : ContinuousENorm (Matrix n n ℂ) :=
  inferInstanceAs (ContinuousENorm (n → n → ℂ))

lemma weak_quadratic_averages {n : Type u29} [Fintype n]
    {f : ℕ → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {w : Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {Hm : ℕ → (ℂ × ℂ) → Matrix n n ℂ}
    (hf : ∀ m, (fun x ↦ coefficientsToMatrix (f m x)) =ᵐ[volume] Hm m)
    (hw : ∀ v, Tendsto (fun m ↦ inner ℂ (f m) v) atTop (𝓝 (inner ℂ w v)))
    (x : ℂ × ℂ) (r : ℝ) (v : n → ℂ) :
    Tendsto (fun m ↦ ⨍ y in ball x r, quadraticValue (Hm m y) v) atTop
      (𝓝 (⨍ y in ball x r, quadraticValue (coefficientsToMatrix (w y)) v)) := by
  have hlim := tendsto_setAverage_of_tendsto_inner (coefficientsQuadraticCLM v)
    (measurableSet_ball (x := x) (ε := r)) measure_ball_lt_top.ne hw
  have he (m : ℕ) : (⨍ y in ball x r, coefficientsQuadraticCLM v (f m y)) =
      ⨍ y in ball x r, quadraticValue (Hm m y) v := by
    apply average_congr
    exact (ae_restrict_of_ae (hf m)).mono fun y hy ↦ by
      exact congrArg (fun M ↦ quadraticValue M v) hy
  simp_rw [he] at hlim
  exact hlim

lemma weak_quadratic_submean {n : Type u30} [Fintype n]
    {f : ℕ → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {w : Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {Hm : ℕ → (ℂ × ℂ) → Matrix n n ℂ}
    {Ω U : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hf : ∀ m, (fun x ↦ coefficientsToMatrix (f m x)) =ᵐ[volume] Hm m)
    (hw : ∀ v, Tendsto (fun m ↦ inner ℂ (f m) v) atTop (𝓝 (inner ℂ w v)))
    (hHm : ∀ m, Integrable (Hm m))
    (hp : ∀ m, DiskPshOn (Ω ×ˢ univ)
      (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2))
    {r : ℝ} (hr : 0 < r) (hb : ∀ x ∈ U, closedBall x r ⊆ Ω) (v : n → ℂ) :
    ∀ᵐ x ∂volume.restrict U,
      quadraticValue (coefficientsToMatrix (w x)) v ≤
        ⨍ y in ball x r, quadraticValue (coefficientsToMatrix (w y)) v := by
  have hall : ∀ m, ∀ᵐ x ∂volume.restrict U, coefficientsQuadraticCLM v (f m x) ≤
      ⨍ y in ball x r, coefficientsQuadraticCLM v (f m y) := by
    intro m
    have he (x : ℂ × ℂ) : (⨍ y in ball x r, coefficientsQuadraticCLM v (f m y)) =
        ⨍ y in ball x r, quadraticValue (Hm m y) v := by
      apply average_congr
      exact (ae_restrict_of_ae (hf m)).mono fun y hy ↦ by
        exact congrArg (fun M ↦ quadraticValue M v) hy
    have hbase : DiskPshOn Ω (fun x ↦ quadraticValue (Hm m x) v) :=
      (hp m).comp (f := fun x ↦ (x,v)) (by fun_prop) (fun _ hx ↦ ⟨hx, mem_univ _⟩)
    have hi : Integrable (fun x ↦ quadraticValue (Hm m x) v) :=
      (quadraticValueCLM v).integrable_comp (hHm m)
    filter_upwards [ae_restrict_mem hU.measurableSet, ae_restrict_of_ae (hf m)] with x hx hfx
    rw [coefficientsQuadraticCLM_apply, hfx, he]
    exact hbase.base_average_submean hΩ (hb x hx (mem_closedBall_self hr.le)) hr
      (hb x hx) hi.integrableOn
  have hs := ae_submean_of_weak_limit U (coefficientsQuadraticCLM v)
    (fun x ↦ ball x r) (fun _ ↦ measurableSet_ball) (fun _ ↦ measure_ball_lt_top.ne) hall hw
  simpa only [coefficientsQuadraticCLM_apply] using hs

local instance : (volume : Measure (ℂ × ℂ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume.prod volume : Measure (ℂ × ℂ)).IsAddHaarMeasure)

theorem weak_quadratic_psh_representative {n : Type u31} [Fintype n] [DecidableEq n]
    {f : ℕ → Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {w : Lp (EuclideanSpace ℂ (n × n)) 2 (volume : Measure (ℂ × ℂ))}
    {Hm : ℕ → (ℂ × ℂ) → Matrix n n ℂ}
    {Ω U : Set (ℂ × ℂ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (hf : ∀ m, (fun x ↦ coefficientsToMatrix (f m x)) =ᵐ[volume] Hm m)
    (hw : ∀ v, Tendsto (fun m ↦ inner ℂ (f m) v) atTop (𝓝 (inner ℂ w v)))
    (hwL1 : Integrable (fun x ↦ w x)) (hHm : ∀ m, Integrable (Hm m))
    (hposm : ∀ m, ∀ᵐ x ∂volume, (Hm m x).PosSemidef)
    (hc : ∀ m, ContinuousOn (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2)
      (Ω ×ˢ univ))
    (hp : ∀ m, DiskPshOn (Ω ×ˢ univ)
      (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (Hm m p.1) p.2))
    {C : ℝ} {r : ℕ → ℝ} (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (𝓝 0))
    (hb : ∀ k, ∀ x ∈ U, closedBall x (r k) ⊆ Ω)
    (hbound : ∀ m, ∀ x ∈ Ω, ∀ v, quadraticValue (Hm m x) v ≤ C * ‖v‖ ^ 2) :
    ∃ M : (ℂ × ℂ) → Matrix n n ℂ,
      (∀ x ∈ U, (M x).PosSemidef) ∧
      M =ᵐ[volume.restrict U] (fun x ↦ coefficientsToMatrix (w x)) ∧
      DiskPshOn (U ×ˢ univ)
        (fun p : (ℂ × ℂ) × (n → ℂ) ↦ quadraticValue (M p.1) p.2) := by
  have hH : Integrable (fun x ↦ coefficientsToMatrix (w x)) :=
    coefficientsToMatrix.toContinuousLinearMap.integrable_comp hwL1
  have hpos : ∀ᵐ x ∂volume, (coefficientsToMatrix (w x)).PosSemidef := by
    apply weak_coefficients_positive _ hw
    intro m
    filter_upwards [hf m, hposm m] with x hx hp
    rwa [hx]
  apply joint_matrix_regularized_representative hU hH hHm hpos hposm hc hp hr hr0
    _ hbound _ _
  · intro k a ha x hx
    apply hb k x hx
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using ha
  · intro k x _ v
    exact weak_quadratic_averages hf hw x (r k) v
  · intro v k
    exact weak_quadratic_submean hΩ hU hf hw hHm hp (hr k) (hb k) v

end QuadricCounterexample

end

end OAI
