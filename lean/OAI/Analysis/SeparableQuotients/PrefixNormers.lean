import OAI.Analysis.SeparableQuotients.AdjointSurjectivity

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped BigOperators Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

@[reducible] noncomputable local instance prefixDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance prefixDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

/-- Finite prefix normers for a zero-based sequence. The existential formulation is equivalent to a maximum over the finite set. -/
structure PrefixNormers (f : ℕ → StrongDual 𝕜 X) where
  D : ℕ → Finset X
  unit : ∀ m, ∀ d ∈ D m, ‖d‖ ≤ 1
  norming : ∀ m, 0 < m → ∀ c : ℕ → 𝕜, ∃ d ∈ D m,
    ‖∑ i ∈ Finset.range m, c i • f i‖ ≤ 2 * ‖(∑ i ∈ Finset.range m, c i • f i) d‖
  vanish : ∀ m n, m ≤ n → ∀ d ∈ D m, f n d = 0

namespace PrefixNormers

variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)

theorem prefix_evaluation (c : ℕ → 𝕜) {m N : ℕ} (hmN : m ≤ N)
    {d : X} (hd : d ∈ H.D m) :
    (∑ i ∈ Finset.range N, c i • f i) d = (∑ i ∈ Finset.range m, c i • f i) d := by
  simp only [sum_apply, smul_apply]
  symm
  apply Finset.sum_subset (Finset.range_mono hmN)
  intro i hiN him
  have hmi : m ≤ i := by simpa using him
  rw [H.vanish m i hmi d hd, smul_zero]

include H

theorem prefix_bound (c : ℕ → 𝕜) {m N : ℕ} (hmN : m ≤ N) :
    ‖∑ i ∈ Finset.range m, c i • f i‖ ≤ 2 * ‖∑ i ∈ Finset.range N, c i • f i‖ := by
  by_cases hm : m = 0
  · subst m; simp
  obtain ⟨d, hd, hb⟩ := H.norming m (Nat.pos_of_ne_zero hm) c
  rw [← H.prefix_evaluation c hmN hd] at hb
  apply hb.trans
  gcongr
  exact ((∑ i ∈ Finset.range N, c i • f i).le_opNorm d).trans
    (by
      simpa using mul_le_mul_of_nonneg_left (H.unit m d hd)
        (norm_nonneg (∑ i ∈ Finset.range N, c i • f i)))

theorem term_bound (c : ℕ → 𝕜) {n N : ℕ} (hn : n < N) :
    ‖c n • f n‖ ≤ 4 * ‖∑ i ∈ Finset.range N, c i • f i‖ := by
  have hp := H.prefix_bound c (Nat.succ_le_of_lt hn)
  have hq := H.prefix_bound c hn.le
  have he : c n • f n =
      (∑ i ∈ Finset.range (n + 1), c i • f i) - (∑ i ∈ Finset.range n, c i • f i) := by
    rw [Finset.sum_range_succ, add_sub_cancel_left]
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

theorem coefficient_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (c : ℕ → 𝕜) {n N : ℕ} (hn : n < N) :
    ‖c n‖ ≤ (4 / a) * ‖∑ i ∈ Finset.range N, c i • f i‖ := by
  have hb := H.term_bound c hn
  rw [norm_smul] at hb
  have hmul := mul_le_mul_of_nonneg_left (hf n) (norm_nonneg (c n))
  have he : 4 * ‖∑ i ∈ Finset.range N, c i • f i‖ / a =
      (4 / a) * ‖∑ i ∈ Finset.range N, c i • f i‖ := by ring
  rw [← he]
  exact (le_div_iff₀ ha).mpr (hmul.trans hb)

theorem finsupp_coefficient_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (c : ℕ →₀ 𝕜) (n : ℕ) :
    ‖c n‖ ≤ (4 / a) * ‖Finsupp.linearCombination 𝕜 f c‖ := by
  classical
  obtain ⟨N, hN⟩ := (insert n c.support).exists_nat_subset_range
  have hsum : (∑ i ∈ Finset.range N, c i • f i) =
      Finsupp.linearCombination 𝕜 f c := by
    change (∑ i ∈ Finset.range N, c i • f i) = ∑ i ∈ c.support, c i • f i
    symm
    apply Finset.sum_subset (fun i hi => hN (Finset.mem_insert_of_mem hi))
    intro i _ hi
    rw [Finsupp.notMem_support_iff.mp hi, zero_smul]
  rw [← hsum]
  exact H.coefficient_bound a ha hf c (Finset.mem_range.mp (hN (Finset.mem_insert_self _ _)))

theorem linearIndependent (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    LinearIndependent 𝕜 f := by
  rw [linearIndependent_iff]
  intro c hc
  ext n
  have h := H.finsupp_coefficient_bound a ha hf c n
  rw [hc, norm_zero, mul_zero] at h
  simpa using norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

/-- Bounded algebraic coordinate functionals. -/
noncomputable def spanCoord (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n : ℕ) :
    StrongDual 𝕜 (Submodule.span 𝕜 (Set.range f)) :=
  LinearMap.mkContinuous ((Finsupp.lapply (R := 𝕜) (M := 𝕜) n).comp (H.linearIndependent a ha hf).repr)
    (4 / a) (fun x => by
      have h := H.finsupp_coefficient_bound a ha hf
        ((H.linearIndependent a ha hf).repr x) n
      rw [LinearIndependent.linearCombination_repr] at h
      exact h)

theorem spanCoord_norm (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n : ℕ) :
    ‖H.spanCoord a ha hf n‖ ≤ 4 / a := by
  apply LinearMap.mkContinuous_norm_le
  exact div_nonneg (by norm_num) ha.le

theorem spanCoord_basis (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n j : ℕ) :
    H.spanCoord a ha hf n ⟨f j, Submodule.subset_span (Set.mem_range_self j)⟩ =
      if j = n then 1 else 0 := by
  change (H.linearIndependent a ha hf).repr _ n = _
  rw [LinearIndependent.repr_eq_single _ j _ rfl]
  simp [Finsupp.single_apply]

/-- Hahn--Banach extension of each coordinate; restrictions to the closed span are canonical. -/
theorem exists_ambientCoord (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    ∃ e : ℕ → StrongDual 𝕜 (StrongDual 𝕜 X),
      (∀ n, ‖e n‖ ≤ 4 / a) ∧ (∀ n, ∀ x : Submodule.span 𝕜 (Set.range f),
        e n x = H.spanCoord a ha hf n x) := by
  have he (n : ℕ) := exists_extension_norm_eq (Submodule.span 𝕜 (Set.range f))
    (H.spanCoord a ha hf n)
  choose e he hnorm using he
  exact ⟨e, fun n => (hnorm n).trans_le (H.spanCoord_norm a ha hf n), he⟩

omit H in
lemma linearCombination_eq_sum_range (c : ℕ →₀ 𝕜) {N : ℕ}
    (hN : c.support ⊆ Finset.range N) :
    Finsupp.linearCombination 𝕜 f c = ∑ i ∈ Finset.range N, c i • f i := by
  classical
  change (∑ i ∈ c.support, c i • f i) = _
  apply Finset.sum_subset hN
  intro i _ hi
  rw [Finsupp.notMem_support_iff.mp hi, zero_smul]

/-- The closed linear span of the sequence. -/
def closedSpan (f : ℕ → StrongDual 𝕜 X) : Submodule 𝕜 (StrongDual 𝕜 X) :=
  (Submodule.span 𝕜 (Set.range f)).topologicalClosure

noncomputable def ambientCoord (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    ℕ → StrongDual 𝕜 (StrongDual 𝕜 X) :=
  Classical.choose (H.exists_ambientCoord a ha hf)

lemma ambientCoord_spec (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    (∀ n, ‖H.ambientCoord a ha hf n‖ ≤ 4 / a) ∧
    (∀ n, ∀ x : Submodule.span 𝕜 (Set.range f),
      H.ambientCoord a ha hf n x = H.spanCoord a ha hf n x) :=
  Classical.choose_spec (H.exists_ambientCoord a ha hf)

noncomputable def ambientPrefix (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (m : ℕ) : StrongDual 𝕜 X →L[𝕜] StrongDual 𝕜 X :=
  ∑ i ∈ Finset.range m, (H.ambientCoord a ha hf i).smulRight (f i)

lemma ambientPrefix_apply_span (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (m : ℕ) (x : Submodule.span 𝕜 (Set.range f)) :
    H.ambientPrefix a ha hf m x =
      ∑ i ∈ Finset.range m, (H.linearIndependent a ha hf).repr x i • f i := by
  simp only [ambientPrefix, sum_apply, ContinuousLinearMap.smulRight_apply,
    (H.ambientCoord_spec a ha hf).2]
  rfl

lemma ambientPrefix_bound_span (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (m : ℕ) (x : Submodule.span 𝕜 (Set.range f)) :
    ‖H.ambientPrefix a ha hf m x‖ ≤ 2 * ‖x‖ := by
  let c := (H.linearIndependent a ha hf).repr x
  obtain ⟨N, hN⟩ := c.support.exists_nat_subset_range
  have hm : m ≤ max m N := le_max_left _ _
  have hN' : c.support ⊆ Finset.range (max m N) :=
    hN.trans (Finset.range_mono (le_max_right _ _))
  have he : (x : StrongDual 𝕜 X) = ∑ i ∈ Finset.range (max m N), c i • f i := by
    rw [← linearCombination_eq_sum_range c hN']
    exact (H.linearIndependent a ha hf).linearCombination_repr x |>.symm
  rw [ambientPrefix_apply_span]
  change ‖∑ i ∈ Finset.range m, c i • f i‖ ≤ 2 * ‖(x : StrongDual 𝕜 X)‖
  rw [he]
  exact H.prefix_bound c hm

lemma ambientPrefix_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (m : ℕ) (x : closedSpan f) :
    ‖H.ambientPrefix a ha hf m x‖ ≤ 2 * ‖x‖ := by
  have hc : IsClosed {x : StrongDual 𝕜 X |
      ‖H.ambientPrefix a ha hf m x‖ ≤ 2 * ‖x‖} :=
    isClosed_le (H.ambientPrefix a ha hf m).continuous.norm (continuous_const.mul continuous_norm)
  exact closure_minimal (fun x hx => H.ambientPrefix_bound_span a ha hf m ⟨x, hx⟩)
    hc x.property

lemma ambientPrefix_eventually_span (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (x : Submodule.span 𝕜 (Set.range f)) :
    ∀ᶠ m in Filter.atTop, H.ambientPrefix a ha hf m x = (x : StrongDual 𝕜 X) := by
  let c := (H.linearIndependent a ha hf).repr x
  obtain ⟨N, hN⟩ := c.support.exists_nat_subset_range
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  rw [ambientPrefix_apply_span, ← linearCombination_eq_sum_range c
    (hN.trans (Finset.range_mono hm))]
  exact (H.linearIndependent a ha hf).linearCombination_repr x

lemma ambientPrefix_tendsto (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (x : closedSpan f) :
    Filter.Tendsto (fun m => H.ambientPrefix a ha hf m x) Filter.atTop
      (𝓝 (x : StrongDual 𝕜 X)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp x.property (ε / 4) (by positivity)
  let yc : closedSpan f := ⟨y, Submodule.le_topologicalClosure _ hy⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (H.ambientPrefix_eventually_span a ha hf ⟨y, hy⟩)
  refine ⟨N, fun m hm => ?_⟩
  have he := hN m hm
  have hb := H.ambientPrefix_bound a ha hf m (x - yc)
  change ‖H.ambientPrefix a ha hf m ((x : StrongDual 𝕜 X) - y)‖ ≤
    2 * ‖(x : StrongDual 𝕜 X) - y‖ at hb
  rw [map_sub, he] at hb
  rw [dist_eq_norm] at hxy ⊢
  calc
    ‖H.ambientPrefix a ha hf m x - (x : StrongDual 𝕜 X)‖ ≤
        ‖H.ambientPrefix a ha hf m x - y‖ + ‖y - (x : StrongDual 𝕜 X)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖(x : StrongDual 𝕜 X) - y‖ + ‖y - (x : StrongDual 𝕜 X)‖ :=
      add_le_add hb le_rfl
    _ < ε := by rw [norm_sub_rev y]; linarith

omit H in
noncomputable def basisVector (f : ℕ → StrongDual 𝕜 X) (n : ℕ) : closedSpan f :=
  ⟨f n, Submodule.le_topologicalClosure _ (Submodule.subset_span (Set.mem_range_self n))⟩

noncomputable def coord (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n : ℕ) :
    StrongDual 𝕜 (closedSpan f) :=
  (H.ambientCoord a ha hf n).comp (closedSpan f).subtypeL

lemma coord_norm (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n : ℕ) :
    ‖H.coord a ha hf n‖ ≤ 4 / a := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  exact ((H.ambientCoord a ha hf n).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right ((H.ambientCoord_spec a ha hf).1 n) (norm_nonneg _))

lemma coord_basis (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n j : ℕ) :
    H.coord a ha hf n (basisVector f j) = if j = n then 1 else 0 := by
  change H.ambientCoord a ha hf n (f j) = _
  rw [(H.ambientCoord_spec a ha hf).2 n ⟨f j, Submodule.subset_span (Set.mem_range_self j)⟩]
  exact H.spanCoord_basis a ha hf n j

noncomputable def prefixOp (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (m : ℕ) :
    closedSpan f →L[𝕜] closedSpan f :=
  ∑ i ∈ Finset.range m, (H.coord a ha hf i).smulRight (basisVector f i)

lemma prefix_coe (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (m : ℕ) (x : closedSpan f) :
    (H.prefixOp a ha hf m x : StrongDual 𝕜 X) = H.ambientPrefix a ha hf m x := by
  simp [prefixOp, ambientPrefix, coord, basisVector]

lemma prefix_norm (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (m : ℕ) :
    ‖H.prefixOp a ha hf m‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖(H.prefixOp a ha hf m x : StrongDual 𝕜 X)‖ ≤ 2 * ‖x‖
  rw [prefix_coe]
  exact H.ambientPrefix_bound a ha hf m x

lemma prefix_tendsto (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (x : closedSpan f) :
    Filter.Tendsto (fun m => H.prefixOp a ha hf m x) Filter.atTop (𝓝 x) := by
  apply tendsto_subtype_rng.mpr
  simpa only [prefix_coe] using H.ambientPrefix_tendsto a ha hf x

/-- Finite prefix normers yield a basic sequence. -/
noncomputable def schauderBasis (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    SchauderBasis 𝕜 (closedSpan f) where
  basis := basisVector f
  coord := H.coord a ha hf
  ortho i j := by
    classical
    rw [H.coord_basis a ha hf i j]
    by_cases h : i = j
    · subst j; simp
    · simp [h, Ne.symm h]
  expansion x := by
    change Filter.Tendsto (fun s : Finset ℕ => ∑ i ∈ s,
      H.coord a ha hf i x • basisVector f i) (SummationFilter.conditional ℕ).filter (𝓝 x)
    rw [SummationFilter.conditional_filter_eq_map_range, Filter.tendsto_map'_iff]
    simpa only [Function.comp_def, prefixOp, sum_apply, ContinuousLinearMap.smulRight_apply]
      using H.prefix_tendsto a ha hf x

@[reducible] noncomputable local instance closedDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 (closedSpan f)) := inferInstance
@[reducible] noncomputable local instance closedDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (closedSpan f)) := inferInstance

/-- Evaluation on the closed span `G`. -/
noncomputable def evaluation (f : ℕ → StrongDual 𝕜 X) :
    X →L[𝕜] StrongDual 𝕜 (closedSpan f) :=
  (ContinuousLinearMap.precomp 𝕜 (closedSpan f).subtypeL).comp
    (NormedSpace.inclusionInDoubleDual 𝕜 X)

omit H in
@[simp] lemma evaluation_apply (x : X) (v : closedSpan f) :
    evaluation f x v = (v : StrongDual 𝕜 X) x := rfl

lemma ambientCoord_basis (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) (n j : ℕ) :
    H.ambientCoord a ha hf n (f j) = if j = n then 1 else 0 :=
  H.coord_basis a ha hf n j

lemma evaluation_normer (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    {m : ℕ} {d : X} (hd : d ∈ H.D m) :
    evaluation f d = ∑ i ∈ Finset.range m, f i d • H.coord a ha hf i := by
  classical
  have heq : Set.EqOn (NormedSpace.inclusionInDoubleDual 𝕜 X d)
      (∑ i ∈ Finset.range m, f i d • H.ambientCoord a ha hf i :
        StrongDual 𝕜 (StrongDual 𝕜 X))
      (closure (Submodule.span 𝕜 (Set.range f) : Set (StrongDual 𝕜 X))) := by
    apply ContinuousLinearMap.eqOn_closure_span
    rintro _ ⟨n, rfl⟩
    change f n d = _
    simp only [sum_apply, smul_apply, H.ambientCoord_basis, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    by_cases hn : n < m
    · simp [hn]
    · simp [hn, H.vanish m n (Nat.le_of_not_gt hn) d hd]
  ext v
  have hv := heq v.property
  change (v : StrongDual 𝕜 X) d = _ at hv
  simpa only [evaluation_apply, sum_apply, smul_apply, coord,
    ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply] using hv

/-- The coefficient vectors used in the adjoint bound. -/
noncomputable def adjointVector (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (m : ℕ) : closedSpan f :=
  ∑ i ∈ Finset.range m, h (H.coord a ha hf i) • basisVector f i

lemma adjointVector_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (m : ℕ) :
    ‖H.adjointVector a ha hf h m‖ ≤ 2 * ‖h.comp (evaluation f)‖ := by
  classical
  by_cases hm : m = 0
  · subst m; simp [adjointVector]
  obtain ⟨d, hd, hb⟩ := H.norming m (Nat.pos_of_ne_zero hm)
    (fun n => h (H.coord a ha hf n))
  have he : (h.comp (evaluation f)) d =
      (∑ i ∈ Finset.range m, h (H.coord a ha hf i) • f i) d := by
    rw [ContinuousLinearMap.comp_apply, H.evaluation_normer a ha hf hd]
    simp [smul_eq_mul, mul_comm]
  rw [← he] at hb
  have hn := (h.comp (evaluation f)).le_opNorm d
  have hu : ‖(h.comp (evaluation f)) d‖ ≤ ‖h.comp (evaluation f)‖ :=
    hn.trans (by
      simpa using mul_le_mul_of_nonneg_left (H.unit m d hd)
        (norm_nonneg (h.comp (evaluation f))))
  have hle := hb.trans (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2))
  change ‖(H.adjointVector a ha hf h m : StrongDual 𝕜 X)‖ ≤ _
  simpa only [adjointVector, Submodule.coe_sum, Submodule.coe_smul, basisVector] using hle

lemma coord_adjointVector (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (m n : ℕ) :
    H.coord a ha hf n (H.adjointVector a ha hf h m) =
      if n < m then h (H.coord a ha hf n) else 0 := by
  classical
  simp [adjointVector, H.coord_basis, smul_eq_mul, mul_ite]

lemma linearCombination_adjointVector (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (c : ℕ →₀ 𝕜)
    {m : ℕ} (hm : c.support ⊆ Finset.range m) :
    (Finsupp.linearCombination 𝕜 (H.coord a ha hf) c) (H.adjointVector a ha hf h m) =
      h (Finsupp.linearCombination 𝕜 (H.coord a ha hf) c) := by
  classical
  change (∑ i ∈ c.support, c i • H.coord a ha hf i) (H.adjointVector a ha hf h m) =
    h (∑ i ∈ c.support, c i • H.coord a ha hf i)
  simp only [sum_apply, smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [H.coord_adjointVector, ite_eq_left (Finset.mem_range.mp (hm hi))]

/-- The closed coefficient span `Z`. -/
noncomputable def coefficientSpan (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    Submodule 𝕜 (StrongDual 𝕜 (closedSpan f)) :=
  (Submodule.span 𝕜 (Set.range (H.coord a ha hf))).topologicalClosure

lemma adjoint_bound_on_coefficientSpan (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (h : StrongDual 𝕜 (StrongDual 𝕜 (closedSpan f))) (u : H.coefficientSpan a ha hf) :
    ‖h u‖ ≤ (2 * ‖h.comp (evaluation f)‖) * ‖u‖ := by
  have hc : IsClosed {u : StrongDual 𝕜 (closedSpan f) |
      ‖h u‖ ≤ (2 * ‖h.comp (evaluation f)‖) * ‖u‖} :=
    isClosed_le h.continuous.norm (continuous_const.mul continuous_norm)
  apply closure_minimal (t := {u | ‖h u‖ ≤ (2 * ‖h.comp (evaluation f)‖) * ‖u‖})
    (fun u hu => ?_) hc u.property
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hu
  obtain ⟨m, hm⟩ := c.support.exists_nat_subset_range
  change ‖h (Finsupp.linearCombination 𝕜 (H.coord a ha hf) c)‖ ≤
    (2 * ‖h.comp (evaluation f)‖) * ‖Finsupp.linearCombination 𝕜 (H.coord a ha hf) c‖
  rw [← H.linearCombination_adjointVector a ha hf h c hm]
  exact ((Finsupp.linearCombination 𝕜 (H.coord a ha hf) c).le_opNorm _).trans
    (by
      rw [mul_comm (2 * _)]
      exact mul_le_mul_of_nonneg_left (H.adjointVector_bound a ha hf h m) (norm_nonneg _))

/-- Evaluation with codomain the closed coefficient span. -/
noncomputable def evaluationToZ (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (hZ : ∀ x, evaluation f x ∈ H.coefficientSpan a ha hf) :
    X →L[𝕜] H.coefficientSpan a ha hf :=
  (evaluation f).codRestrict (H.coefficientSpan a ha hf) hZ

lemma evaluationToZ_adjoint_bound (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (hZ : ∀ x, evaluation f x ∈ H.coefficientSpan a ha hf)
    (h : StrongDual 𝕜 (H.coefficientSpan a ha hf)) :
    (1 / 2 : ℝ) * ‖h‖ ≤ ‖h.comp (H.evaluationToZ a ha hf hZ)‖ := by
  obtain ⟨h', he, _⟩ := exists_extension_norm_eq (H.coefficientSpan a ha hf) h
  have hcomp : h'.comp (evaluation f) = h.comp (H.evaluationToZ a ha hf hZ) := by
    ext x
    exact he (H.evaluationToZ a ha hf hZ x)
  have hb : ‖h‖ ≤ 2 * ‖h.comp (H.evaluationToZ a ha hf hZ)‖ := by
    apply h.opNorm_le_bound (mul_nonneg (by norm_num) (norm_nonneg _))
    intro u
    rw [← he u]
    simpa only [hcomp] using H.adjoint_bound_on_coefficientSpan a ha hf h' u
  linarith

/-- Coefficients are linearly independent, so their closed span is infinite dimensional. -/
lemma coord_linearIndependent (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    LinearIndependent 𝕜 (H.coord a ha hf) := by
  classical
  refine linearIndependent_iff.mpr fun c hc => c.ext fun n => ?_
  have he := congrArg (fun u : StrongDual 𝕜 (closedSpan f) => u (basisVector f n)) hc
  simpa [Finsupp.linearCombination_apply, Finsupp.sum, H.coord_basis,
    smul_eq_mul, mul_ite] using he

noncomputable def coefficientVector (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (n : ℕ) : H.coefficientSpan a ha hf :=
  ⟨H.coord a ha hf n, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self n))⟩

lemma coefficientVector_linearIndependent (a : ℝ) (ha : 0 < a)
    (hf : ∀ n, a ≤ ‖f n‖) : LinearIndependent 𝕜 (H.coefficientVector a ha hf) :=
  LinearIndependent.of_comp (H.coefficientSpan a ha hf).subtype
    (H.coord_linearIndependent a ha hf)

lemma coefficientSpan_infiniteDimensional (a : ℝ) (ha : 0 < a)
    (hf : ∀ n, a ≤ ‖f n‖) : ¬ FiniteDimensional 𝕜 (H.coefficientSpan a ha hf) := by
  intro h
  let := h
  exact Module.Finite.not_linearIndependent_of_infinite (H.coefficientVector a ha hf)
    (H.coefficientVector_linearIndependent a ha hf)

lemma coefficientSpan_isClosed (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    IsClosed (H.coefficientSpan a ha hf : Set (StrongDual 𝕜 (closedSpan f))) :=
  (Submodule.span 𝕜 (Set.range (H.coord a ha hf))).isClosed_topologicalClosure

lemma coefficientSpan_separable (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖) :
    TopologicalSpace.SeparableSpace (H.coefficientSpan a ha hf) := by
  have hs := ((Set.countable_range (H.coord a ha hf)).isSeparable.span (R := 𝕜)).closure
  exact hs.separableSpace

end PrefixNormers
end SeparableQuotient

namespace SeparableQuotient
namespace PrefixNormers
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {f : ℕ → StrongDual 𝕜 X} (H : PrefixNormers f)
@[reducible] noncomputable local instance outcomeDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance outcomeDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance outcomeClosedDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 (closedSpan f)) := inferInstance
@[reducible] noncomputable local instance outcomeClosedDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (closedSpan f)) := inferInstance

/-- The adjoint lower bound implies surjectivity of evaluation. -/
theorem evaluationToZ_surjective (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (hZ : ∀ x, evaluation f x ∈ H.coefficientSpan a ha hf) :
    Function.Surjective (H.evaluationToZ a ha hf hZ) :=
  surjective_of_adjoint_bound_rclike (𝕜 := 𝕜) (E := X)
    (F := H.coefficientSpan a ha hf) (H.evaluationToZ a ha hf hZ) (1 / 2)
    (by norm_num) (H.evaluationToZ_adjoint_bound a ha hf hZ)

/-- Finite prefix normers yield a separable quotient. -/
theorem hasSeparableQuotient_of_range (a : ℝ) (ha : 0 < a) (hf : ∀ n, a ≤ ‖f n‖)
    (hZ : ∀ x, evaluation f x ∈ H.coefficientSpan a ha hf) : HasSeparableQuotient 𝕜 X := by
  let : IsClosed (H.coefficientSpan a ha hf : Set (StrongDual 𝕜 (closedSpan f))) :=
    H.coefficientSpan_isClosed a ha hf
  refine ⟨H.coefficientSpan a ha hf, inferInstance, inferInstance, inferInstance,
    H.coefficientSpan_separable a ha hf, H.coefficientSpan_infiniteDimensional a ha hf,
    H.evaluationToZ a ha hf hZ, H.evaluationToZ_surjective a ha hf hZ⟩

end PrefixNormers
end SeparableQuotient

end OAI
