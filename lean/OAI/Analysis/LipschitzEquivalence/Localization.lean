import OAI.Analysis.LipschitzEquivalence.GraphObstruction

namespace OAI

universe uM uV

noncomputable section
namespace LipschitzCounterexample

namespace LocalizedLinearization
open Filter Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

omit [Zero M] in
theorem lipschitz_sub_const {V : Type uV} [NormedAddCommGroup V] (f : M → V)
    {K : ℝ≥0} (hf : LipschitzWith K f) (c : V) :
    LipschitzWith K (fun x => f x - c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_sub_right] using hf.dist_le_mul x y

omit [Zero M] in
theorem lipschitz_const_sub {V : Type uV} [NormedAddCommGroup V] (f : M → V)
    {K : ℝ≥0} (hf : LipschitzWith K f) (c : V) :
    LipschitzWith K (fun x => c - f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_sub_left] using hf.dist_le_mul x y

def normalized (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) : FreeSpace.LipZero M :=
  ⟨fun x => f x - f 0, ⟨by simp, C, by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y⟩⟩

def test (f : FreeSpace.LipZero M) : FreeSpace.Space M →L[ℝ] ℝ :=
  ({ toFun := fun μ => FreeSpace.inclusion μ f
     map_add' := by intro μ ν; rfl
     map_smul' := by intro c μ; rfl } : FreeSpace.Space M →ₗ[ℝ] ℝ).mkContinuous
    ‖f‖ (by
      intro μ
      change ‖μ.1 f‖ ≤ ‖f‖ * ‖μ.1‖
      simpa only [mul_comm] using μ.1.le_opNorm f)

@[simp] theorem test_point (f : FreeSpace.LipZero M) (x : M) :
    test f (FreeSpace.point x) = f.1 x := rfl

theorem norm_test_apply_le (f : FreeSpace.LipZero M) (μ : FreeSpace.Space M) :
    ‖test f μ‖ ≤ ‖f‖ * ‖μ‖ := by
  change ‖μ.1 f‖ ≤ ‖f‖ * ‖μ.1‖
  simpa only [mul_comm] using μ.1.le_opNorm f

theorem norm_normalized_le (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) :
    ‖normalized f hf‖ ≤ C := FreeSpace.norm_le_of_lipschitz _ (by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [normalized, Real.dist_eq, sub_sub_sub_cancel_right] using hf.dist_le_mul x y)

def cutoff (z : M) (s : ℝ≥0) (x : M) : ℝ :=
  max 0 (min 1 (2 - (2 / (s : ℝ)) * dist x z))

omit [Zero M] in
theorem cutoff_nonneg (z : M) (s : ℝ≥0) (x : M) : 0 ≤ cutoff z s x := le_max_left _ _
omit [Zero M] in
theorem cutoff_le_one (z : M) (s : ℝ≥0) (x : M) : cutoff z s x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

omit [Zero M] in
theorem cutoff_zero (z : M) {s : ℝ≥0} (hs : 0 < s) {x : M} (hx : (s : ℝ) ≤ dist x z) :
    cutoff z s x = 0 := by
  have hs' : 0 < (s : ℝ) := hs
  have hmul : 2 ≤ (2 / (s : ℝ)) * dist x z := by
    calc
      2 = (2 / (s : ℝ)) * s := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

omit [Zero M] in
theorem cutoff_one (z : M) {s : ℝ≥0} (hs : 0 < s) {x : M} (hx : dist x z ≤ s / 2) :
    cutoff z s x = 1 := by
  have hs' : 0 < (s : ℝ) := hs
  have hmul : (2 / (s : ℝ)) * dist x z ≤ 1 := by
    calc
      _ ≤ (2 / (s : ℝ)) * ((s : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ = 1 := by field_simp
  unfold cutoff
  rw [min_eq_left (by linarith)]
  norm_num

omit [Zero M] in
theorem cutoff_lipschitz (z : M) (s : ℝ≥0) : LipschitzWith (2 / s) (cutoff z s) := by
  have h : LipschitzWith (2 / s) (fun x : M => 2 - (2 / (s : ℝ)) * dist x z) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    calc
      |(2 - 2 / (s : ℝ) * dist x z) - (2 - 2 / (s : ℝ) * dist y z)| =
          (2 / (s : ℝ)) * |dist x z - dist y z| := by
            rw [show (2 - 2 / (s : ℝ) * dist x z) - (2 - 2 / (s : ℝ) * dist y z) =
              -(2 / (s : ℝ) * (dist x z - dist y z)) by ring,
              abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / (s : ℝ))]
      _ ≤ (2 / (s : ℝ)) * dist x y := mul_le_mul_of_nonneg_left (abs_dist_sub_le x y z) (by positivity)
      _ = _ := by simp
  exact (h.const_min 1).const_max 0

omit [Zero M] in

theorem product_lipschitz (z : M) {s : ℝ≥0} (hs : 0 < s)
    (f ψ : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) (hfz : f z = 0)
    (hψ : LipschitzWith (2 / s) ψ) (hb : ∀ x, |ψ x| ≤ 1)
    (hv : ∀ x y, ψ x ≠ ψ y → dist x z < s ∨ dist y z < s) :
    LipschitzWith (3 * C) (fun x => f x * ψ x) := by
  have hs' : 0 < (s : ℝ) := hs
  have hfbound (x : M) (hx : dist x z < s) : |f x| ≤ C * s := by
    have h := hf.dist_le_mul x z
    rw [hfz, dist_zero_right, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left hx.le C.coe_nonneg)
  have hsmall (x y : M) (hx : dist x z < s) :
      |f x * ψ x - f y * ψ y| ≤ (3 * (C : ℝ)) * dist x y := by
    have hfxy : |f x - f y| ≤ C * dist x y := hf.dist_le_mul x y
    have hψxy : |ψ x - ψ y| ≤ (2 / (s : ℝ)) * dist x y := hψ.dist_le_mul x y
    calc
      |f x * ψ x - f y * ψ y| = |ψ y * (f x - f y) + f x * (ψ x - ψ y)| := by congr 1; ring
      _ ≤ |ψ y * (f x - f y)| + |f x * (ψ x - ψ y)| := abs_add_le _ _
      _ = |ψ y| * |f x - f y| + |f x| * |ψ x - ψ y| := by rw [abs_mul, abs_mul]
      _ ≤ 1 * (C * dist x y) + (C * s) * ((2 / (s : ℝ)) * dist x y) :=
        add_le_add (mul_le_mul (hb y) hfxy (abs_nonneg _) (by norm_num))
          (mul_le_mul (hfbound x hx) hψxy (abs_nonneg _) (by positivity))
      _ = (3 * (C : ℝ)) * dist x y := by field_simp; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_mul, NNReal.coe_ofNat]
  by_cases heq : ψ x = ψ y
  · rw [← heq, ← sub_mul, abs_mul]
    have hxy : |f x - f y| ≤ C * dist x y := hf.dist_le_mul x y
    calc
      _ ≤ (C * dist x y) * 1 := mul_le_mul hxy (hb x) (abs_nonneg _) (by positivity)
      _ ≤ 3 * (C : ℝ) * dist x y := by nlinarith [C.coe_nonneg, dist_nonneg (x := x) (y := y)]
  · rcases hv x y heq with hx | hy
    · exact hsmall x y hx
    · simpa only [abs_sub_comm, dist_comm] using hsmall y x hy

omit [Zero M] in
theorem cutoff_product_lipschitz (z : M) {s : ℝ≥0} (hs : 0 < s)
    (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) (hfz : f z = 0) :
    LipschitzWith (3 * C) (fun x => f x * cutoff z s x) := by
  apply product_lipschitz z hs f _ hf hfz (cutoff_lipschitz z s)
  · intro x
    rw [abs_of_nonneg (cutoff_nonneg z s x)]
    exact cutoff_le_one z s x
  · intro x y h
    by_contra! hc
    exact h ((cutoff_zero z hs hc.1).trans (cutoff_zero z hs hc.2).symm)

omit [Zero M] in
theorem annular_product_lipschitz (z : M) {s : ℝ≥0} (hs : 0 < s)
    (f : M → ℝ) {C : ℝ≥0} (hf : LipschitzWith C f) (hfz : f z = 0) :
    LipschitzWith (3 * C) (fun x => f x * (1 - cutoff z s x)) := by
  apply product_lipschitz z hs f _ hf hfz
  · exact lipschitz_const_sub _ (cutoff_lipschitz z s) 1
  · intro x
    rw [abs_of_nonneg (sub_nonneg.mpr (cutoff_le_one z s x))]
    linarith [cutoff_nonneg z s x]
  · intro x y h
    by_contra! hc
    exact h (by rw [cutoff_zero z hs hc.1, cutoff_zero z hs hc.2])

def DisjointTests (h : ℕ → M → ℝ) : Prop :=
  ∀ x i j, h i x ≠ 0 → h j x ≠ 0 → i = j

omit [Zero M] [MetricSpace M] in
theorem DisjointTests.exists_index {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) :
    ∃ i, ∀ j, j ≠ i → h j x = 0 := by
  classical
  by_cases he : ∃ i, h i x ≠ 0
  · obtain ⟨i, hi⟩ := he
    exact ⟨i, fun j hj => by by_contra hh; exact hj (hd x j i hh hi)⟩
  · push Not at he
    exact ⟨0, fun j _ => he j⟩

noncomputable def activeIndex {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) : ℕ :=
  (hd.exists_index x).choose

omit [Zero M] [MetricSpace M] in
theorem activeIndex_spec {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) :
    ∀ j, j ≠ activeIndex hd x → h j x = 0 := (hd.exists_index x).choose_spec

noncomputable def disjointMap {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) :
    WeakSequences.RealL1 := lp.single 1 (activeIndex hd x) (h (activeIndex hd x) x)

omit [Zero M] [MetricSpace M] in
theorem disjointMap_apply {h : ℕ → M → ℝ} (hd : DisjointTests h) (x : M) (i : ℕ) :
    disjointMap hd x i = h i x := by
  classical
  by_cases hi : i = activeIndex hd x
  · subst i
    simp [disjointMap]
  · simp [disjointMap, lp.single_apply, hi, activeIndex_spec hd x i hi]

omit [Zero M] in
theorem disjointMap_lipschitz {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) :
    LipschitzWith (2 * K) (disjointMap hd) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  by_cases hi : activeIndex hd x = activeIndex hd y
  · unfold disjointMap
    rw [← hi, ← lp.single_sub, lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
    calc
      ‖h (activeIndex hd x) x - h (activeIndex hd x) y‖ ≤ K * dist x y :=
        (hh _).dist_le_mul x y
      _ ≤ (2 * K : ℝ≥0) * dist x y := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        nlinarith [K.coe_nonneg, dist_nonneg (x := x) (y := y)]
  · have hxy := activeIndex_spec hd y (activeIndex hd x) hi
    have hyx := activeIndex_spec hd x (activeIndex hd y) (Ne.symm hi)
    have hx : ‖disjointMap hd x‖ ≤ K * dist x y := by
      rw [disjointMap, lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
      simpa only [hxy, dist_zero_right] using (hh (activeIndex hd x)).dist_le_mul x y
    have hy : ‖disjointMap hd y‖ ≤ K * dist x y := by
      rw [disjointMap, lp.norm_single (by norm_num : 0 < (1 : ℝ≥0∞))]
      have ht := (hh (activeIndex hd y)).dist_le_mul y x
      rw [hyx, dist_zero_right, dist_comm] at ht
      exact ht
    calc
      _ ≤ ‖disjointMap hd x‖ + ‖disjointMap hd y‖ := norm_sub_le _ _
      _ ≤ (2 * K : ℝ≥0) * dist x y := by
        simp only [NNReal.coe_mul, NNReal.coe_ofNat]
        linarith

noncomputable def disjointOperator {h : ℕ → M → ℝ} (hd : DisjointTests h) :
    FreeSpace.Space M →L[ℝ] WeakSequences.RealL1 :=
  FreeSpace.linearize (fun x => disjointMap hd x - disjointMap hd 0)

theorem disjointOperator_point {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) (x : M) :
    disjointOperator hd (FreeSpace.point x) = disjointMap hd x - disjointMap hd 0 := by
  apply FreeSpace.linearize_point _ (lipschitz_sub_const _ (disjointMap_lipschitz hd hh) _)
  simp

theorem disjointOperator_coord {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) (μ : FreeSpace.Space M) (i : ℕ) :
    disjointOperator hd μ i = test (normalized (h i) (hh i)) μ := by
  have eqc : (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i).comp (disjointOperator hd) =
      test (normalized (h i) (hh i)) := by
    have h₁ := FreeSpace.linearize_unique (fun x => h i x - h i 0)
      (lipschitz_sub_const _ (hh i) _) (by simp)
      ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 i).comp (disjointOperator hd))
      (by intro x; simp only [ContinuousLinearMap.comp_apply, disjointOperator_point hd hh]
          change (disjointMap hd x) i - (disjointMap hd 0) i = _
          rw [disjointMap_apply, disjointMap_apply])
    have h₂ := FreeSpace.linearize_unique (fun x => h i x - h i 0)
      (lipschitz_sub_const _ (hh i) _) (by simp) (test (normalized (h i) (hh i))) (fun x => rfl)
    exact h₁.symm.trans h₂
  exact congrArg (fun T : FreeSpace.Space M →L[ℝ] ℝ => T μ) eqc

theorem disjoint_tests_vanish {h : ℕ → M → ℝ} (hd : DisjointTests h)
    {K : ℝ≥0} (hh : ∀ i, LipschitzWith K (h i)) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) :
    Tendsto (fun i => test (normalized (h i) (hh i)) (μ i)) atTop (𝓝 0) := by
  have hn := WeakSequences.schur (hw.map (disjointOperator hd))
  apply squeeze_zero_norm (fun i => ?_) (by simpa only [norm_zero] using hn.norm)
  rw [← disjointOperator_coord hd hh]
  exact lp.norm_apply_le_norm (by norm_num) _ _

omit [Zero M] in
theorem finite_avoid_radius (z : M) (A : Finset M) {r : ℝ} (hr : 0 < r) :
    ∃ s : ℝ, 0 < s ∧ s < r ∧ ∀ x ∈ A, x ≠ z → s ≤ dist x z := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨r / 2, half_pos hr, half_lt_self hr, by simp⟩
  | @insert x A hx ih =>
      obtain ⟨s, hs, hsr, hA⟩ := ih
      by_cases hxz : x = z
      · refine ⟨s, hs, hsr, ?_⟩
        intro y hy hyz
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact (hyz hxz).elim
        · exact hA y hy hyz
      · refine ⟨min s (dist x z), lt_min hs (dist_pos.mpr hxz),
          (min_le_left _ _).trans_lt hsr, ?_⟩
        intro y hy hyz
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact min_le_right _ _
        · exact (min_le_left _ _).trans (hA y hy hyz)

theorem test_combination_zero (f : FreeSpace.LipZero M) (a : M →₀ ℝ)
    (hf : ∀ x ∈ a.support, f.1 x = 0) :
    test f (Finsupp.linearCombination ℝ FreeSpace.point a) = 0 := by
  classical
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, test_point]
  apply Finset.sum_eq_zero
  intro x hx
  rw [hf x hx, smul_zero]

theorem test_normalized_sub (f g : M → ℝ) {C D E : ℝ≥0}
    (hf : LipschitzWith C f) (hg : LipschitzWith D g)
    (hfg : LipschitzWith E (fun x => f x - g x)) (μ : FreeSpace.Space M) :
    test (normalized (fun x => f x - g x) hfg) μ =
      test (normalized f hf) μ - test (normalized g hg) μ := by
  change μ.1 (normalized (fun x => f x - g x) hfg) =
    μ.1 (normalized f hf) - μ.1 (normalized g hg)
  rw [← map_sub]
  congr 1
  apply Subtype.ext
  funext x
  change (f x - g x) - (f 0 - g 0) = (f x - f 0) - (g x - g 0)
  ring

theorem exists_small_cutoff (z : M) (μ : FreeSpace.Space M) (C : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) {r : ℝ≥0} (hr : 0 < r) :
    ∃ s : ℝ≥0, ∃ hs : 0 < s, s < r ∧ ∀ (f : M → ℝ) (hf : LipschitzWith C f)
      (hfz : f z = 0),
      |test (normalized (fun x => f x * cutoff z s x)
        (cutoff_product_lipschitz z hs f hf hfz)) μ| < ε := by
  classical
  have hden : 0 < 3 * (C : ℝ) + 1 := by positivity
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.1 FreeSpace.dense_combinations μ
    (ε / (3 * (C : ℝ) + 1)) (div_pos hε hden)
  obtain ⟨s, hs, hsr, hsA⟩ := finite_avoid_radius z (insert 0 a.support) (show 0 < (r : ℝ) from hr)
  let sn : ℝ≥0 := ⟨s, hs.le⟩
  refine ⟨sn, hs, hsr, ?_⟩
  intro f hf hfz
  let p : M → ℝ := fun x => f x * cutoff z sn x
  have hp : LipschitzWith (3 * C) p := cutoff_product_lipschitz z hs f hf hfz
  have hpzero (x : M) (hx : x ∈ insert 0 a.support) : p x = 0 := by
    by_cases hxz : x = z
    · simp [p, hxz, hfz]
    · change f x * cutoff z sn x = 0
      rw [cutoff_zero z hs (hsA x hx hxz), mul_zero]
  have hp0 := hpzero 0 (Finset.mem_insert_self _ _)
  have hν : test (normalized p hp) (Finsupp.linearCombination ℝ FreeSpace.point a) = 0 := by
    apply test_combination_zero
    intro x hx
    change p x - p 0 = 0
    rw [hpzero x (Finset.mem_insert_of_mem hx), hp0, sub_self]
  have heq : test (normalized p hp) μ =
      test (normalized p hp) (μ - Finsupp.linearCombination ℝ FreeSpace.point a) := by
    rw [map_sub, hν, sub_zero]
  change |test (normalized p hp) μ| < ε
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖normalized p hp‖ * ‖μ - Finsupp.linearCombination ℝ FreeSpace.point a‖ :=
      norm_test_apply_le _ _
    _ ≤ (3 * (C : ℝ) + 1) * ‖μ - Finsupp.linearCombination ℝ FreeSpace.point a‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have h := norm_normalized_le p hp
      simp only [NNReal.coe_mul, NNReal.coe_ofNat] at h
      linarith
    _ < (3 * (C : ℝ) + 1) * (ε / (3 * (C : ℝ) + 1)) := by
      apply mul_lt_mul_of_pos_left _ hden
      simpa only [dist_eq_norm] using ha
    _ = ε := mul_div_cancel₀ _ hden.ne'

theorem shrinking_tests (z : M) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (r : ℕ → ℝ≥0) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto (fun i => (r i : ℝ)) atTop (𝓝 0))
    (f : ℕ → M → ℝ) {C : ℝ≥0} (hf : ∀ i, LipschitzWith C (f i))
    (hfz : ∀ i, f i z = 0) (hfs : ∀ i x, (r i : ℝ) ≤ dist x z → f i x = 0) :
    Tendsto (fun i => test (normalized (f i) (hf i)) (μ i)) atTop (𝓝 0) := by
  classical
  by_contra hn
  rw [Metric.tendsto_atTop] at hn
  push Not at hn
  obtain ⟨ε, hε, hlarge⟩ := hn
  simp only [dist_zero_right, Real.norm_eq_abs] at hlarge
  have hsmall := fun i => exists_small_cutoff z (μ i) C (half_pos hε) (hr i)
  choose s hs hsr hsbound using hsmall
  have chooseStep (p : ℕ) : ∃ n : ℕ, p < n ∧
      ε ≤ |test (normalized (f n) (hf n)) (μ n)| ∧ (r n : ℝ) < s p / 2 := by
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hrlim ((s p : ℝ) / 2) (half_pos (hs p))
    obtain ⟨n, hnp, hnε⟩ := hlarge (max N (p + 1))
    refine ⟨n, ?_, hnε, ?_⟩
    · exact (Nat.lt_succ_self p).trans_le ((le_max_right _ _).trans hnp)
    · have ht := hN n ((le_max_left _ _).trans hnp)
      simpa only [dist_zero_right, Real.norm_of_nonneg (r n).coe_nonneg] using ht
  let next (p : ℕ) : ℕ := Classical.choose (chooseStep p)
  let seq : ℕ → ℕ := fun j => Nat.rec 0 (fun _ p => next p) j
  have hseq (j : ℕ) : seq j < seq (j+1) ∧
      ε ≤ |test (normalized (f (seq (j+1))) (hf _)) (μ (seq (j+1)))| ∧
      (r (seq (j+1)) : ℝ) < s (seq j) / 2 := Classical.choose_spec (chooseStep (seq j))
  have hseqmono : StrictMono seq := strictMono_nat_of_lt_succ (fun j => (hseq j).1)
  let a : ℕ → ℕ := fun j => seq (j+1)
  have ha : StrictMono a := fun _ _ h => hseqmono (Nat.add_lt_add_right h 1)
  have hrad (j : ℕ) : (r (a (j+1)) : ℝ) < s (a j) / 2 := (hseq (j+1)).2.2
  have hanti : StrictAnti (fun j => (r (a j) : ℝ)) := by
    apply strictAnti_nat_of_succ_lt
    intro j
    have ht : (s (a j) : ℝ) < r (a j) := hsr (a j)
    have hp : 0 < (s (a j) : ℝ) := hs (a j)
    linarith [hrad j]
  let h : ℕ → M → ℝ := fun j x => f (a j) x * (1 - cutoff z (s (a j)) x)
  have hh (j : ℕ) : LipschitzWith (3 * C) (h j) :=
    annular_product_lipschitz z (hs (a j)) (f (a j)) (hf _) (hfz _)
  have hsupport (j : ℕ) (x : M) (hx : h j x ≠ 0) :
      (s (a j) : ℝ) / 2 < dist x z ∧ dist x z < r (a j) := by
    constructor
    · by_contra hx'
      have ht := cutoff_one z (hs (a j)) (le_of_not_gt hx')
      exact hx (by simp only [h, ht, sub_self, mul_zero])
    · by_contra hx'
      have ht := hfs (a j) x (le_of_not_gt hx')
      exact hx (by simp only [h, ht, zero_mul])
  have hd : DisjointTests h := by
    intro x j k hj hk
    by_contra hjk
    have hs₁ := hsupport j x hj
    have hs₂ := hsupport k x hk
    rcases lt_or_gt_of_ne hjk with hjk | hkj
    · have ht := hanti.antitone (Nat.succ_le_of_lt hjk)
      change (r (a k) : ℝ) ≤ r (a (j+1)) at ht
      linarith [hrad j]
    · have ht := hanti.antitone (Nat.succ_le_of_lt hkj)
      change (r (a j) : ℝ) ≤ r (a (k+1)) at ht
      linarith [hrad k]
  have hpos (j : ℕ) : ε / 2 < |test (normalized (h j) (hh j)) (μ (a j))| := by
    let p : M → ℝ := fun x => f (a j) x * cutoff z (s (a j)) x
    have hp : LipschitzWith (3 * C) p :=
      cutoff_product_lipschitz z (hs (a j)) (f (a j)) (hf _) (hfz _)
    have hid : normalized (h j) (hh j) = normalized (f (a j)) (hf _) - normalized p hp := by
      apply Subtype.ext
      funext x
      change (f (a j) x * (1 - cutoff z (s (a j)) x)) -
        (f (a j) 0 * (1 - cutoff z (s (a j)) 0)) =
        (f (a j) x - f (a j) 0) -
          (f (a j) x * cutoff z (s (a j)) x - f (a j) 0 * cutoff z (s (a j)) 0)
      ring
    have hpairid : test (normalized (h j) (hh j)) (μ (a j)) =
        test (normalized (f (a j)) (hf _)) (μ (a j)) - test (normalized p hp) (μ (a j)) := by
      change (μ (a j)).1 (normalized (h j) (hh j)) = _
      rw [hid, map_sub]
      rfl
    have hremoved : |test (normalized p hp) (μ (a j))| < ε / 2 :=
      hsbound (a j) (f (a j)) (hf _) (hfz _)
    have hbig : ε ≤ |test (normalized (f (a j)) (hf _)) (μ (a j))| := (hseq j).2.1
    rw [hpairid]
    have ht := abs_sub_abs_le_abs_sub
      (test (normalized (f (a j)) (hf _)) (μ (a j))) (test (normalized p hp) (μ (a j)))
    linarith
  have hlim := disjoint_tests_vanish hd hh (hw.subseq ha)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (ε / 2) (half_pos hε)
  have ht := hN N le_rfl
  rw [dist_zero_right, Real.norm_eq_abs] at ht
  exact (not_lt_of_ge (hpos N).le) ht

end LocalizedLinearization

end LipschitzCounterexample
end

end OAI
