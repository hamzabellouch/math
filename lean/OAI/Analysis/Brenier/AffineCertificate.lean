import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace Problem358.FiniteAffine

variable {ι F : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The convex potential used by a finite-affine transport map. -/
def potential (y : ι → F) (c : ι → ℝ) (x : F) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪x, y i⟫ + c i)

/-- An index is active when its affine form dominates every other form. -/
def Maximizes (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) : Prop :=
  ∀ j, ⟪x, y j⟫ + c j ≤ ⟪x, y i⟫ + c i

lemma affine_le_potential (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    ⟪x, y i⟫ + c i ≤ potential y c x := by
  unfold potential
  exact Finset.le_sup' (fun j => ⟪x, y j⟫ + c j) (Finset.mem_univ i)

lemma potential_eq_iff_maximizes (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    potential y c x = ⟪x, y i⟫ + c i ↔ Maximizes y c x i := by
  constructor
  · intro h j
    simpa only [h] using affine_le_potential y c x j
  · intro h
    exact le_antisymm (Finset.sup'_le _ _ fun j _ => h j)
      (affine_le_potential y c x i)

lemma exists_maximizer (y : ι → F) (c : ι → ℝ) (x : F) :
    ∃ i, Maximizes y c x i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => ⟪x, y i⟫ + c i)
  exact ⟨i, (potential_eq_iff_maximizes y c x i).mp hi⟩

lemma continuous_potential (y : ι → F) (c : ι → ℝ) :
    Continuous (potential y c) := by
  unfold potential
  exact Continuous.finset_sup'_apply _ fun i _ =>
    (continuous_id.inner continuous_const).add continuous_const

lemma potential_le_of_affine_le (y : ι → F) (c : ι → ℝ) (x : F) (r : ℝ)
    (h : ∀ i, ⟪x, y i⟫ + c i ≤ r) : potential y c x ≤ r := by
  exact Finset.sup'_le _ _ fun i _ => h i

lemma convexOn_potential (y : ι → F) (c : ι → ℝ) :
    ConvexOn ℝ Set.univ (potential y c) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ a b ha hb hab
  apply potential_le_of_affine_le
  intro i
  have hx := mul_le_mul_of_nonneg_left (affine_le_potential y c x i) ha
  have hz := mul_le_mul_of_nonneg_left (affine_le_potential y c z i) hb
  simp only [inner_add_left, real_inner_smul_left, smul_eq_mul]
  have hc : (a + b) * c i = c i := by rw [hab]; ring
  nlinarith [hc]

lemma potential_sub_le (y : ι → F) (c : ι → ℝ) {L : ℝ}
    (hL : ∀ i, ‖y i‖ ≤ L) (x z : F) :
    potential y c x - potential y c z ≤ L * ‖x - z‖ := by
  apply sub_le_iff_le_add.mpr
  apply potential_le_of_affine_le
  intro i
  have hi := (real_inner_le_norm (x - z) (y i)).trans
    (mul_le_mul_of_nonneg_left (hL i) (norm_nonneg (x - z)))
  rw [inner_sub_left] at hi
  have hz := affine_le_potential y c z i
  nlinarith

lemma abs_potential_sub_le (y : ι → F) (c : ι → ℝ) {L : ℝ}
    (hL : ∀ i, ‖y i‖ ≤ L) (x z : F) :
    |potential y c x - potential y c z| ≤ L * ‖x - z‖ := by
  refine abs_le.mpr ⟨?_, potential_sub_le y c hL x z⟩
  have h := potential_sub_le y c hL z x
  rw [norm_sub_rev] at h
  linarith

lemma lipschitzWith_potential (y : ι → F) (c : ι → ℝ) {L : NNReal}
    (hL : ∀ i, ‖y i‖ ≤ L) : LipschitzWith L (potential y c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using abs_potential_sub_le y c hL x z

lemma potential_add_const (y : ι → F) (c : ι → ℝ) (k : ℝ) (x : F) :
    potential y (fun i => c i + k) x = potential y c x + k := by
  apply le_antisymm
  · apply potential_le_of_affine_le
    intro i
    have h := affine_le_potential y c x i
    linarith
  · obtain ⟨i, hi⟩ := exists_maximizer y c x
    rw [(potential_eq_iff_maximizes y c x i).mpr hi]
    have h := affine_le_potential y (fun i => c i + k) x i
    linarith

lemma supporting_inequality (y : ι → F) (c : ι → ℝ) (x z : F) (i : ι)
    (hi : Maximizes y c x i) :
    potential y c x + ⟪z - x, y i⟫ ≤ potential y c z := by
  rw [(potential_eq_iff_maximizes y c x i).mpr hi, inner_sub_left]
  have h := affine_le_potential y c z i
  linarith

omit [Fintype ι] [Nonempty ι] in
lemma active_slopes_monotone (y : ι → F) (c : ι → ℝ) (x z : F)
    (i j : ι) (hi : Maximizes y c x i) (hj : Maximizes y c z j) :
    0 ≤ ⟪x - z, y i - y j⟫ := by
  have h₁ := hi j
  have h₂ := hj i
  simp only [inner_sub_left, inner_sub_right]
  linarith

lemma intercept_le_potential_add (y : ι → F) (c : ι → ℝ)
    {R L : ℝ} (hL : ∀ i, ‖y i‖ ≤ L) (hL0 : 0 ≤ L)
    (x : F) (hx : ‖x‖ ≤ R) (i : ι) : c i ≤ potential y c x + R * L := by
  have hi := affine_le_potential y c x i
  have habs := (abs_real_inner_le_norm x (y i)).trans
    ((mul_le_mul_of_nonneg_left (hL i) (norm_nonneg x)).trans
      (mul_le_mul_of_nonneg_right hx hL0))
  have hneg := (abs_le.mp habs).1
  linarith

/-- The source term of the quadratic Kantorovich certificate. -/
def sourceDual (y : ι → F) (c : ι → ℝ) (x : F) : ℝ :=
  ‖x‖ ^ 2 - 2 * potential y c x

/-- The target term at a specified site. -/
def targetDualAt (y : ι → F) (c : ι → ℝ) (i : ι) : ℝ :=
  ‖y i‖ ^ 2 + 2 * c i

lemma dual_gap (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    ‖x - y i‖ ^ 2 - (sourceDual y c x + targetDualAt y c i) =
      2 * (potential y c x - (⟪x, y i⟫ + c i)) := by
  rw [norm_sub_sq_real]
  unfold sourceDual targetDualAt
  ring

lemma dual_le_cost (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    sourceDual y c x + targetDualAt y c i ≤ ‖x - y i‖ ^ 2 := by
  have h := affine_le_potential y c x i
  have hg := dual_gap y c x i
  linarith

lemma dual_eq_cost_iff (y : ι → F) (c : ι → ℝ) (x : F) (i : ι) :
    sourceDual y c x + targetDualAt y c i = ‖x - y i‖ ^ 2 ↔
      Maximizes y c x i := by
  rw [← potential_eq_iff_maximizes]
  have hg := dual_gap y c x i
  constructor <;> intro h <;> linarith

lemma dual_eq_cost_of_maximizes (y : ι → F) (c : ι → ℝ) (x : F) (i : ι)
    (hi : Maximizes y c x i) :
    sourceDual y c x + targetDualAt y c i = ‖x - y i‖ ^ 2 :=
  (dual_eq_cost_iff y c x i).mpr hi

omit [Fintype ι] [Nonempty ι] in
lemma maximizing_site_unique_of_strict (y : ι → F) (c : ι → ℝ)
    (x : F) (i : ι)
    (hi : ∀ j, j ≠ i → ⟪x, y j⟫ + c j < ⟪x, y i⟫ + c i)
    {j : ι} (hj : Maximizes y c x j) : j = i := by
  by_contra hji
  exact (not_lt_of_ge (hj i)) (hi j hji)

lemma continuous_sourceDual (y : ι → F) (c : ι → ℝ) :
    Continuous (sourceDual y c) := by
  exact (continuous_norm.pow 2).sub (continuous_const.mul (continuous_potential y c))

/-- A Borel extension of the target term from the finite set of sites. -/
def targetDual (y : ι → F) (c : ι → ℝ) (z : F) : ℝ :=
  ∑ i, ({y i} : Set F).indicator (fun _ => targetDualAt y c i) z

omit [Nonempty ι] [InnerProductSpace ℝ F] in
lemma targetDual_site (y : ι → F) (c : ι → ℝ) (hy : Function.Injective y)
    (i : ι) : targetDual y c (y i) = targetDualAt y c i := by
  classical
  simp [targetDual, Set.indicator, hy.eq_iff]

variable [MeasurableSpace F] [BorelSpace F]

omit [Nonempty ι] [InnerProductSpace ℝ F] in
lemma measurable_targetDual (y : ι → F) (c : ι → ℝ) :
    Measurable (targetDual y c) := by
  unfold targetDual
  exact Finset.measurable_sum _ fun i _ =>
    measurable_const.indicator (measurableSet_singleton (y i))

omit [Nonempty ι] [InnerProductSpace ℝ F] in
lemma integrable_targetDual (y : ι → F) (c : ι → ℝ)
    (μ : Measure F) [IsFiniteMeasure μ] : Integrable (targetDual y c) μ := by
  unfold targetDual
  exact integrable_finsetSum _ fun i _ =>
    (integrable_const _).indicator (measurableSet_singleton (y i))

omit [MeasurableSpace F] [BorelSpace F] in
lemma dual_le_cost_on_range (y : ι → F) (c : ι → ℝ) (hy : Function.Injective y)
    (x z : F) (hz : z ∈ Set.range y) :
    sourceDual y c x + targetDual y c z ≤ ‖x - z‖ ^ 2 := by
  obtain ⟨i, rfl⟩ := hz
  rw [targetDual_site y c hy i]
  exact dual_le_cost y c x i

omit [MeasurableSpace F] [BorelSpace F] in
lemma dual_eq_cost_on_range_iff (y : ι → F) (c : ι → ℝ)
    (hy : Function.Injective y) (x : F) (i : ι) :
    sourceDual y c x + targetDual y c (y i) = ‖x - y i‖ ^ 2 ↔
      Maximizes y c x i := by
  rw [targetDual_site y c hy i]
  exact dual_eq_cost_iff y c x i

end Problem358.FiniteAffine

end

open MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace Problem358.FiniteAffine

variable {ι V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Opposite intercept perturbations cancel at the midpoint of two active cells. -/
theorem maximizes_midpoint_of_symmetric_intercepts
    (y : ι → V) (c q : ι → ℝ) (s : ℝ) {x z : V} {i : ι}
    (hx : Maximizes y (fun j => c j - s * q j) x i)
    (hz : Maximizes y (fun j => c j + s * q j) z i) :
    Maximizes y c ((1 / 2 : ℝ) • (x + z)) i := by
  intro j
  have hxj := hx j
  have hzj := hz j
  simp only [inner_add_left, real_inner_smul_left]
  linarith

/-- The same inclusion restricted to a convex source body. -/
theorem midpoint_mem_cell_of_symmetric_intercepts
    (y : ι → V) (c q : ι → ℝ) (s : ℝ) {K : Set V}
    (hK : Convex ℝ K) {x z : V} {i : ι}
    (hxK : x ∈ K) (hzK : z ∈ K)
    (hx : Maximizes y (fun j => c j - s * q j) x i)
    (hz : Maximizes y (fun j => c j + s * q j) z i) :
    (1 / 2 : ℝ) • (x + z) ∈ K ∧
      Maximizes y c ((1 / 2 : ℝ) • (x + z)) i := by
  refine ⟨?_, maximizes_midpoint_of_symmetric_intercepts y c q s hx hz⟩
  simpa only [smul_add] using hK hxK hzK (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)

theorem isClosed_setOf_maximizes (y : ι → V) (c : ι → ℝ) (i : ι) :
    IsClosed {x | Maximizes y c x i} := by
  simp only [Maximizes, Set.ofPred_forall]
  apply isClosed_iInter
  intro j
  exact isClosed_le ((continuous_id.inner continuous_const).add continuous_const)
    ((continuous_id.inner continuous_const).add continuous_const)

/-- Global domination restricts to the support of the dominated measure. -/
theorem le_restrict_of_ae_mem {X : Type*} [MeasurableSpace X]
    {ρ ν : Measure X} {S : Set X} (hle : ρ ≤ ν) (hS : ∀ᵐ x ∂ρ, x ∈ S) :
    ρ ≤ ν.restrict S := by
  rw [← Measure.restrict_eq_self_of_ae_mem hS]
  exact Measure.restrict_mono_measure hle S

/-- A midpoint coupling of opposite cells is supported on the middle cell, so
any ambient density domination automatically restricts to that middle cell. -/
theorem scaled_midpoint_law_le_restrict_cell
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (y : ι → V) (c q : ι → ℝ) (s : ℝ) (i : ι)
    {K : Set V} (hK : Convex ℝ K) (hKm : MeasurableSet K)
    {π : Measure (V × V)} {ν : Measure V} {γ : ℝ≥0∞}
    (hminus : ∀ᵐ p ∂π, p.1 ∈ K ∧ Maximizes y (fun j => c j - s * q j) p.1 i)
    (hplus : ∀ᵐ p ∂π, p.2 ∈ K ∧ Maximizes y (fun j => c j + s * q j) p.2 i)
    (hdom : γ • Measure.map (fun p : V × V => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤ ν) :
    γ • Measure.map (fun p : V × V => (1 / 2 : ℝ) • (p.1 + p.2)) π ≤
      ν.restrict {x | x ∈ K ∧ Maximizes y c x i} := by
  apply le_restrict_of_ae_mem hdom
  apply Measure.ae_smul_measure
  have hm : Measurable (fun p : V × V => (1 / 2 : ℝ) • (p.1 + p.2)) := by
    fun_prop
  apply (ae_map_iff hm.aemeasurable
    (hKm.inter (isClosed_setOf_maximizes y c i).measurableSet)).mpr
  filter_upwards [hminus, hplus] with p hp hm
  exact midpoint_mem_cell_of_symmetric_intercepts y c q s hK hp.1 hm.1 hp.2 hm.2

end Problem358.FiniteAffine

end OAI
