import OAI.Analysis.KadisonKastler.BoundaryDiagonal
import OAI.Analysis.KadisonKastler.ConcreteTraceHilbert
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic.DeriveCountable

namespace OAI

/-! # Measurability of diagonal least-norm vectors

Finite rational convex expressions form a countable dense subset of each
closed convex hull. Choosing the first expression within a specified
squared-norm tolerance gives measurable approximants; the parallelogram
identity forces their convergence to the unique least vector.
-/

namespace KadisonKastler

open Filter Set MeasureTheory TopologicalSpace
open scoped Topology

noncomputable section

/-- A countable syntax for rational convex combinations. Clamping the
rational parameter avoids proof fields in the syntax. -/
inductive RationalConvexExpr (ι : Type*) where
  | leaf : ι → RationalConvexExpr ι
  | blend : ℚ → RationalConvexExpr ι → RationalConvexExpr ι → RationalConvexExpr ι
  deriving Countable

private def convexParameter (t : ℝ) : ℝ := max 0 (min 1 t)

private theorem convexParameter_nonneg (t : ℝ) : 0 ≤ convexParameter t := le_max_left _ _
private theorem convexParameter_le_one (t : ℝ) : convexParameter t ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)
private theorem convexParameter_eq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    convexParameter t = t := by simp [convexParameter, min_eq_right h1, max_eq_right h0]

namespace RationalConvexExpr

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Evaluation of the rational convex syntax. -/
def eval (v : ι → E) : RationalConvexExpr ι → E
  | leaf i => v i
  | blend q a b => convexParameter (q : ℝ) • eval v a +
      (1 - convexParameter (q : ℝ)) • eval v b

/-- Every expression belongs to the ordinary convex hull of its leaves. -/
theorem eval_mem_convexHull (v : ι → E) (a : RationalConvexExpr ι) :
    eval v a ∈ convexHull ℝ (Set.range v) := by
  induction a with
  | leaf i => exact subset_convexHull ℝ _ ⟨i, rfl⟩
  | blend q a b ha hb =>
    exact convex_convexHull ℝ _ ha hb (convexParameter_nonneg _)
      (sub_nonneg.mpr (convexParameter_le_one _)) (add_sub_cancel _ _)

/-- The closure of rational combinations is closed under all real convex
combinations, by density of the rational parameters. -/
theorem convex_closure_range_eval (v : ι → E) :
    Convex ℝ (closure (Set.range (eval v))) := by
  intro x hx y hy a b ha hb hab
  have hq (q : ℚ) : convexParameter (q : ℝ) • x +
      (1 - convexParameter (q : ℝ)) • y ∈ closure (Set.range (eval v)) := by
    apply map_mem_closure₂ (f := fun x y : E =>
      convexParameter (q : ℝ) • x + (1 - convexParameter (q : ℝ)) • y)
      (by fun_prop) hx hy
    rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
    exact ⟨blend q c d, rfl⟩
  have hcont : Continuous (fun t : ℝ => convexParameter t • x +
      (1 - convexParameter t) • y) := by unfold convexParameter; fun_prop
  have hmem := map_mem_closure hcont (Rat.denseRange_cast a) (by
    rintro _ ⟨q, rfl⟩
    exact hq q)
  rw [isClosed_closure.closure_eq] at hmem
  have ha1 : a ≤ 1 := by linarith
  simpa only [convexParameter_eq ha ha1, show 1 - a = b by linarith] using hmem

/-- Rational convex expressions are dense in the real convex hull. -/
theorem closure_range_eval (v : ι → E) :
    closure (Set.range (eval v)) = closure (convexHull ℝ (Set.range v)) := by
  apply le_antisymm
  · exact closure_mono (Set.range_subset_iff.mpr (eval_mem_convexHull v))
  · apply closure_minimal _ isClosed_closure
    apply convexHull_min _ (convex_closure_range_eval v)
    rintro _ ⟨i, rfl⟩
    exact subset_closure ⟨leaf i, rfl⟩

/-- Evaluation preserves strong measurability of a family of leaves. -/
theorem stronglyMeasurable_eval {P : Type*} [MeasurableSpace P]
    (v : ι → P → E) (hv : ∀ i, StronglyMeasurable (v i)) (a : RationalConvexExpr ι) :
    StronglyMeasurable (fun p => eval (fun i => v i p) a) := by
  induction a with
  | leaf i => exact hv i
  | blend q a b ha hb => exact (ha.const_smul _).add (hb.const_smul _)

/-- Evaluation preserves almost-everywhere strong measurability. -/
theorem aestronglyMeasurable_eval {P : Type*} [MeasurableSpace P] {μ : Measure P}
    (v : ι → P → E) (hv : ∀ i, AEStronglyMeasurable (v i) μ) (a : RationalConvexExpr ι) :
    AEStronglyMeasurable (fun p => eval (fun i => v i p) a) μ := by
  induction a with
  | leaf i => exact hv i
  | blend q a b ha hb => exact (ha.const_smul _).add (hb.const_smul _)

end RationalConvexExpr

section Least

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A squared-norm tolerance controls distance to a least vector. -/
theorem norm_sub_sq_le_twice_gap {K : Set E} (hK : Convex ℝ K)
    {c z : E} (hc : c ∈ K) (hz : z ∈ K) (hmin : ∀ y ∈ K, ‖c‖ ≤ ‖y‖) :
    ‖z - c‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 - ‖c‖ ^ 2) := by
  have hm : (1 / 2 : ℝ) • (z + c) ∈ K := by
    simpa only [smul_add] using hK hz hc (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hp := hmin _ hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hp
  have hs := mul_self_le_mul_self (norm_nonneg c) hp
  have hpar := parallelogram_law_with_norm ℂ z c
  nlinarith

omit [InnerProductSpace ℂ E] in
/-- The infimum over a dense countable family is the least squared norm. -/
theorem iInf_norm_sq_eq_least (z : ℕ → E) (c : E)
    (hc : c ∈ closure (Set.range z))
    (hmin : ∀ y ∈ closure (Set.range z), ‖c‖ ≤ ‖y‖) :
    (⨅ n, ‖z n‖ ^ 2) = ‖c‖ ^ 2 := by
  have hlo : ‖c‖ ^ 2 ≤ ⨅ n, ‖z n‖ ^ 2 := by
    apply le_ciInf
    intro n
    exact pow_le_pow_left₀ (norm_nonneg c) (hmin _ (subset_closure ⟨n, rfl⟩)) _
  obtain ⟨w, hw, hwlim⟩ := mem_closure_iff_seq_limit.mp hc
  have hi (n : ℕ) : (⨅ n, ‖z n‖ ^ 2) ≤ ‖w n‖ ^ 2 := by
    obtain ⟨k, hk⟩ := hw n
    rw [← hk]
    exact ciInf_le ⟨0, Set.forall_mem_range.mpr (fun _ => sq_nonneg _)⟩ k
  exact le_antisymm (ge_of_tendsto (hwlim.norm.pow 2) (Eventually.of_forall hi)) hlo

variable {P : Type*} [MeasurableSpace P] [MeasurableSpace E] [BorelSpace E]
  [SeparableSpace E]

/-- The first countable approximant with almost least squared norm is a
measurable function; its limit is the least vector. -/
theorem stronglyMeasurable_countable_least (z : ℕ → P → E)
    (hz : ∀ n, StronglyMeasurable (z n)) (c : P → E)
    (hc : ∀ p, c p ∈ closure (Set.range (fun n => z n p)))
    (hconv : ∀ p, Convex ℝ (closure (Set.range (fun n => z n p))))
    (hmin : ∀ p y, y ∈ closure (Set.range (fun n => z n p)) → ‖c p‖ ≤ ‖y‖) :
    StronglyMeasurable c := by
  let d : P → ℝ := fun p => ⨅ n, ‖z n p‖ ^ 2
  have hd : Measurable d := Measurable.iInf (fun n => (hz n).measurable.norm.pow_const 2)
  have hdeq (p : P) : d p = ‖c p‖ ^ 2 := iInf_norm_sq_eq_least _ _ (hc p) (hmin p)
  have hex (k : ℕ) (p : P) : ∃ n, ‖z n p‖ ^ 2 < d p + 1 / ((k : ℝ) + 1) := by
    apply exists_lt_of_ciInf_lt
    have hpos : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact lt_add_of_pos_right _ hpos
  let a : ℕ → P → E := fun k p => z (Nat.find (hex k p)) p
  have ham (k : ℕ) : StronglyMeasurable (a k) := by
    apply Measurable.stronglyMeasurable
    exact Measurable.find (fun n => (hz n).measurable)
      (fun n => measurableSet_lt ((hz n).measurable.norm.pow_const 2)
        (hd.add_const _)) (hex k)
  apply stronglyMeasurable_of_tendsto atTop ham
  apply tendsto_pi_nhds.mpr
  intro p
  rw [← tendsto_sub_nhds_zero_iff]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hbound (k : ℕ) : ‖a k p - c p‖ ≤ Real.sqrt (2 / ((k : ℝ) + 1)) := by
    have hgap := norm_sub_sq_le_twice_gap (hconv p) (hc p)
      (subset_closure ⟨Nat.find (hex k p), rfl⟩) (hmin p)
    have hk := Nat.find_spec (hex k p)
    have hk' : ‖a k p‖ ^ 2 < ‖c p‖ ^ 2 + 1 / ((k : ℝ) + 1) :=
      hk.trans_le (by rw [hdeq p])
    change ‖a k p - c p‖ ^ 2 ≤ 2 * (‖a k p‖ ^ 2 - ‖c p‖ ^ 2) at hgap
    have hs : ‖a k p - c p‖ ^ 2 ≤ 2 / ((k : ℝ) + 1) := calc
      _ ≤ 2 * (‖a k p‖ ^ 2 - ‖c p‖ ^ 2) := hgap
      _ ≤ 2 * (1 / ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hk']) (by norm_num)
      _ = _ := by ring
    exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hs
  apply squeeze_zero (fun _ => norm_nonneg _) hbound
  have ht : Tendsto (fun k : ℕ => 2 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
  simpa only [Real.sqrt_zero, Function.comp_def] using Real.continuous_sqrt.continuousAt.tendsto.comp ht


/-- The least vector of the closed convex hull of countably many strongly
measurable Hilbert-valued fields is strongly measurable. -/
theorem stronglyMeasurable_convex_least {ι : Type*} [Countable ι] [Nonempty ι]
    (v : ι → P → E) (hv : ∀ i, StronglyMeasurable (v i)) (c : P → E)
    (hc : ∀ p, c p ∈ closure (convexHull ℝ (Set.range (fun i => v i p))))
    (hmin : ∀ p y, y ∈ closure (convexHull ℝ (Set.range (fun i => v i p))) →
      ‖c p‖ ≤ ‖y‖) : StronglyMeasurable c := by
  let : Nonempty (RationalConvexExpr ι) := ⟨.leaf (Classical.choice inferInstance)⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (RationalConvexExpr ι)
  let z : ℕ → P → E := fun n p => RationalConvexExpr.eval (fun i => v i p) (e n)
  have hclosure (p : P) : closure (Set.range (fun n => z n p)) =
      closure (convexHull ℝ (Set.range (fun i => v i p))) := by
    have hrange : Set.range (fun n => z n p) =
        Set.range (RationalConvexExpr.eval (fun i => v i p)) :=
      he.range_comp _
    rw [hrange, RationalConvexExpr.closure_range_eval]
  apply stronglyMeasurable_countable_least z
    (fun n => RationalConvexExpr.stronglyMeasurable_eval v hv (e n)) c
  · intro p
    rw [hclosure]
    exact hc p
  · intro p
    rw [hclosure]
    exact (convex_convexHull ℝ _).closure
  · intro p y hy
    rw [hclosure] at hy
    exact hmin p y hy

/-- Almost-everywhere measurable generators suffice: choose measurable
versions of the leaves, apply the explicit countable approximation, and
use uniqueness on the common conull set. -/
theorem aestronglyMeasurable_convex_least [CompleteSpace E]
    {ι : Type*} [Countable ι] [Nonempty ι] {μ : Measure P}
    (v : ι → P → E) (hv : ∀ i, AEStronglyMeasurable (v i) μ) (c : P → E)
    (hc : ∀ p, c p ∈ closure (convexHull ℝ (Set.range (fun i => v i p))))
    (hmin : ∀ p y, y ∈ closure (convexHull ℝ (Set.range (fun i => v i p))) →
      ‖c p‖ ≤ ‖y‖) : AEStronglyMeasurable c μ := by
  let v' : ι → P → E := fun i => (hv i).mk (v i)
  have hex (p : P) : ∃ x : E,
      x ∈ closure (convexHull ℝ (Set.range (fun i => v' i p))) ∧
      ∀ y ∈ closure (convexHull ℝ (Set.range (fun i => v' i p))), ‖x‖ ≤ ‖y‖ := by
    apply (exists_unique_least_norm ?_ isClosed_closure (convex_convexHull ℝ _).closure).exists
    exact ⟨v' (Classical.choice inferInstance) p,
      subset_closure (subset_convexHull ℝ _ (Set.mem_range_self _))⟩
  choose c' hc' using hex
  have hcm : StronglyMeasurable c' := stronglyMeasurable_convex_least v'
    (fun i => (hv i).stronglyMeasurable_mk) c' (fun p => (hc' p).1) (fun p => (hc' p).2)
  apply hcm.aestronglyMeasurable.congr
  filter_upwards [ae_all_iff.mpr (fun i => (hv i).ae_eq_mk)] with p hp
  have heq : (fun i => v i p) = fun i => v' i p := funext hp
  apply eq_of_convex_least_norm (convex_convexHull ℝ _).closure (hc' p).1
    (by simpa only [heq] using hc p) (hc' p).2
  intro y hy
  exact hmin p y (by simpa only [heq] using hy)

end Least

/-- Measurability of the actual diagonal least operator in its supplied
separable trace Hilbert realization. -/
theorem aestronglyMeasurable_diagonal_least
    {H E P ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace P] [Countable ι] [Nonempty ι]
    {M : VonNeumannAlgebra H} (J : Algebra M →ₗ[ℂ] E) {μ : Measure P}
    (v : ι → P → Algebra M)
    (hv : ∀ i, AEStronglyMeasurable (fun p => J (v i p)) μ)
    (c : P → Algebra M)
    (hc : ∀ p, J (c p) ∈ diagonalTraceHull J (Set.range (fun i => v i p)))
    (hmin : ∀ p y, y ∈ diagonalTraceHull J (Set.range (fun i => v i p)) →
      ‖J (c p)‖ ≤ ‖y‖) : AEStronglyMeasurable (fun p => J (c p)) μ := by
  apply aestronglyMeasurable_convex_least (fun i p => J (v i p)) hv (fun p => J (c p))
  · intro p
    simpa only [diagonalTraceHull_eq, ← Set.range_comp, Function.comp_def] using hc p
  · intro p y hy
    apply hmin p y
    simpa only [diagonalTraceHull_eq, ← Set.range_comp, Function.comp_def] using hy



section DiagonalFields

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
variable (hτ : FiniteVectorTrace τ)

local instance diagonalMeasurableOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder (Algebra M)
local instance diagonalMeasurableStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing (Algebra M)

include hJ hτ

/-- The actual diagonal least field has a measurable trace-Hilbert
realization, full least-vector properties, and exact covariance. -/
theorem exists_measurable_diagonal_least_field
    {G D : Type*} [Group G] [Countable G] [MeasurableSpace D] {μ : Measure (D × D)}
    (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    (hWmeas : ∀ t, AEStronglyMeasurable
      (fun p : D × D => J ((W t p.1 : Algebra M) * star (W t p.2 : Algebra M))) μ)
    {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ c : D → D → Algebra M,
      AEStronglyMeasurable (fun p : D × D => J (c p.1 p.2)) μ ∧
      (∀ x y, J (c x y) ∈ diagonalTraceHull J (diagonalGenerators W x y) ∧
        ‖c x y‖ ≤ 1 ∧ ‖c x y - 1‖ ≤ r ∧
        ∀ z ∈ diagonalTraceHull J (diagonalGenerators W x y), ‖J (c x y)‖ ≤ ‖z‖) ∧
      (∀ g x y, c x y = (W g x : Algebra M) * c (shift g x) (shift g y) *
        star (W g y : Algebra M)) := by
  obtain ⟨c, hc, hcov⟩ := exists_diagonal_least_field_full J hJ hτ shift W hW hr hnear
  refine ⟨c, ?_, hc, hcov⟩
  exact aestronglyMeasurable_diagonal_least J
    (fun t (p : D × D) => (W t p.1 : Algebra M) * star (W t p.2 : Algebra M))
    hWmeas (fun p : D × D => c p.1 p.2)
    (fun p => (hc p.1 p.2).1) (fun p => (hc p.1 p.2).2.2.2)

/-- Measurable least-field data together with its exact unitary polar
factor. The trace-Hilbert measurability assertion concerns the least
field; operator measurability of its polar factor is a separate transfer. -/
theorem exists_measurable_diagonal_polar_data
    {G D : Type*} [Group G] [Countable G] [MeasurableSpace D] {μ : Measure (D × D)}
    (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    (hWmeas : ∀ t, AEStronglyMeasurable
      (fun p : D × D => J ((W t p.1 : Algebra M) * star (W t p.2 : Algebra M))) μ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ (c : D → D → Algebra M) (a : D → D → unitary (Algebra M)),
      AEStronglyMeasurable (fun p : D × D => J (c p.1 p.2)) μ ∧
      (∀ x y, ‖c x y‖ ≤ 1 ∧ ‖c x y - 1‖ ≤ r ∧ IsUnit (c x y) ∧
        (a x y : Algebra M) * CFC.abs (c x y) = c x y ∧
        ‖(a x y : Algebra M) - 1‖ ≤ 2 * r) ∧
      (∀ g x y, c x y = (W g x : Algebra M) * c (shift g x) (shift g y) *
        star (W g y : Algebra M)) ∧
      (∀ g x y, (a x y : Algebra M) =
        (W g x : Algebra M) * (a (shift g x) (shift g y) : Algebra M) *
          star (W g y : Algebra M)) := by
  obtain ⟨c, hcm, hc, hcov⟩ :=
    exists_measurable_diagonal_least_field J hJ hτ shift W hW hWmeas hr0 hnear
  have hunit (x y : D) : IsUnit (c x y) := by
    nontriviality Algebra M
    exact (Units.ofNearby 1 (c x y) (by simpa using ((hc x y).2.2.1).trans_lt hr)).isUnit
  have hp (x y : D) := exists_polar_unitary_near_one (c x y)
    (((hc x y).2.2.1).trans_lt hr)
  choose a ha han using hp
  refine ⟨c, a, hcm, ?_, hcov, ?_⟩
  · intro x y
    exact ⟨(hc x y).2.1, (hc x y).2.2.1, hunit x y, ha x y,
      (han x y).trans (mul_le_mul_of_nonneg_left (hc x y).2.2.1 (by norm_num))⟩
  · intro g x y
    exact polar_unitary_sandwich (hunit x y) (W g x) (W g y) (a x y)
      (a (shift g x) (shift g y)) (ha x y) (ha (shift g x) (shift g y)) (hcov g x y)

end DiagonalFields


section Canonical

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] {M : VonNeumannAlgebra H}
local instance diagonalCanonicalOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder (Algebra M)
local instance diagonalCanonicalStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing (Algebra M)

/-- The measurable diagonal construction in the canonical separable
trace Hilbert space of a separably acting finite factor. -/
theorem exists_concrete_measurable_diagonal_polar_data
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    {G D : Type*} [Group G] [Countable G] [MeasurableSpace D] {μ : Measure (D × D)}
    (shift : G → D → D) (W : G → D → unitary (Algebra M))
    (hW : ∀ g t x, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (shift g x) : Algebra M))
    (hWmeas : ∀ t, AEStronglyMeasurable (fun p : D × D =>
      concreteTraceEmbedding hM ((W t p.1 : Algebra M) * star (W t p.2 : Algebra M))) μ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (hnear : ∀ t x y, ‖(W t x : Algebra M) * star (W t y : Algebra M) - 1‖ ≤ r) :
    ∃ (c : D → D → Algebra M) (a : D → D → unitary (Algebra M)),
      AEStronglyMeasurable (fun p : D × D => concreteTraceEmbedding hM (c p.1 p.2)) μ ∧
      (∀ x y, ‖c x y‖ ≤ 1 ∧ ‖c x y - 1‖ ≤ r ∧ IsUnit (c x y) ∧
        (a x y : Algebra M) * CFC.abs (c x y) = c x y ∧
        ‖(a x y : Algebra M) - 1‖ ≤ 2 * r) ∧
      (∀ g x y, c x y = (W g x : Algebra M) * c (shift g x) (shift g y) *
        star (W g y : Algebra M)) ∧
      (∀ g x y, (a x y : Algebra M) =
        (W g x : Algebra M) * (a (shift g x) (shift g y) : Algebra M) *
          star (W g y : Algebra M)) := by
  borelize (ConcreteTraceHilbert hM)
  exact exists_measurable_diagonal_polar_data (concreteTraceEmbedding hM)
    (concreteTraceEmbedding_norm hM) (concreteFactorTrace_finiteVector hM)
    shift W hW hWmeas hr0 hr hnear

end Canonical

end

end KadisonKastler

end OAI
