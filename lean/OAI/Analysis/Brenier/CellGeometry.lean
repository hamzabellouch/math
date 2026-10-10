import OAI.Analysis.Brenier.Argmax
import OAI.Analysis.Brenier.Uniform

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace

namespace Problem358
namespace CellGeometry

variable {d : ℕ} {ι : Type*}

/-- The closed cell of one affine branch, including ties. -/
def closedCell (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι) : Set (E d) :=
  {x | x ∈ K ∧ ∀ j, inner ℝ x (y j) + c j ≤ inner ℝ x (y i) + c i}

theorem closedCell_subset (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (i : ι) :
    closedCell K y c i ⊆ K := fun _ h => h.1

theorem isClosed_closedCell {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) : IsClosed (closedCell K y c i) := by
  have heq : closedCell K y c i = K ∩ ⋂ j,
      {x | inner ℝ x (y j) + c j ≤ inner ℝ x (y i) + c i} := by
    ext x
    simp [closedCell]
  rw [heq]
  exact hK.inter (isClosed_iInter fun j =>
    isClosed_le ((continuous_id.inner continuous_const).add continuous_const)
      ((continuous_id.inner continuous_const).add continuous_const))

theorem isCompact_closedCell {K : Set (E d)} (hK : IsCompact K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) : IsCompact (closedCell K y c i) :=
  hK.of_isClosed_subset (isClosed_closedCell hK.isClosed y c i)
    (closedCell_subset K y c i)

theorem convex_closedCell {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (i : ι) : Convex ℝ (closedCell K y c i) := by
  intro x hx z hz a b ha hb hab
  refine ⟨hK hx.1 hz.1 ha hb hab, ?_⟩
  intro j
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  have h1 := mul_le_mul_of_nonneg_left (hx.2 j) ha
  have h2 := mul_le_mul_of_nonneg_left (hz.2 j) hb
  nlinarith [congrArg (fun t : ℝ => t * c i) hab,
    congrArg (fun t : ℝ => t * c j) hab]

theorem exists_mem_closedCell [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (y : ι → E d) (c : ι → ℝ) {x : E d} (hx : x ∈ K) :
    ∃ i, x ∈ closedCell K y c i := by
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j => inner ℝ x (y j) + c j) Finset.univ_nonempty
  exact ⟨i, hx, fun j => hi j (Finset.mem_univ j)⟩

theorem iUnion_closedCell [Fintype ι] [Nonempty ι]
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) :
    (⋃ i, closedCell K y c i) = K := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact hi.1
  · intro hx
    obtain ⟨i, hi⟩ := exists_mem_closedCell y c hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- Positive-volume cells have strictly active points in the interior, once affine ties
have been removed as a null set. -/
theorem exists_strict_active_interior {K : Set (E d)}
    (hconv : Convex ℝ K) (y : ι → E d) (c : ι → ℝ) (i : ι)
    (hpos : volume (closedCell K y c i) ≠ 0)
    (hties : ∀ᵐ x ∂volume, ∀ j, j ≠ i →
      inner ℝ x (y j) + c j ≠ inner ℝ x (y i) + c i) :
    ∃ x ∈ interior K, ∀ j, j ≠ i →
      inner ℝ x (y j) + c j < inner ℝ x (y i) + c i := by
  have hboundary : ∀ᵐ x ∂(volume : Measure (E d)), x ∉ frontier K := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hconv.addHaar_frontier volume
  have hgood : ∀ᵐ x ∂volume.restrict (closedCell K y c i),
      x ∉ frontier K ∧ ∀ j, j ≠ i →
        inner ℝ x (y j) + c j ≠ inner ℝ x (y i) + c i :=
    ae_restrict_of_ae (hboundary.and hties)
  obtain ⟨x, hx, hxb, hxt⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos hgood
  refine ⟨x, ?_, fun j hj => lt_of_le_of_ne (hx.2 j) (hxt j hj)⟩
  by_contra hn
  exact hxb ⟨subset_closure hx.1, hn⟩

/-- Convex interpolation of the intercepts and source points remains in the same cell. -/
theorem combo_mem_closedCell {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c e : ι → ℝ) (i : ι) {x z : E d}
    (hx : x ∈ closedCell K y c i) (hz : z ∈ closedCell K y e i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • z ∈ closedCell K y (fun j => a * c j + b * e j) i := by
  refine ⟨hK hx.1 hz.1 ha hb hab, ?_⟩
  intro j
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
  have h1 := mul_le_mul_of_nonneg_left (hx.2 j) ha
  have h2 := mul_le_mul_of_nonneg_left (hz.2 j) hb
  nlinarith

/-- The opposite-intercept midpoint inclusion used in the moment estimate. -/
theorem midpoint_mem_closedCell {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c q : ι → ℝ) (i : ι) (s : ℝ) {x z : E d}
    (hx : x ∈ closedCell K y (fun j => c j - s * q j) i)
    (hz : z ∈ closedCell K y (fun j => c j + s * q j) i) :
    (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • z ∈ closedCell K y c i := by
  have h := combo_mem_closedCell hK y _ _ i hx hz
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
  have heq : (fun j => (1 / 2 : ℝ) * (c j - s * q j) +
      (1 / 2 : ℝ) * (c j + s * q j)) = c := by
    funext j
    ring
  rwa [heq] at h

/-- An affine equality plane separating two strictly active interior points meets
 the interior of the convex source. -/
theorem exists_affine_equality_interior {K : Set (E d)} (hK : Convex ℝ K)
    {y z : E d} {c e : ℝ} {p q : E d}
    (hp : p ∈ interior K) (hq : q ∈ interior K)
    (hp_lt : inner ℝ p y + c < inner ℝ p z + e)
    (hq_lt : inner ℝ q z + e < inner ℝ q y + c) :
    ∃ x ∈ interior K, inner ℝ x y + c = inner ℝ x z + e := by
  let f : E d → ℝ := fun x => (inner ℝ x y + c) - (inner ℝ x z + e)
  have hf : Continuous f :=
    ((continuous_id.inner continuous_const).add continuous_const).sub
      ((continuous_id.inner continuous_const).add continuous_const)
  have hzero : (0 : ℝ) ∈ Set.Icc (f p) (f q) := by
    constructor <;> dsimp [f] <;> linarith
  obtain ⟨x, hx, heq⟩ := hK.interior.isPreconnected.intermediate_value
    hp hq hf.continuousOn hzero
  exact ⟨x, hx, sub_eq_zero.mp heq⟩

end CellGeometry
end Problem358

end

noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace

namespace Problem358
namespace CellGeometry

variable {d : ℕ} {ι : Type*}

/-- Distinct-site closed cells overlap only along null affine tie planes. -/
theorem pairwise_aedisjoint_closedCell {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    (K : Set (E d)) (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) :
    Pairwise (fun i j => AEDisjoint ρ (closedCell K y c i) (closedCell K y c j)) := by
  intro i j hij
  change ρ (closedCell K y c i ∩ closedCell K y c j) = 0
  apply hρ
  apply measure_mono_null (t := {x | inner ℝ x (y i) + c i = inner ℝ x (y j) + c j})
  · intro x hx
    exact le_antisymm (hx.2.2 i) (hx.1.2 j)
  · exact haar_affine_tie_null volume (hy.ne hij) (c i) (c j)

/-- The closed cells form a finite partition for all measures absolutely continuous
with respect to volume. -/
theorem sum_measure_closedCell [Fintype ι] [Nonempty ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume) {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) :
    (∑ i, ρ (closedCell K y c i)) = ρ K := by
  have h := measure_iUnion₀ (pairwise_aedisjoint_closedCell hρ K y c hy)
    (fun i => (isClosed_closedCell hK y c i).measurableSet.nullMeasurableSet)
  simpa only [iUnion_closedCell, tsum_fintype] using h.symm

/-- Integrable functions can be summed cellwise despite the shared boundary faces. -/
theorem sum_integral_closedCell [Fintype ι] [Nonempty ι]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume) {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    {f : E d → V} (hf : IntegrableOn f K ρ) :
    (∑ i, ∫ x in closedCell K y c i, f x ∂ρ) = ∫ x in K, f x ∂ρ := by
  have hi : IntegrableOn f (⋃ i, closedCell K y c i) ρ := by
    simpa only [iUnion_closedCell] using hf
  have h := integral_iUnion_ae
    (fun i => (isClosed_closedCell hK y c i).measurableSet.nullMeasurableSet)
    (pairwise_aedisjoint_closedCell hρ K y c hy) hi
  simpa only [iUnion_closedCell, tsum_fintype] using h.symm

/-- Real-valued cell masses also add to the total source mass. -/
theorem sum_real_measure_closedCell [Fintype ι] [Nonempty ι]
    {ρ : Measure (E d)} [IsFiniteMeasure ρ] (hρ : ρ ≪ volume)
    {K : Set (E d)} (hK : IsClosed K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y) :
    (∑ i, ρ.real (closedCell K y c i)) = ρ.real K := by
  have h := sum_integral_closedCell hρ hK y c hy
    (f := fun _ => (1 : ℝ)) (integrable_const 1)
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ,
    smul_eq_mul, mul_one] using h

/-- Injective sites discharge the null-tie premise in strict activation. -/
theorem exists_strict_active_interior_of_injective [Countable ι]
    {K : Set (E d)} (hK : Convex ℝ K) (y : ι → E d) (c : ι → ℝ)
    (hy : Function.Injective y) (i : ι) (hpos : volume (closedCell K y c i) ≠ 0) :
    ∃ x ∈ interior K, ∀ j, j ≠ i →
      inner ℝ x (y j) + c j < inner ℝ x (y i) + c i := by
  apply exists_strict_active_interior hK y c i hpos
  filter_upwards [ae_affine_tie_implies_slopes_eq volume y c] with x hx
  intro j hji heq
  exact hji (hy (hx j i heq))

/-- Positive cell mass for an absolutely continuous source already guarantees a
strictly active interior point. -/
theorem exists_strict_active_interior_of_mass [Countable ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume) {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (i : ι) (hpos : ρ (closedCell K y c i) ≠ 0) :
    ∃ x ∈ interior K, ∀ j, j ≠ i →
      inner ℝ x (y j) + c j < inner ℝ x (y i) + c i := by
  apply exists_strict_active_interior_of_injective hK y c hy i
  exact fun hnull => hpos (hρ hnull)

/-- Every equality plane between positive-mass cells cuts the interior of the source. -/
theorem exists_equality_interior_of_positive_cells [Countable ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume) {K : Set (E d)} (hK : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    {i j : ι} (hij : i ≠ j)
    (hi : ρ (closedCell K y c i) ≠ 0) (hj : ρ (closedCell K y c j) ≠ 0) :
    ∃ x ∈ interior K, inner ℝ x (y i) + c i = inner ℝ x (y j) + c j := by
  obtain ⟨p, hp, hpi⟩ := exists_strict_active_interior_of_mass hρ hK y c hy i hi
  obtain ⟨q, hq, hqj⟩ := exists_strict_active_interior_of_mass hρ hK y c hy j hj
  exact exists_affine_equality_interior hK hq hp (hqj i hij) (hpi j hij.symm)

end CellGeometry
end Problem358

end

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Problem358.CellGeometry

variable {d : ℕ} {ι : Type*}

/-- With distinct slopes, any maximizing index selects the closed affine cell
almost everywhere. No measurability of the supplied selector is required. -/
theorem ae_fiber_eq_closedCell [Countable ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (k : E d → ι)
    (hk : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    {x | k x = i} =ᵐ[uniformMeasure K] closedCell K y c i := by
  filter_upwards [UniformSource.ae_mem hK,
    uniform_ae_affine_tie_implies_slopes_eq K y c, hk] with x hx ht hk
  apply propext
  constructor
  · intro hi
    exact ⟨hx, fun j => hi ▸ hk j⟩
  · intro hi
    apply hy
    exact ht (k x) i (le_antisymm (hi.2 (k x)) (hk i))

/-- Closed-cell masses are exactly the masses of any maximizing selector. -/
theorem measure_fiber_eq_closedCell [Countable ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (k : E d → ι)
    (hk : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    uniformMeasure K {x | k x = i} =
      uniformMeasure K (closedCell K y c i) :=
  measure_congr (ae_fiber_eq_closedCell hK y c hy k hk i)

/-- The real-valued mass form used in the moving-potential energy estimate. -/
theorem real_fiber_eq_closedCell [Countable ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : ι → E d) (c : ι → ℝ) (hy : Function.Injective y)
    (k : E d → ι)
    (hk : ∀ᵐ x ∂uniformMeasure K, ∀ j,
      ⟪x, y j⟫ + c j ≤ ⟪x, y (k x)⟫ + c (k x)) (i : ι) :
    (uniformMeasure K).real {x | k x = i} =
      (uniformMeasure K).real (closedCell K y c i) :=
  congrArg ENNReal.toReal (measure_fiber_eq_closedCell hK y c hy k hk i)

/-- A single globally measurable selector works for all parameters. Its masses
agree with closed-cell masses at every parameter with distinct slopes, so no
injectivity at endpoint parameters or outside the time interval is imposed. -/
theorem exists_joint_measurable_selector_closedCell_masses
    {P : Type*} [MeasurableSpace P] [MeasurableSpace ι]
    [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : P → ι → E d) (c : P → ι → ℝ)
    (hy : ∀ i, Measurable (fun p => y p i))
    (hc : ∀ i, Measurable (fun p => c p i)) :
    ∃ k : P × E d → ι, Measurable k ∧
      (∀ p x j, ⟪x, y p j⟫ + c p j ≤
        ⟪x, y p (k (p, x))⟫ + c p (k (p, x))) ∧
      ∀ p, Function.Injective (y p) → ∀ i,
        (uniformMeasure K).real {x | k (p, x) = i} =
          (uniformMeasure K).real (closedCell K (y p) (c p) i) := by
  have hf (i : ι) : Measurable
      (fun p : P × E d => ⟪p.2, y p.1 i⟫ + c p.1 i) :=
    (measurable_snd.inner ((hy i).comp measurable_fst)).add
      ((hc i).comp measurable_fst)
  obtain ⟨k, hk, _, hmax⟩ := exists_measurable_argmax
    (fun i (p : P × E d) => ⟪p.2, y p.1 i⟫ + c p.1 i) hf
  refine ⟨k, hk, fun p x j => hmax (p, x) j, ?_⟩
  intro p hp i
  exact real_fiber_eq_closedCell hK (y p) (c p) hp (fun x => k (p, x))
    (Filter.Eventually.of_forall fun x => hmax (p, x)) i

/-- Prescribed closed-cell masses on a chosen set of parameters are realized by
one jointly measurable selector, even when sites collide elsewhere. -/
theorem exists_joint_measurable_selector_prescribed_masses
    {P : Type*} [MeasurableSpace P] [MeasurableSpace ι]
    [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : MeasurableSet K)
    (y : P → ι → E d) (c m : P → ι → ℝ) (s : Set P)
    (hy : ∀ i, Measurable (fun p => y p i))
    (hc : ∀ i, Measurable (fun p => c p i))
    (hinj : ∀ p ∈ s, Function.Injective (y p))
    (hm : ∀ p ∈ s, ∀ i,
      (uniformMeasure K).real (closedCell K (y p) (c p) i) = m p i) :
    ∃ k : P × E d → ι, Measurable k ∧
      (∀ p x j, ⟪x, y p j⟫ + c p j ≤
        ⟪x, y p (k (p, x))⟫ + c p (k (p, x))) ∧
      ∀ p ∈ s, ∀ i, (uniformMeasure K).real {x | k (p, x) = i} = m p i := by
  obtain ⟨k, hk, hmax, hmass⟩ :=
    exists_joint_measurable_selector_closedCell_masses hK y c hy hc
  exact ⟨k, hk, hmax, fun p hp i => (hmass p (hinj p hp) i).trans (hm p hp i)⟩

end Problem358.CellGeometry

end

end OAI
