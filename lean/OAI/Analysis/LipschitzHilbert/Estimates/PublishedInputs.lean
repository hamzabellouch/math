import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace OAI

/-!
# Published inputs for the Lipschitz-direction Hilbert transform

The two classical estimates used by the manuscript are stated as propositions.
Their deterministic consequences make the quantifiers needed for the
finite rectangle and martingale applications explicit.

* Lacey--Li, *On a conjecture of E. M. Stein on the Hilbert transform on
  vector fields*, Memoirs AMS 205 (2010), no. 965, result 1.10 and equation
  (1.11); DOI 10.1090/S0065-9266-10-00572-7. In the author version
  arXiv:0704.0808 these occur on printed p. 3, with the finite-family proof
  in Chapter 3. This is the published form of arXiv:math/0601213v2,
  Theorem 1.4. We use the finite admissible-rectangle weak `(2,2)` estimate.
* Zorin-Kranich, *Weighted Lépingle inequality*, Bernoulli 26 (2020),
  2311--2318, Theorem 1.1, with `p = 2`, `r = 3`, and weight one.
  We use only real-valued finite martingales on probability spaces.

The deterministic consequences below make the quantifiers relevant to the
application explicit: a union of high-average rectangles, and a variation
sum whose increasing indices may be chosen separately at each point.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace LipschitzHilbert

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A closed orthogonal rectangle; `long` and `short` are full side lengths. -/
structure Rectangle where
  center : Plane
  axes : OrthonormalBasis (Fin 2) ℝ Plane
  long : ℝ
  short : ℝ
  short_pos : 0 < short
  short_le_long : short ≤ long

namespace Rectangle

def carrier (R : Rectangle) : Set Plane :=
  {x | |R.axes.repr (x - R.center) 0| ≤ R.long / 2 ∧
    |R.axes.repr (x - R.center) 1| ≤ R.short / 2}

theorem measurableSet_carrier (R : Rectangle) : MeasurableSet R.carrier := by
  have h (i : Fin 2) : Continuous (fun x : Plane => R.axes.repr (x - R.center) i) :=
    (PiLp.continuous_apply 2 _ i).comp (R.axes.repr.continuous.comp (continuous_id.sub continuous_const))
  exact ((isClosed_le (h 0).abs continuous_const).inter
    (isClosed_le (h 1).abs continuous_const)).measurableSet

/-- The arc of total angular length `short / long` about the long-side direction.
The field is separately required to have unit norm. -/
def popularSet (R : Rectangle) (v : Plane → Plane) : Set Plane :=
  {x ∈ R.carrier | Real.cos (R.short / (2 * R.long)) ≤ inner ℝ (v x) (R.axes 0)}

/-- Admissibility uses the long-side length restriction, with no restriction when `K = 0`. -/
def Admissible (R : Rectangle) (v : Plane → Plane) (K δ : ℝ≥0) : Prop :=
  100 * (K : ℝ) * R.long ≤ 1 ∧
    (δ : ℝ≥0∞) * volume R.carrier ≤ volume (R.popularSet v)

def average (R : Rectangle) (h : Plane → ℝ) : ℝ≥0∞ :=
  (volume R.carrier)⁻¹ * ∫⁻ x in R.carrier, ‖h x‖ₑ

end Rectangle

/-- The finite-rectangle maximal function appearing in the needed specialization. -/
def rectangleMaximum {ι : Type*} [Fintype ι] (R : ι → Rectangle)
    (h : Plane → ℝ) (x : Plane) : ℝ≥0∞ :=
  by
    classical
    exact Finset.univ.sup fun i => if x ∈ (R i).carrier then (R i).average h else 0

/-- Squared `L²` size; using the nonnegative integral also covers intermediate expressions. -/
def squareIntegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (h : Ω → ℝ) : ℝ≥0∞ := ∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ

/-- Lacey--Li, published result 1.10 / equation (1.11), specialized to finite
families in squared weak-type form (also arXiv:math/0601213v2, Theorem 1.4).
`C` is the weak `L²` operator constant before squaring. -/
def LaceyLiInput : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (v : Plane → Plane) (K δ : ℝ≥0),
      LipschitzWith K v → (∀ x, ‖v x‖ = 1) → 0 < δ → δ < 1 →
      ∀ (n : ℕ) (R : Fin n → Rectangle),
        (∀ i, (R i).Admissible v K δ) →
        ∀ (h : Plane → ℝ), MemLp h 2 volume → ∀ t : ℝ≥0, 0 < t →
          (t : ℝ≥0∞) ^ 2 * volume {x | (t : ℝ≥0∞) < rectangleMaximum R h x} ≤
            (C : ℝ≥0∞) ^ 2 / (δ : ℝ≥0∞) * squareIntegral volume h

/-- If every selected rectangle has a high average, their union lies in the level set. -/
theorem rectangle_union_subset_level {ι : Type*} [Fintype ι]
    (R : ι → Rectangle) (h : Plane → ℝ) (t : ℝ≥0)
    (havg : ∀ i, (t : ℝ≥0∞) < (R i).average h) :
    (⋃ i, (R i).carrier) ⊆ {x | (t : ℝ≥0∞) < rectangleMaximum R h x} := by
  classical
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hle : (R i).average h ≤ rectangleMaximum R h x := by
    simpa [rectangleMaximum, hi] using
      (Finset.le_sup (f := fun i => if x ∈ (R i).carrier then (R i).average h else 0)
        (Finset.mem_univ i))
  exact (havg i).trans_le hle

/-- Disjoint popularity witnesses turn a covering bound into a weighted packing
bound. In the manuscript, `w i` is a top rectangle's area and `a` its
popularity lower bound. -/
theorem disjoint_witness_packing {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (E R : ι → Set Ω) (w : ι → ℝ≥0∞) (a : ℝ≥0∞)
    (hmeas : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hsub : ∀ i, E i ⊆ R i) (hsize : ∀ i, a * w i ≤ μ (E i)) :
    a * ∑ i, w i ≤ μ (⋃ i, R i) := by
  classical
  calc
    a * ∑ i, w i = ∑ i, a * w i := Finset.mul_sum _ _ _
    _ ≤ ∑ i, μ (E i) := Finset.sum_le_sum fun i _ => hsize i
    _ = μ (⋃ i, E i) := by rw [measure_iUnion hdisj hmeas, tsum_fintype]
    _ ≤ μ (⋃ i, R i) := measure_mono (Set.iUnion_mono hsub)

/-- The precise covering consequence used for the popular-top count. -/
theorem laceyLi_union_bound (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (v : Plane → Plane) (K δ : ℝ≥0),
        LipschitzWith K v → (∀ x, ‖v x‖ = 1) → 0 < δ → δ < 1 →
        ∀ (n : ℕ) (R : Fin n → Rectangle),
          (∀ i, (R i).Admissible v K δ) →
          ∀ (h : Plane → ℝ), MemLp h 2 volume → ∀ t : ℝ≥0, 0 < t →
            (∀ i, (t : ℝ≥0∞) < (R i).average h) →
            (t : ℝ≥0∞) ^ 2 * volume (⋃ i, (R i).carrier) ≤
              (C : ℝ≥0∞) ^ 2 / (δ : ℝ≥0∞) * squareIntegral volume h := by
  obtain ⟨C, hC, hbound⟩ := hLL
  refine ⟨C, hC, ?_⟩
  intro v K δ hv hu hδ hδ1 n R hR h hh t ht havg
  exact (mul_le_mul' le_rfl (measure_mono (rectangle_union_subset_level R h t havg))).trans
    (hbound v K δ hv hu hδ hδ1 n R hR h hh t ht)

/-- Cubed variation of a finite scalar sequence. Repetitions in the monotone list
allow every shorter partition to be padded to length `N + 1`. -/
def variationCube {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ) (x : Ω) : ℝ≥0∞ :=
  by
    classical
    exact Finset.univ.sup fun p : Fin (N + 1) → Fin (N + 1) =>
      if Monotone p then
        ∑ i : Fin N, ‖F (p i.succ) x - F (p i.castSucc) x‖ₑ ^ 3
      else 0

/-- Lépingle's unweighted scalar `L²` bound for `3`-variation. The constant is
uniform in the probability space, the filtration, and the finite horizon. -/
def LepingleInput : Prop :=
  ∃ C : ℝ≥0, 0 < C ∧
    ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
      IsProbabilityMeasure μ →
      ∀ (ℱ : Filtration ℕ m) (F : ℕ → Ω → ℝ),
        Martingale F ℱ μ → (∀ n, MemLp (F n) 2 μ) → ∀ N : ℕ,
          (∫⁻ x, variationCube F N x ^ (2 / 3 : ℝ) ∂μ) ≤
            (C : ℝ≥0∞) ^ 2 * squareIntegral μ (F N)

/-- Pointwise-selected increasing partitions are controlled by the full variation. -/
theorem selected_variation_le {Ω : Type*} (F : ℕ → Ω → ℝ) (N : ℕ)
    (p : Ω → Fin (N + 1) → Fin (N + 1)) (hp : ∀ x, Monotone (p x)) (x : Ω) :
    (∑ i : Fin N, ‖F (p x i.succ) x - F (p x i.castSucc) x‖ₑ ^ 3) ≤
      variationCube F N x := by
  classical
  simpa [variationCube, hp x] using
    (Finset.le_sup
      (f := fun q : Fin (N + 1) → Fin (N + 1) => if Monotone q then
        ∑ i : Fin N, ‖F (q i.succ) x - F (q i.castSucc) x‖ₑ ^ 3 else 0)
      (Finset.mem_univ (p x)))

/-- The published estimate also permits the endpoints to depend on the point.
No measurability of the selection is needed for the nonnegative upper integral. -/
theorem lepingle_selected_bound (hL : LepingleInput) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (Ω : Type) (m : MeasurableSpace Ω) (μ : Measure Ω),
        IsProbabilityMeasure μ →
        ∀ (ℱ : Filtration ℕ m) (F : ℕ → Ω → ℝ),
          Martingale F ℱ μ → (∀ n, MemLp (F n) 2 μ) → ∀ (N : ℕ)
            (p : Ω → Fin (N + 1) → Fin (N + 1)),
            (∀ x, Monotone (p x)) →
            (∫⁻ x, (∑ i : Fin N,
              ‖F (p x i.succ) x - F (p x i.castSucc) x‖ₑ ^ 3) ^ (2 / 3 : ℝ) ∂μ) ≤
              (C : ℝ≥0∞) ^ 2 * squareIntegral μ (F N) := by
  obtain ⟨C, hC, hbound⟩ := hL
  refine ⟨C, hC, ?_⟩
  intro Ω m μ hμ ℱ F hF hF2 N p hp
  refine (lintegral_mono fun x => ?_).trans (hbound Ω m μ hμ ℱ F hF hF2 N)
  exact ENNReal.rpow_le_rpow (selected_variation_le F N p hp x) (by norm_num)

end LipschitzHilbert

end

end OAI
