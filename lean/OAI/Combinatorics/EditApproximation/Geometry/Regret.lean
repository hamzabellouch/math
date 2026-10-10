import Mathlib

namespace OAI

/-!
# Clipped Bellman regret for edit-distance refinement

The deterministic bound of Lemma `lem:generic-regret` in
Section 7 of *An Almost-Linear Approximation Scheme for Edit Distance*
(manuscript of September 24, 2026) applies to an arbitrary finite set of
children satisfying the Bellman inequality and exact-cost connection
inequality.
-/

namespace EditApproximation

open Finset

/-- Values are clipped at the exact cost only for the regret analysis. -/
def clipped (cost value : ℝ) : ℝ := max cost value

theorem clipped_bellman_bound {ι : Type*} (children : Finset ι)
    (cost value charge : ℝ) (childCost childValue : ι → ℝ)
    (hcost : cost ≤ charge + ∑ i ∈ children, childCost i)
    (hvalue : value ≤ charge + ∑ i ∈ children, childValue i) :
    clipped cost value ≤ charge + ∑ i ∈ children, clipped (childCost i) (childValue i) := by
  apply max_le
  · exact hcost.trans (add_le_add (le_refl charge)
      (sum_le_sum fun i _ => le_max_left _ _))
  · exact hvalue.trans (add_le_add (le_refl charge)
      (sum_le_sum fun i _ => le_max_right _ _))

/-- Clipping preserves the useful endpoint decrease bound even when the
initial estimate itself lies below the true cost. -/
theorem clipped_endpoint_decrease (cost initial final mass gap : ℝ)
    (hmono : final ≤ initial) (hinit : initial ≤ mass)
    (hgapCost : |gap| ≤ cost) (hgapMass : |gap| ≤ mass) :
    clipped cost initial - clipped cost final ≤ mass - |gap| := by
  by_cases h : initial ≤ cost
  · simp only [clipped, max_eq_left h, max_eq_left (hmono.trans h), sub_self]
    exact sub_nonneg.mpr hgapMass
  · have hmax : clipped cost initial = initial := max_eq_right (le_of_not_ge h)
    have hfinal : |gap| ≤ clipped cost final := hgapCost.trans (le_max_left _ _)
    rw [hmax]
    exact sub_le_sub hinit hfinal

/-- Finite-time telescoping of the clipped parent Bellman inequalities.
The summation uses indices `t + 1`, corresponding to manuscript indices
`1, …, S`. -/
theorem generic_regret_telescope {ι : Type*} (children : Finset ι)
    (S : ℕ) (cost charge : ℝ) (childCost : ι → ℝ)
    (parent : ℕ → ℝ) (child : ℕ → ι → ℝ)
    (hsplit : cost ≤ charge + ∑ i ∈ children, childCost i)
    (hbellman : ∀ t < S, parent (t + 1) ≤ charge + ∑ i ∈ children, child t i) :
    ∑ t ∈ range S,
        (clipped cost (parent (t + 1)) - charge -
          ∑ i ∈ children, clipped (childCost i) (child (t + 1) i)) ≤
      ∑ i ∈ children,
        (clipped (childCost i) (child 0 i) - clipped (childCost i) (child S i)) := by
  let total : ℕ → ℝ := fun t => ∑ i ∈ children, clipped (childCost i) (child t i)
  have hstep (t : ℕ) (ht : t < S) :
      clipped cost (parent (t + 1)) - charge - total (t + 1) ≤
        total t - total (t + 1) := by
    have hb := clipped_bellman_bound children cost (parent (t + 1)) charge
      childCost (child t) hsplit (hbellman t ht)
    change clipped cost (parent (t + 1)) ≤ charge + total t at hb
    linarith
  have htel : ∑ t ∈ range S, (total t - total (t + 1)) = total 0 - total S := by
    clear hbellman hstep
    induction S with
    | zero => simp
    | succ S ih =>
      rw [sum_range_succ, ih]
      ring
  calc
    _ ≤ ∑ t ∈ range S, (total t - total (t + 1)) := by
      exact sum_le_sum fun t ht => hstep t (mem_range.mp ht)
    _ = total 0 - total S := htel
    _ = _ := by simp only [total, sum_sub_distrib]

/-- The endpoint terms in generic regret are bounded by the warmup masses
minus the absolute length gaps. -/
theorem generic_regret_mass_bound {ι : Type*} (children : Finset ι)
    (S : ℕ) (cost charge : ℝ) (childCost mass gap : ι → ℝ)
    (parent : ℕ → ℝ) (child : ℕ → ι → ℝ)
    (hsplit : cost ≤ charge + ∑ i ∈ children, childCost i)
    (hbellman : ∀ t < S, parent (t + 1) ≤ charge + ∑ i ∈ children, child t i)
    (hmono : ∀ i ∈ children, child S i ≤ child 0 i)
    (hinit : ∀ i ∈ children, child 0 i ≤ mass i)
    (hgapCost : ∀ i ∈ children, |gap i| ≤ childCost i)
    (hgapMass : ∀ i ∈ children, |gap i| ≤ mass i) :
    ∑ t ∈ range S,
        (clipped cost (parent (t + 1)) - charge -
          ∑ i ∈ children, clipped (childCost i) (child (t + 1) i)) ≤
      ∑ i ∈ children, (mass i - |gap i|) := by
  apply (generic_regret_telescope children S cost charge childCost parent child
    hsplit hbellman).trans
  exact sum_le_sum fun i hi => clipped_endpoint_decrease (childCost i)
    (child 0 i) (child S i) (mass i) (gap i)
    (hmono i hi) (hinit i hi) (hgapCost i hi) (hgapMass i hi)

/-- Since child length gaps add to the parent's gap, their absolute values
give the final bound in manuscript Equation `eq:generic-regret`. -/
theorem sum_mass_sub_abs_le {ι : Type*} (children : Finset ι)
    (mass gap : ι → ℝ) :
    ∑ i ∈ children, (mass i - |gap i|) ≤
      (∑ i ∈ children, mass i) - |∑ i ∈ children, gap i| := by
  rw [sum_sub_distrib]
  exact sub_le_sub_left (abs_sum_le_sum_abs _ _) _

/-- At a comparison node whose predicted normalized length gap is close
to one, almost all warmup mass is accounted for by the absolute gap. -/
theorem predicted_length_gap_bound (W Z gap τ : ℝ)
    (hZ : 0 < Z) (hZW : Z ≤ W) (hτ : 0 ≤ τ)
    (hprediction : 1 - τ < |gap| / Z) :
    W - |gap| ≤ (W - Z) + τ * W := by
  have hp : (1 - τ) * Z < |gap| := (lt_div_iff₀ hZ).mp hprediction
  have hmass : 0 ≤ τ * (W - Z) := mul_nonneg hτ (sub_nonneg.mpr hZW)
  nlinarith

/-- The refined generic bound at a node that is not bad and whose
normalized length-gap predictor lies near one. The parameter `q` is
`H^(-1/4)` in the manuscript. -/
theorem near_length_gap_regret_bound (W Z gap τ q F cost : ℝ)
    (hZ : 0 < Z) (hZW : Z ≤ W) (hτ : 0 ≤ τ)
    (hprediction : 1 - τ < |gap| / Z)
    (hdiscrepancy : W - Z ≤ q * cost)
    (hmass : W ≤ 4 * F * cost) :
    W - |gap| ≤ (q + 4 * τ * F) * cost := by
  have hpred := predicted_length_gap_bound W Z gap τ hZ hZW hτ hprediction
  have hscale := mul_le_mul_of_nonneg_left hmass hτ
  nlinarith

/-- Scalar exponential estimate used in Lemma `lem:entropy`, Equation
`eq:entropy-exponential`. -/
theorem entropy_exponential_bound (κ x : ℝ)
    (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2) (hx : 0 ≤ x) (hxκ : x ≤ κ) :
    Real.exp ((1 - 2 * κ) * x) ≤ 1 + (1 - κ) * x := by
  have h1κ : 0 ≤ 1 - κ := by linarith
  have h1κle : 1 - κ ≤ 1 := by linarith
  have h2κ : 0 ≤ 1 - 2 * κ := by linarith
  have h2κle : 1 - 2 * κ ≤ 1 := by linarith
  have hy : 0 ≤ (1 - κ) * x := mul_nonneg h1κ hx
  have hypos : 0 < 1 + (1 - κ) * x := by linarith
  apply (Real.le_log_iff_exp_le hypos).mp
  have hlog := Real.le_log_one_add_of_nonneg hy
  apply le_trans _ hlog
  apply (le_div_iff₀ (show 0 < (1 - κ) * x + 2 by linarith)).mpr
  have hproduct : (1 - 2 * κ) * (1 - κ) ≤ 1 :=
    (mul_le_mul_of_nonneg_right h2κle h1κ).trans (by simpa using h1κle)
  have hprodκ : (1 - 2 * κ) * (1 - κ) * x ≤ κ :=
    (mul_le_mul_of_nonneg_right hproduct hx).trans (by simpa using hxκ)
  have hfinal : 0 ≤ x * (κ - (1 - 2 * κ) * (1 - κ) * x) :=
    mul_nonneg hx (sub_nonneg.mpr hprodκ)
  have hkx : 0 ≤ κ * x := mul_nonneg hκ hx
  nlinarith

/-- The final telescoping step of Lemma `lem:entropy`. Here `played t`
is the inner product with the chosen distribution, `comparator t` is
the comparator inner product, and `decrement t` is its normalized
decrement. The potential-increment and variational bounds are explicit
internal proof obligations; this theorem does not assume a published
online-learning guarantee. -/
theorem entropy_potential_telescoping (S : ℕ) (η κ bound : ℝ)
    (potential played comparator decrement : ℕ → ℝ)
    (hη : 0 < η) (hκ : 0 ≤ κ)
    (hincrement : ∀ t < S,
      potential (t + 1) - potential t ≤ η * played t)
    (hstart : potential 0 ≤ bound)
    (hcomparator : η * ((∑ t ∈ range S, comparator t) -
        2 * κ * ∑ t ∈ range S, decrement t) ≤ potential S)
    (hdecrement : ∑ t ∈ range S, decrement t ≤ 1) :
    (∑ t ∈ range S, comparator t) - bound / η - 2 * κ ≤
      ∑ t ∈ range S, played t := by
  have htel : ∑ t ∈ range S, (potential (t + 1) - potential t) =
      potential S - potential 0 := by
    clear hincrement hcomparator hdecrement
    induction S with
    | zero => simp
    | succ S ih =>
      rw [sum_range_succ, ih]
      ring
  have hsum : potential S - potential 0 ≤ η * ∑ t ∈ range S, played t := by
    rw [← htel, mul_sum]
    exact sum_le_sum fun t ht => hincrement t (mem_range.mp ht)
  have hdecrement' : η * (2 * κ * ∑ t ∈ range S, decrement t) ≤ η * (2 * κ) := by
    calc
      _ ≤ η * (2 * κ * 1) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hdecrement (by positivity)) hη.le
      _ = _ := by ring
  have hcancel : η * (bound / η) = bound := mul_div_cancel₀ bound hη.ne'
  apply le_of_mul_le_mul_left (a := η) _ hη
  nlinarith

/-- Accumulating the loss from approximate mixture vectors. In the
application, `error = H^(-3)` and the coordinate gains lie in `[-1, 0]`. -/
theorem entropy_approximation_loss (S : ℕ) (bound error : ℝ)
    (exactValue approximateValue : ℕ → ℝ)
    (hexact : bound ≤ ∑ t ∈ range S, exactValue t)
    (happrox : ∀ t < S, exactValue t - error ≤ approximateValue t) :
    bound - S * error ≤ ∑ t ∈ range S, approximateValue t := by
  have hsum : (∑ t ∈ range S, exactValue t) - S * error ≤
      ∑ t ∈ range S, approximateValue t := by
    calc
      _ = ∑ t ∈ range S, (exactValue t - error) := by simp [sum_sub_distrib]
      _ ≤ _ := sum_le_sum fun t ht => happrox t (mem_range.mp ht)
  linarith

/-- Nonnegativity of relative entropy for a finite probability vector and
a strictly positive reference vector. Zero coordinates of the first
vector are allowed and contribute zero. -/
theorem finite_relative_entropy_nonnegative {ι : Type*} (coordinates : Finset ι)
    (p q : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hq : ∀ i ∈ coordinates, 0 < q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1) :
    0 ≤ ∑ i ∈ coordinates, p i * Real.log (p i / q i) := by
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      p i * Real.log (q i / p i) ≤ q i - p i := by
    by_cases hzero : p i = 0
    · simpa [hzero] using (hq i hi).le
    · have hp' : 0 < p i := lt_of_le_of_ne (hp i hi) (Ne.symm hzero)
      have hl := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (div_pos (hq i hi) hp')) hp'.le
      have hcancel : p i * (q i / p i - 1) = q i - p i := by
        field_simp
      rwa [hcancel] at hl
  have hsum : ∑ i ∈ coordinates, p i * Real.log (q i / p i) ≤ 0 := by
    calc
      _ ≤ ∑ i ∈ coordinates, (q i - p i) := sum_le_sum hcoord
      _ = 0 := by rw [sum_sub_distrib, hqsum, hpsum]; ring
  have hneg (i : ι) (hi : i ∈ coordinates) :
      p i * Real.log (p i / q i) = -(p i * Real.log (q i / p i)) := by
    by_cases hzero : p i = 0
    · simp [hzero]
    · rw [Real.log_div hzero (hq i hi).ne', Real.log_div (hq i hi).ne' hzero]
      ring
  calc
    0 ≤ -(∑ i ∈ coordinates, p i * Real.log (q i / p i)) := neg_nonneg.mpr hsum
    _ = ∑ i ∈ coordinates, p i * Real.log (p i / q i) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun i hi => (hneg i hi).symm

/-- The finite Gibbs variational bound used when the innovation
supremum over the actual action hull is extended to the simplex.
This is a proved inequality, with no maximization-oracle assumption. -/
theorem finite_gibbs_variational_bound {ι : Type*} (coordinates : Finset ι)
    (p q gain : ι → ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hq : ∀ i ∈ coordinates, 0 < q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1) :
    (∑ i ∈ coordinates, p i * gain i) -
        (∑ i ∈ coordinates, p i * Real.log (p i / q i)) ≤
      Real.log (∑ i ∈ coordinates, q i * Real.exp (gain i)) := by
  let Z := ∑ i ∈ coordinates, q i * Real.exp (gain i)
  have hs : coordinates.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    simp [he] at hqsum
  have hZ : 0 < Z := sum_pos (fun i hi => mul_pos (hq i hi) (Real.exp_pos _)) hs
  let r : ι → ℝ := fun i => q i * Real.exp (gain i) / Z
  have hr (i : ι) (hi : i ∈ coordinates) : 0 < r i :=
    div_pos (mul_pos (hq i hi) (Real.exp_pos _)) hZ
  have hrsum : ∑ i ∈ coordinates, r i = 1 := by
    simp only [r]
    rw [← sum_div]
    change Z / Z = 1
    exact div_self hZ.ne'
  have hKL := finite_relative_entropy_nonnegative coordinates p r hp hr hpsum hrsum
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      p i * gain i - p i * Real.log (p i / q i) =
        p i * Real.log Z - p i * Real.log (p i / r i) := by
    by_cases hzero : p i = 0
    · simp [hzero]
    · have hlogr : Real.log (r i) = Real.log (q i) + gain i - Real.log Z := by
        change Real.log (q i * Real.exp (gain i) / Z) = _
        rw [Real.log_div (mul_pos (hq i hi) (Real.exp_pos _)).ne' hZ.ne',
          Real.log_mul (hq i hi).ne' (Real.exp_pos _).ne', Real.log_exp]
      rw [Real.log_div hzero (hq i hi).ne', Real.log_div hzero (hr i hi).ne', hlogr]
      ring
  have hidentity :
      (∑ i ∈ coordinates, p i * gain i) -
          (∑ i ∈ coordinates, p i * Real.log (p i / q i)) =
        Real.log Z - ∑ i ∈ coordinates, p i * Real.log (p i / r i) := by
    rw [← sum_sub_distrib]
    calc
      _ = ∑ i ∈ coordinates,
          (p i * Real.log Z - p i * Real.log (p i / r i)) := sum_congr rfl hcoord
      _ = _ := by rw [sum_sub_distrib, ← sum_mul, hpsum, one_mul]
  change _ ≤ Real.log Z
  rw [hidentity]
  exact sub_le_self _ hKL

/-- The small-decrement logarithmic moment bound in the entropy
innovation argument. The bound on `η * innovation i` is the only
smallness requirement needed here. -/
theorem entropy_small_increment_logsum {ι : Type*} (coordinates : Finset ι)
    (p innovation : ι → ℝ) (η κ : ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hinnovation : ∀ i ∈ coordinates, 0 ≤ η * innovation i)
    (hsmall : ∀ i ∈ coordinates, η * innovation i ≤ κ) :
    Real.log (∑ i ∈ coordinates,
        p i * Real.exp (η * (1 - 2 * κ) * innovation i)) ≤
      η * (1 - κ) * ∑ i ∈ coordinates, p i * innovation i := by
  let Z := ∑ i ∈ coordinates, p i * Real.exp (η * (1 - 2 * κ) * innovation i)
  have hs : coordinates.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    simp [he] at hpsum
  have hZ : 0 < Z := sum_pos (fun i hi => mul_pos (hp i hi) (Real.exp_pos _)) hs
  have hbound : Z ≤ 1 + η * (1 - κ) * ∑ i ∈ coordinates, p i * innovation i := by
    calc
      _ ≤ ∑ i ∈ coordinates, p i * (1 + (1 - κ) * (η * innovation i)) := by
        apply sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (hp i hi).le
        rw [show η * (1 - 2 * κ) * innovation i =
          (1 - 2 * κ) * (η * innovation i) by ring]
        exact entropy_exponential_bound κ (η * innovation i) hκ hκhalf
          (hinnovation i hi) (hsmall i hi)
      _ = _ := by
        simp_rw [mul_add, mul_one]
        rw [sum_add_distrib, hpsum]
        congr 1
        rw [mul_sum]
        apply sum_congr rfl
        intro i hi
        ring
  exact (Real.log_le_sub_one_of_pos hZ).trans (by linarith)

/-- Equal probability mass in every child block makes every blockwise
constant vector have the same inner product with the two distributions. -/
theorem fixed_block_mass_inner_product {ι β : Type*} [Fintype β] [DecidableEq β]
    (coordinates : Finset ι) (block : ι → β) (p q : ι → ℝ) (baseline : β → ℝ)
    (hblock : ∀ b, (∑ i ∈ coordinates with block i = b, p i) =
      ∑ i ∈ coordinates with block i = b, q i) :
    (∑ i ∈ coordinates, p i * baseline (block i)) =
      ∑ i ∈ coordinates, q i * baseline (block i) := by
  classical
  have hdecompose (r : ι → ℝ) :
      (∑ b : β, baseline b * ∑ i ∈ coordinates with block i = b, r i) =
        ∑ i ∈ coordinates, r i * baseline (block i) := by
    simp only [mul_sum, sum_filter, mul_ite, mul_zero]
    rw [sum_comm]
    simp [mul_comm]
  rw [← hdecompose p, ← hdecompose q]
  exact sum_congr rfl fun b _ => congrArg (baseline b * ·) (hblock b)

/-- The innovation variational inequality for the actual action hull.
Its fixed block masses are used exactly through `hfixedMass`: the
blockwise minimum vector `baseline` has the same inner product with
every feasible vector. The residual `innovation` has small range.

Combined with the entropy penalty at a positive maximizer, this bounds
the potential increment without replacing the action hull by a simplex
in the algorithm. -/
theorem entropy_innovation_variational_bound {ι : Type*} (coordinates : Finset ι)
    (p q decrement baseline innovation : ι → ℝ) (η κ : ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hq : ∀ i ∈ coordinates, 0 ≤ q i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1)
    (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hbaseline : ∀ i ∈ coordinates, 0 ≤ baseline i)
    (hdecomposition : ∀ i ∈ coordinates, decrement i = baseline i + innovation i)
    (hfixedMass : (∑ i ∈ coordinates, q i * baseline i) =
      ∑ i ∈ coordinates, p i * baseline i)
    (hinnovation : ∀ i ∈ coordinates, 0 ≤ η * innovation i)
    (hsmall : ∀ i ∈ coordinates, η * innovation i ≤ κ) :
    η * (1 - 2 * κ) * (∑ i ∈ coordinates, q i * decrement i) -
        (∑ i ∈ coordinates, q i * Real.log (q i / p i)) ≤
      η * (1 - κ) * ∑ i ∈ coordinates, p i * decrement i := by
  have hgibbs := finite_gibbs_variational_bound coordinates q p
    (fun i => η * (1 - 2 * κ) * innovation i) hq hp hqsum hpsum
  have hlog := entropy_small_increment_logsum coordinates p innovation η κ
    hp hpsum hκ hκhalf hinnovation hsmall
  have hgain : (∑ i ∈ coordinates, q i * (η * (1 - 2 * κ) * innovation i)) =
      η * (1 - 2 * κ) * ∑ i ∈ coordinates, q i * innovation i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hgain] at hgibbs
  have hresidual := hgibbs.trans hlog
  have hpsumDecrement : (∑ i ∈ coordinates, p i * decrement i) =
      (∑ i ∈ coordinates, p i * baseline i) +
        ∑ i ∈ coordinates, p i * innovation i := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [hdecomposition i hi, mul_add]
  have hqsumDecrement : (∑ i ∈ coordinates, q i * decrement i) =
      (∑ i ∈ coordinates, p i * baseline i) +
        ∑ i ∈ coordinates, q i * innovation i := by
    rw [← hfixedMass, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    rw [hdecomposition i hi, mul_add]
  have hmass : 0 ≤ ∑ i ∈ coordinates, p i * baseline i :=
    sum_nonneg fun i hi => mul_nonneg (hp i hi).le (hbaseline i hi)
  have hcorrection : 0 ≤ η * κ * ∑ i ∈ coordinates, p i * baseline i :=
    mul_nonneg (mul_nonneg hη hκ) hmass
  rw [hpsumDecrement, hqsumDecrement]
  nlinarith

/-- First-order optimality of entropy plus a linear objective along a
feasible segment. The segment-maximization hypothesis is exactly what
an entropy maximizer on a convex action hull supplies. -/
theorem entropy_first_order_on_segment {ι : Type*} (coordinates : Finset ι)
    (p q objective : ι → ℝ) (η : ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hmax : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∑ i ∈ coordinates,
        (Real.negMulLog (p i + t * (q i - p i)) +
          η * objective i * (p i + t * (q i - p i)))) ≤
      ∑ i ∈ coordinates, (Real.negMulLog (p i) + η * objective i * p i)) :
    ∑ i ∈ coordinates,
      (-Real.log (p i) - 1 + η * objective i) * (q i - p i) ≤ 0 := by
  let f : ℝ → ℝ := fun t => ∑ i ∈ coordinates,
    (Real.negMulLog (p i + t * (q i - p i)) +
      η * objective i * (p i + t * (q i - p i)))
  have hd : HasDerivAt f (∑ i ∈ coordinates,
      (-Real.log (p i) - 1 + η * objective i) * (q i - p i)) 0 := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hline : HasDerivAt (fun t : ℝ => p i + t * (q i - p i)) (q i - p i) 0 := by
      simpa using (hasDerivAt_const (0 : ℝ) (p i)).fun_add
        ((hasDerivAt_id (0 : ℝ)).mul_const (q i - p i))
    have hneg : HasDerivAt Real.negMulLog (-Real.log (p i) - 1)
        (p i + 0 * (q i - p i)) := by
      simpa using Real.hasDerivAt_negMulLog (hp i hi).ne'
    have hent := hneg.comp 0 hline
    have hent' : HasDerivAt (fun t : ℝ => Real.negMulLog (p i + t * (q i - p i)))
        ((-Real.log (p i) - 1) * (q i - p i)) 0 := by
      convert! hent using 1
    convert hent'.add (hline.const_mul (η * objective i)) using 1
    ring
  have hmaxOn : IsMaxOn f (Set.Icc (0 : ℝ) 1) 0 := by
    intro t ht
    simpa [f] using hmax t ht.1 ht.2
  have htangent : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    have hsegment : segment ℝ (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := by
      rw [segment_eq_Icc (by norm_num)]
    simpa using sub_mem_posTangentConeAt_of_segment_subset hsegment
  have hnonpos := hmaxOn.isLocalMaxOn.hasFDerivWithinAt_nonpos
    hd.hasFDerivAt.hasFDerivWithinAt htangent
  simpa using hnonpos

/-- The exact relative-entropy penalty at a positive first-order
maximizer. This proves manuscript Equation `eq:entropy-penalty` once
the first-order condition is supplied by
`entropy_first_order_on_segment`. -/
theorem entropy_penalty_of_first_order {ι : Type*} (coordinates : Finset ι)
    (p q objective : ι → ℝ) (η : ℝ)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1)
    (hfirst : ∑ i ∈ coordinates,
      (-Real.log (p i) - 1 + η * objective i) * (q i - p i) ≤ 0) :
    (∑ i ∈ coordinates, Real.negMulLog (q i)) +
        η * (∑ i ∈ coordinates, objective i * q i) ≤
      (∑ i ∈ coordinates, Real.negMulLog (p i)) +
        η * (∑ i ∈ coordinates, objective i * p i) -
        (∑ i ∈ coordinates, q i * Real.log (q i / p i)) := by
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      Real.negMulLog (q i) - Real.negMulLog (p i) +
          η * objective i * (q i - p i) + q i * Real.log (q i / p i) =
        (-Real.log (p i) - 1 + η * objective i) * (q i - p i) + (q i - p i) := by
    by_cases hqzero : q i = 0
    · simp only [hqzero, Real.negMulLog, zero_mul, zero_div]
      ring
    · rw [Real.log_div hqzero (hp i hi).ne']
      simp only [Real.negMulLog]
      ring
  have hidentity :
      (∑ i ∈ coordinates,
        (Real.negMulLog (q i) - Real.negMulLog (p i) +
          η * objective i * (q i - p i) + q i * Real.log (q i / p i))) =
        ∑ i ∈ coordinates,
          (-Real.log (p i) - 1 + η * objective i) * (q i - p i) := by
    calc
      _ = ∑ i ∈ coordinates,
          ((-Real.log (p i) - 1 + η * objective i) * (q i - p i) + (q i - p i)) :=
        sum_congr rfl hcoord
      _ = _ := by rw [sum_add_distrib, sum_sub_distrib, hqsum, hpsum]; ring
  have hbound := hidentity.trans_le hfirst
  simp only [sum_add_distrib, sum_sub_distrib, mul_sub] at hbound
  have hlinear : (∑ i ∈ coordinates, η * objective i * q i) =
      η * ∑ i ∈ coordinates, objective i * q i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  have hlinear' : (∑ i ∈ coordinates, η * objective i * p i) =
      η * ∑ i ∈ coordinates, objective i * p i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hlinear, hlinear'] at hbound
  linarith

/-- An entropy maximizer cannot have a zero coordinate when a strictly
positive feasible vector is available. Only maximization on the
segments to that vector is needed, so this applies to the actual finite
action hull in the manuscript. -/
theorem entropy_maximizer_positive {ι : Type*} (coordinates : Finset ι)
    (p witness objective : ι → ℝ) (η : ℝ)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hw : ∀ i ∈ coordinates, 0 < witness i)
    (hmax : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∑ i ∈ coordinates,
        (Real.negMulLog ((1 - t) * p i + t * witness i) +
          η * objective i * ((1 - t) * p i + t * witness i))) ≤
      ∑ i ∈ coordinates, (Real.negMulLog (p i) + η * objective i * p i)) :
    ∀ i ∈ coordinates, 0 < p i := by
  classical
  intro k hk
  by_contra hnot
  have hpk : p k = 0 := le_antisymm (le_of_not_gt hnot) (hp k hk)
  let value : ι → ℝ → ℝ := fun i x => Real.negMulLog x + η * objective i * x
  let A := (∑ i ∈ coordinates, value i (witness i)) -
    ∑ i ∈ coordinates, value i (p i)
  let t := Real.exp (-(|A| / witness k + 1))
  have ht : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hratio : 0 ≤ |A| / witness k := div_nonneg (abs_nonneg _) (hw k hk).le
    linarith
  have htlog : Real.log t = -(|A| / witness k + 1) := Real.log_exp _
  have hpositive : 0 < t * A + witness k * Real.negMulLog t := by
    have hbracket : 0 < A + |A| + witness k := by
      have := neg_le_abs A
      linarith [hw k hk]
    calc
      _ = t * (A + |A| + witness k) := by
        rw [Real.negMulLog, htlog]
        field_simp [(hw k hk).ne']
        ring
      _ > 0 := mul_pos ht hbracket
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      (1 - t) * value i (p i) + t * value i (witness i) ≤
        value i ((1 - t) * p i + t * witness i) := by
    have hconcave := Real.concaveOn_negMulLog.2 (hp i hi) (hw i hi).le
      (show 0 ≤ 1 - t by linarith) ht.le (show (1 - t) + t = 1 by ring)
    simp only [smul_eq_mul] at hconcave
    dsimp only [value]
    nlinarith
  have hkexact :
      (1 - t) * value k (p k) + t * value k (witness k) +
          witness k * Real.negMulLog t =
        value k ((1 - t) * p k + t * witness k) := by
    simp only [hpk, value, mul_zero, Real.negMulLog_zero, zero_add, add_zero]
    rw [Real.negMulLog_mul]
    ring
  let lower : ι → ℝ := fun i => (1 - t) * value i (p i) + t * value i (witness i)
  let upper : ι → ℝ := fun i => value i ((1 - t) * p i + t * witness i)
  have hothers : ∑ i ∈ coordinates.erase k, lower i ≤
      ∑ i ∈ coordinates.erase k, upper i :=
    sum_le_sum fun i hi => hcoord i (mem_of_mem_erase hi)
  have hwhole : (∑ i ∈ coordinates.erase k, lower i) + lower k +
      witness k * Real.negMulLog t ≤ (∑ i ∈ coordinates.erase k, upper i) + upper k := by
    change lower k + witness k * Real.negMulLog t = upper k at hkexact
    linarith
  rw [sum_erase_add coordinates lower hk, sum_erase_add coordinates upper hk] at hwhole
  have hlower : (∑ i ∈ coordinates, lower i) =
      (1 - t) * (∑ i ∈ coordinates, value i (p i)) +
        t * ∑ i ∈ coordinates, value i (witness i) := by
    simp only [lower, sum_add_distrib, ← mul_sum]
  rw [hlower] at hwhole
  have hupper : ∑ i ∈ coordinates, upper i ≤ ∑ i ∈ coordinates, value i (p i) :=
    hmax t ht.le ht1
  have hfinal := hwhole.trans hupper
  dsimp only [A] at hpositive
  nlinarith

/-- Entropy is nonnegative on a finite probability vector. -/
theorem finite_entropy_nonnegative {ι : Type*} (coordinates : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1) :
    0 ≤ ∑ i ∈ coordinates, Real.negMulLog (p i) := by
  apply sum_nonneg
  intro i hi
  apply Real.negMulLog_nonneg (hp i hi)
  exact (single_le_sum hp hi).trans hpsum.le

/-- The entropy of a finite probability vector is at most the logarithm
of the number of listed coordinates. -/
theorem finite_entropy_le_log_card {ι : Type*} (coordinates : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1) :
    (∑ i ∈ coordinates, Real.negMulLog (p i)) ≤ Real.log coordinates.card := by
  have hs : coordinates.Nonempty := by
    apply Finset.nonempty_of_ne_empty
    intro he
    simp [he] at hpsum
  have hn : 0 < (coordinates.card : ℝ) := Nat.cast_pos.mpr hs.card_pos
  let uniform : ι → ℝ := fun _ => 1 / coordinates.card
  have hu : ∀ i ∈ coordinates, 0 < uniform i := fun _ _ => div_pos zero_lt_one hn
  have husum : ∑ i ∈ coordinates, uniform i = 1 := by
    simp only [uniform, sum_const, nsmul_eq_mul]
    field_simp
  have hKL := finite_relative_entropy_nonnegative coordinates p uniform hp hu hpsum husum
  have hcoord (i : ι) (hi : i ∈ coordinates) :
      p i * Real.log (p i / uniform i) =
        -Real.negMulLog (p i) + p i * Real.log coordinates.card := by
    by_cases hzero : p i = 0
    · simp [hzero]
    · rw [Real.log_div hzero (hu i hi).ne']
      simp only [uniform, one_div, Real.log_inv, Real.negMulLog]
      ring
  have hid : (∑ i ∈ coordinates, p i * Real.log (p i / uniform i)) =
      -(∑ i ∈ coordinates, Real.negMulLog (p i)) + Real.log coordinates.card := by
    calc
      _ = ∑ i ∈ coordinates, (-Real.negMulLog (p i) + p i * Real.log coordinates.card) :=
        sum_congr rfl hcoord
      _ = _ := by rw [sum_add_distrib, sum_neg_distrib, ← sum_mul, hpsum, one_mul]
  rw [hid] at hKL
  linarith

/-- Entropy plus the linear objective, with the manuscript's scaling. -/
noncomputable def entropyValue {ι : Type*} (coordinates : Finset ι)
    (η : ℝ) (objective p : ι → ℝ) : ℝ :=
  ∑ i ∈ coordinates, (Real.negMulLog (p i) + η * objective i * p i)

theorem entropyValue_eq {ι : Type*} (coordinates : Finset ι)
    (η : ℝ) (objective p : ι → ℝ) :
    entropyValue coordinates η objective p =
      (∑ i ∈ coordinates, Real.negMulLog (p i)) +
        η * ∑ i ∈ coordinates, objective i * p i := by
  unfold entropyValue
  rw [sum_add_distrib, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i hi
  ring

/-- The entropy potential is attained on every nonempty compact action
hull, since the zero-coordinate convention gives continuous entropy. -/
theorem exists_entropy_maximizer {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η : ℝ) (objective : ι → ℝ)
    (hcompact : IsCompact Q) (hne : Q.Nonempty) :
    ∃ p ∈ Q, IsMaxOn (entropyValue coordinates η objective) Q p := by
  apply hcompact.exists_isMaxOn hne
  unfold entropyValue
  fun_prop

/-- Positivity of the entropy maximizer on a convex feasible hull with
a positive feasible witness. -/
theorem entropy_hull_maximizer_positive {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η : ℝ) (objective p witness : ι → ℝ)
    (hconvex : Convex ℝ Q) (hpQ : p ∈ Q) (hwQ : witness ∈ Q)
    (hp : ∀ i ∈ coordinates, 0 ≤ p i)
    (hw : ∀ i ∈ coordinates, 0 < witness i)
    (hmax : IsMaxOn (entropyValue coordinates η objective) Q p) :
    ∀ i ∈ coordinates, 0 < p i := by
  apply entropy_maximizer_positive coordinates p witness objective η hp hw
  intro t ht ht1
  have hmem := hconvex hpQ hwQ (show 0 ≤ 1 - t by linarith) ht
    (show (1 - t) + t = 1 by ring)
  simpa [entropyValue, Pi.smul_apply, Pi.add_apply, smul_eq_mul] using hmax hmem

/-- The exact KL penalty holds for every competitor in the action hull,
including competitors with zero coordinates. -/
theorem entropy_hull_penalty {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η : ℝ) (objective p q : ι → ℝ)
    (hconvex : Convex ℝ Q) (hpQ : p ∈ Q) (hqQ : q ∈ Q)
    (hp : ∀ i ∈ coordinates, 0 < p i)
    (hpsum : ∑ i ∈ coordinates, p i = 1)
    (hqsum : ∑ i ∈ coordinates, q i = 1)
    (hmax : IsMaxOn (entropyValue coordinates η objective) Q p) :
    entropyValue coordinates η objective q ≤ entropyValue coordinates η objective p -
      ∑ i ∈ coordinates, q i * Real.log (q i / p i) := by
  have hfirst := entropy_first_order_on_segment coordinates p q objective η hp
    (by
      intro t ht ht1
      have hmem := hconvex hpQ hqQ (show 0 ≤ 1 - t by linarith) ht
        (show (1 - t) + t = 1 by ring)
      have heq : (1 - t) • p + t • q = fun i => p i + t * (q i - p i) := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [heq] at hmem
      exact hmax hmem)
  rw [entropyValue_eq, entropyValue_eq]
  exact entropy_penalty_of_first_order coordinates p q objective η hp hpsum hqsum hfirst

theorem entropyValue_add_scaled {ι : Type*} (coordinates : Finset ι)
    (η scale : ℝ) (objective increment p : ι → ℝ) :
    entropyValue coordinates η (fun i => objective i + scale * increment i) p =
      entropyValue coordinates η objective p +
        η * scale * ∑ i ∈ coordinates, increment i * p i := by
  rw [entropyValue_eq, entropyValue_eq]
  simp_rw [add_mul]
  rw [sum_add_distrib]
  have hsum : (∑ i ∈ coordinates, scale * increment i * p i) =
      scale * ∑ i ∈ coordinates, increment i * p i := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

/-- One complete optimistic entropy-potential step on the actual hull.
The old objective and its predicted increment are arbitrary and may
have negative coordinates. Only the residual decrement is small. -/
theorem entropy_hull_potential_step {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (η κ : ℝ)
    (old gain decrement baseline innovation oldLeader predicted newLeader : ι → ℝ)
    (hconvex : Convex ℝ Q)
    (hpredQ : predicted ∈ Q) (hnewQ : newLeader ∈ Q)
    (hpred : ∀ i ∈ coordinates, 0 < predicted i)
    (hnew : ∀ i ∈ coordinates, 0 ≤ newLeader i)
    (hpredsum : ∑ i ∈ coordinates, predicted i = 1)
    (hnewsum : ∑ i ∈ coordinates, newLeader i = 1)
    (holdMax : IsMaxOn (entropyValue coordinates η old) Q oldLeader)
    (hpredMax : IsMaxOn
      (entropyValue coordinates η (fun i => old i + gain i)) Q predicted)
    (hη : 0 ≤ η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hbaseline : ∀ i ∈ coordinates, 0 ≤ baseline i)
    (hdecomposition : ∀ i ∈ coordinates, decrement i = baseline i + innovation i)
    (hfixedMass : (∑ i ∈ coordinates, newLeader i * baseline i) =
      ∑ i ∈ coordinates, predicted i * baseline i)
    (hinnovation : ∀ i ∈ coordinates, 0 ≤ η * innovation i)
    (hsmall : ∀ i ∈ coordinates, η * innovation i ≤ κ) :
    entropyValue coordinates η
        (fun i => old i + gain i + (1 - 2 * κ) * decrement i) newLeader -
        entropyValue coordinates η old oldLeader ≤
      η * ∑ i ∈ coordinates, (gain i + (1 - κ) * decrement i) * predicted i := by
  have hpenalty := entropy_hull_penalty coordinates Q η (fun i => old i + gain i)
    predicted newLeader hconvex hpredQ hnewQ hpred hpredsum hnewsum hpredMax
  have hinnovationBound := entropy_innovation_variational_bound coordinates predicted
    newLeader decrement baseline innovation η κ hpred hnew hpredsum hnewsum
    hη hκ hκhalf hbaseline hdecomposition hfixedMass hinnovation hsmall
  have hpredComm : (∑ i ∈ coordinates, predicted i * decrement i) =
      ∑ i ∈ coordinates, decrement i * predicted i :=
    sum_congr rfl fun i _ => mul_comm _ _
  have hnewComm : (∑ i ∈ coordinates, newLeader i * decrement i) =
      ∑ i ∈ coordinates, decrement i * newLeader i :=
    sum_congr rfl fun i _ => mul_comm _ _
  rw [hpredComm, hnewComm] at hinnovationBound
  have hnewValue := entropyValue_add_scaled coordinates η (1 - 2 * κ)
    (fun i => old i + gain i) decrement newLeader
  have hpredValue := entropyValue_add_scaled coordinates η 1 old gain predicted
  simp only [one_mul, mul_one] at hpredValue
  have holdBound := holdMax hpredQ
  change entropyValue coordinates η old predicted ≤
    entropyValue coordinates η old oldLeader at holdBound
  have hsum : (∑ i ∈ coordinates, (gain i + (1 - κ) * decrement i) * predicted i) =
      (∑ i ∈ coordinates, gain i * predicted i) +
        (1 - κ) * ∑ i ∈ coordinates, decrement i * predicted i := by
    simp_rw [add_mul]
    rw [sum_add_distrib]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  nlinarith

/-- The accumulated optimistic objective before a time index. -/
noncomputable def optimisticHistory {ι : Type*} (κ : ℝ)
    (gain decrement : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  ∑ j ∈ range t, (gain j i + (1 - 2 * κ) * decrement j i)

theorem optimisticHistory_succ {ι : Type*} (κ : ℝ)
    (gain decrement : ℕ → ι → ℝ) (t : ℕ) :
    optimisticHistory κ gain decrement (t + 1) =
      fun i => optimisticHistory κ gain decrement t i + gain t i +
        (1 - 2 * κ) * decrement t i := by
  ext i
  simp only [optimisticHistory, sum_range_succ]
  ring

theorem optimisticHistory_inner_product {ι : Type*} (coordinates : Finset ι)
    (κ : ℝ) (gain decrement : ℕ → ι → ℝ) (S : ℕ) (p : ι → ℝ) :
    (∑ i ∈ coordinates, optimisticHistory κ gain decrement S i * p i) =
      (∑ t ∈ range S, ∑ i ∈ coordinates, (gain t i + decrement t i) * p i) -
        2 * κ * ∑ t ∈ range S, ∑ i ∈ coordinates, decrement t i * p i := by
  simp only [optimisticHistory, sum_mul]
  rw [sum_comm, mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro t ht
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  ring

/-- Lemma `lem:entropy` for a finite compact convex action hull. The
fixed child-block masses enter through the equality of the baseline
inner products; `fixed_block_mass_inner_product` supplies that equality
from the individual block masses. The potential argument uses positivity and the relative-entropy penalty. -/
theorem finite_hull_entropy_regret {ι : Type*} (coordinates : Finset ι)
    (Q : Set (ι → ℝ)) (S : ℕ) (η κ : ℝ)
    (gain decrement baseline innovation predicted : ℕ → ι → ℝ)
    (witness comparator : ι → ℝ)
    (hcompact : IsCompact Q) (hconvex : Convex ℝ Q)
    (hwQ : witness ∈ Q) (hcQ : comparator ∈ Q)
    (hw : ∀ i ∈ coordinates, 0 < witness i)
    (hprob : ∀ p ∈ Q,
      (∀ i ∈ coordinates, 0 ≤ p i) ∧ (∑ i ∈ coordinates, p i = 1))
    (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hpredQ : ∀ t < S, predicted t ∈ Q)
    (hpredMax : ∀ t < S, IsMaxOn
      (entropyValue coordinates η
        (fun i => optimisticHistory κ gain decrement t i + gain t i)) Q (predicted t))
    (hbaseline : ∀ t < S, ∀ i ∈ coordinates, 0 ≤ baseline t i)
    (hdecomposition : ∀ t < S, ∀ i ∈ coordinates,
      decrement t i = baseline t i + innovation t i)
    (hfixedMass : ∀ t < S, ∀ p ∈ Q, ∀ q ∈ Q,
      (∑ i ∈ coordinates, p i * baseline t i) =
        ∑ i ∈ coordinates, q i * baseline t i)
    (hinnovation : ∀ t < S, ∀ i ∈ coordinates, 0 ≤ η * innovation t i)
    (hsmall : ∀ t < S, ∀ i ∈ coordinates, η * innovation t i ≤ κ)
    (hdecrement : ∀ i ∈ coordinates, ∑ t ∈ range S, decrement t i ≤ 1) :
    (∑ t ∈ range S, ∑ i ∈ coordinates, (gain t i + decrement t i) * comparator i) -
        Real.log coordinates.card / η - 2 * κ ≤
      ∑ t ∈ range S, ∑ i ∈ coordinates,
        (gain t i + (1 - κ) * decrement t i) * predicted t i := by
  classical
  have hex : ∀ t : ℕ, ∃ p ∈ Q,
      IsMaxOn (entropyValue coordinates η (optimisticHistory κ gain decrement t)) Q p :=
    fun t => exists_entropy_maximizer coordinates Q η
      (optimisticHistory κ gain decrement t) hcompact ⟨witness, hwQ⟩
  choose leader hleaderQ hleaderMax using hex
  let potential : ℕ → ℝ := fun t => entropyValue coordinates η
    (optimisticHistory κ gain decrement t) (leader t)
  have hpredPositive (t : ℕ) (ht : t < S) : ∀ i ∈ coordinates, 0 < predicted t i :=
    entropy_hull_maximizer_positive coordinates Q η
      (fun i => optimisticHistory κ gain decrement t i + gain t i)
      (predicted t) witness hconvex (hpredQ t ht) hwQ
      (hprob (predicted t) (hpredQ t ht)).1 hw (hpredMax t ht)
  have hincrement (t : ℕ) (ht : t < S) :
      potential (t + 1) - potential t ≤
        η * ∑ i ∈ coordinates, (gain t i + (1 - κ) * decrement t i) * predicted t i := by
    have hstep := entropy_hull_potential_step coordinates Q η κ
      (optimisticHistory κ gain decrement t) (gain t) (decrement t) (baseline t)
      (innovation t) (leader t) (predicted t) (leader (t + 1)) hconvex
      (hpredQ t ht) (hleaderQ (t + 1)) (hpredPositive t ht)
      (hprob (leader (t + 1)) (hleaderQ (t + 1))).1
      (hprob (predicted t) (hpredQ t ht)).2
      (hprob (leader (t + 1)) (hleaderQ (t + 1))).2
      (hleaderMax t) (hpredMax t ht) hη.le hκ hκhalf (hbaseline t ht)
      (hdecomposition t ht)
      (hfixedMass t ht (leader (t + 1)) (hleaderQ (t + 1)) (predicted t) (hpredQ t ht))
      (hinnovation t ht) (hsmall t ht)
    simpa only [potential, optimisticHistory_succ] using hstep
  have hstart : potential 0 ≤ Real.log coordinates.card := by
    have hbound := finite_entropy_le_log_card coordinates (leader 0)
      (hprob (leader 0) (hleaderQ 0)).1 (hprob (leader 0) (hleaderQ 0)).2
    simpa [potential, entropyValue, optimisticHistory] using hbound
  have hcomparator : η *
      ((∑ t ∈ range S, ∑ i ∈ coordinates, (gain t i + decrement t i) * comparator i) -
        2 * κ * ∑ t ∈ range S, ∑ i ∈ coordinates, decrement t i * comparator i) ≤
        potential S := by
    have hmax := hleaderMax S hcQ
    change entropyValue coordinates η (optimisticHistory κ gain decrement S) comparator ≤
      potential S at hmax
    rw [entropyValue_eq, optimisticHistory_inner_product] at hmax
    have hentropy := finite_entropy_nonnegative coordinates comparator
      (hprob comparator hcQ).1 (hprob comparator hcQ).2
    linarith
  have hdecrementSum : (∑ t ∈ range S, ∑ i ∈ coordinates, decrement t i * comparator i) ≤ 1 := by
    calc
      _ = ∑ i ∈ coordinates, (∑ t ∈ range S, decrement t i) * comparator i := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i hi
        rw [sum_mul]
      _ ≤ ∑ i ∈ coordinates, comparator i := sum_le_sum fun i hi => by
        simpa using mul_le_mul_of_nonneg_right (hdecrement i hi) ((hprob comparator hcQ).1 i hi)
      _ = 1 := (hprob comparator hcQ).2
  exact entropy_potential_telescoping S η κ (Real.log coordinates.card) potential
    (fun t => ∑ i ∈ coordinates, (gain t i + (1 - κ) * decrement t i) * predicted t i)
    (fun t => ∑ i ∈ coordinates, (gain t i + decrement t i) * comparator i)
    (fun t => ∑ i ∈ coordinates, decrement t i * comparator i)
    hη hκ hincrement hstart hcomparator hdecrementSum

/-- Replacing a probability vector by an approximation in `ℓ₁` loses
at most that error against any coordinate gain in `[-1, 0]`. -/
theorem bounded_gain_l1_approximation {ι : Type*} (coordinates : Finset ι)
    (gain exactVector approximateVector : ι → ℝ) (error : ℝ)
    (hgain : ∀ i ∈ coordinates, -1 ≤ gain i ∧ gain i ≤ 0)
    (hl1 : ∑ i ∈ coordinates, |approximateVector i - exactVector i| ≤ error) :
    (∑ i ∈ coordinates, gain i * exactVector i) - error ≤
      ∑ i ∈ coordinates, gain i * approximateVector i := by
  have hterm (i : ι) (hi : i ∈ coordinates) :
      gain i * (exactVector i - approximateVector i) ≤
        |approximateVector i - exactVector i| := by
    have habs : |gain i| ≤ 1 := abs_le.mpr ⟨(hgain i hi).1, (hgain i hi).2.trans zero_le_one⟩
    calc
      _ ≤ |gain i * (exactVector i - approximateVector i)| := le_abs_self _
      _ = |gain i| * |exactVector i - approximateVector i| := abs_mul _ _
      _ ≤ 1 * |exactVector i - approximateVector i| :=
        mul_le_mul_of_nonneg_right habs (abs_nonneg _)
      _ = _ := by rw [one_mul, abs_sub_comm]
  have hsum := (sum_le_sum hterm).trans hl1
  simp only [mul_sub, sum_sub_distrib] at hsum
  linarith

/-- The entropy-regret lemma in its fixed-child-block form. Baseline
decrements are constructed as the actual minimum within each child
block; the range hypothesis supplies the small residual required by
the potential proof. -/
theorem finite_block_entropy_regret {ι β : Type*} [Fintype β] [DecidableEq β]
    (coordinates : Finset ι) (block : ι → β)
    (Q : Set (ι → ℝ)) (S : ℕ) (η κ rangeBound : ℝ)
    (gain decrement predicted : ℕ → ι → ℝ) (witness comparator : ι → ℝ)
    (hcompact : IsCompact Q) (hconvex : Convex ℝ Q)
    (hwQ : witness ∈ Q) (hcQ : comparator ∈ Q)
    (hw : ∀ i ∈ coordinates, 0 < witness i)
    (hprob : ∀ p ∈ Q,
      (∀ i ∈ coordinates, 0 ≤ p i) ∧ (∑ i ∈ coordinates, p i = 1))
    (hblocks : ∀ b, (coordinates.filter (fun i => block i = b)).Nonempty)
    (hblockMass : ∀ p ∈ Q, ∀ q ∈ Q, ∀ b,
      (∑ i ∈ coordinates with block i = b, p i) =
        ∑ i ∈ coordinates with block i = b, q i)
    (hη : 0 < η) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hηrange : η * rangeBound ≤ κ)
    (hpredQ : ∀ t < S, predicted t ∈ Q)
    (hpredMax : ∀ t < S, IsMaxOn
      (entropyValue coordinates η
        (fun i => optimisticHistory κ gain decrement t i + gain t i)) Q (predicted t))
    (hdecrementNonneg : ∀ t < S, ∀ i ∈ coordinates, 0 ≤ decrement t i)
    (hrange : ∀ t < S, ∀ i ∈ coordinates, ∀ j ∈ coordinates,
      block i = block j → |decrement t i - decrement t j| ≤ rangeBound)
    (hdecrement : ∀ i ∈ coordinates, ∑ t ∈ range S, decrement t i ≤ 1) :
    (∑ t ∈ range S, ∑ i ∈ coordinates, (gain t i + decrement t i) * comparator i) -
        Real.log coordinates.card / η - 2 * κ ≤
      ∑ t ∈ range S, ∑ i ∈ coordinates,
        (gain t i + (1 - κ) * decrement t i) * predicted t i := by
  classical
  let blockMinimum : ℕ → β → ℝ := fun t b =>
    (coordinates.filter (fun i => block i = b)).inf' (hblocks b) (decrement t)
  let baseline : ℕ → ι → ℝ := fun t i => blockMinimum t (block i)
  let innovation : ℕ → ι → ℝ := fun t i => decrement t i - baseline t i
  have hbaseline (t : ℕ) (ht : t < S) (i : ι) (hi : i ∈ coordinates) :
      0 ≤ baseline t i := by
    apply Finset.le_inf'
    intro j hj
    exact hdecrementNonneg t ht j (mem_filter.mp hj).1
  have hminor (t : ℕ) (i : ι) (hi : i ∈ coordinates) :
      baseline t i ≤ decrement t i := by
    have hiBlock : i ∈ coordinates.filter (fun j => block j = block i) :=
      mem_filter.mpr ⟨hi, rfl⟩
    exact Finset.inf'_le (decrement t) hiBlock
  have hresidual (t : ℕ) (ht : t < S) (i : ι) (hi : i ∈ coordinates) :
      innovation t i ≤ rangeBound := by
    have hlower : decrement t i - rangeBound ≤ baseline t i := by
      apply Finset.le_inf'
      intro j hj
      have hdiff := hrange t ht i hi j (mem_filter.mp hj).1 (mem_filter.mp hj).2.symm
      have := (abs_le.mp hdiff).2
      linarith
    dsimp only [innovation]
    linarith
  apply finite_hull_entropy_regret coordinates Q S η κ gain decrement baseline innovation
    predicted witness comparator hcompact hconvex hwQ hcQ hw hprob hη hκ hκhalf
    hpredQ hpredMax hbaseline
  · intro t ht i hi
    dsimp only [innovation]
    ring
  · intro t ht p hp q hq
    exact fixed_block_mass_inner_product coordinates block p q (blockMinimum t)
      (hblockMass p hp q hq)
  · intro t ht i hi
    exact mul_nonneg hη.le (sub_nonneg.mpr (hminor t i hi))
  · intro t ht i hi
    exact (mul_le_mul_of_nonneg_left (hresidual t ht i hi) hη.le).trans hηrange
  · exact hdecrement

end EditApproximation

end OAI
