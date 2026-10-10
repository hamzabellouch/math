import OAI.Analysis.PlaneSpectrum.PhaseEncoding

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate

open scoped BigOperators
namespace EuclideanFiveColor.PhaseCollision

section

variable {ι κ V : Type*} [Fintype ι] [Fintype κ]
local instance : DecidableEq ι := Classical.decEq ι
local instance : DecidableEq κ := Classical.decEq κ

/-- Ordered distinct pairs in one assigned bin. -/
def repeatedPairs (s : Finset ι) (f : ι → κ) : Finset (ι × ι) := by
  classical
  exact (s ×ˢ s).filter (fun p => p.1 ≠ p.2 ∧ f p.1 = f p.2)

omit [Fintype ι] in
lemma sameBin_card (s : Finset ι) (f : ι → κ) :
    ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card =
      ∑ b : κ, (s.filter (fun i => f i = b)).card ^ 2 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : ι × ι => f p.1)
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro b _
  have he : (((s ×ˢ s).filter (fun p => f p.1 = f p.2)).filter
      (fun p => f p.1 = b)) =
      (s.filter (fun i => f i = b)) ×ˢ (s.filter (fun i => f i = b)) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product]
    aesop
  rw [he, Finset.card_product, pow_two]

omit [Fintype ι] [Fintype κ] in
lemma sameBin_card_eq (s : Finset ι) (f : ι → κ) :
    ((s ×ˢ s).filter (fun p => f p.1 = f p.2)).card =
      (repeatedPairs s f).card + s.card := by
  classical
  let T := (s ×ˢ s).filter (fun p => f p.1 = f p.2)
  have hsplit := Finset.card_filter_add_card_filter_not (s := T)
    (p := fun p => p.1 ≠ p.2)
  have hfirst : T.filter (fun p => p.1 ≠ p.2) = repeatedPairs s f := by
    ext p
    simp only [T, repeatedPairs, Finset.mem_filter, Finset.mem_product]
    tauto
  have hsecond : T.filter (fun p => ¬p.1 ≠ p.2) = s.diag := by
    ext p
    simp only [T, Finset.mem_filter, Finset.mem_product, not_not, Finset.mem_diag]
    aesop
  rw [hfirst, hsecond, Finset.diag_card] at hsplit
  exact hsplit.symm

/- Sum of squares, with diagonal pairs removed. -/
omit [Fintype ι] in
theorem repeated_bin_lower_bound (s : Finset ι) (f : ι → κ) :
    (s.card : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) *
      ((repeatedPairs s f).card + (s.card : ℝ)) := by
  classical
  have hs : ∑ b : κ, (s.filter (fun i => f i = b)).card = s.card := by
    symm
    exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  have hs' : ∑ b : κ, ((s.filter (fun i => f i = b)).card : ℝ) = s.card := by
    exact_mod_cast hs
  have hpair : ∑ b : κ, ((s.filter (fun i => f i = b)).card : ℝ) ^ 2 =
      (repeatedPairs s f).card + (s.card : ℝ) := by
    exact_mod_cast (sameBin_card s f).symm.trans (sameBin_card_eq s f)
  simpa only [hs', hpair, Finset.card_univ] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun b : κ => ((s.filter (fun i => f i = b)).card : ℝ)))

variable [PseudoMetricSpace V]

/-- Ordered distinct phase pairs within a fixed distance. -/
def closePairs (v : ι → V) (r : ℝ) : Finset (ι × ι) := by
  classical
  exact Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ dist (v p.1) (v p.2) ≤ r)

theorem close_pair_lower_bound (s : Finset ι) (f : ι → κ)
    (v : ι → V) (w : κ → V) (r : ℝ)
    (h : ∀ i ∈ s, dist (v i) (w (f i)) ≤ r) :
    (s.card : ℝ) ^ 2 ≤ (Fintype.card κ : ℝ) *
      ((closePairs v (2 * r)).card + (Fintype.card ι : ℝ)) := by
  classical
  have hsub : repeatedPairs s f ⊆ closePairs v (2 * r) := by
    intro p hp
    simp only [repeatedPairs, Finset.mem_filter, Finset.mem_product] at hp
    simp only [closePairs, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hp.2.1, ?_⟩
    calc
      dist (v p.1) (v p.2) ≤ dist (v p.1) (w (f p.1)) +
          dist (w (f p.1)) (v p.2) := dist_triangle _ _ _
      _ ≤ r + r := by
        apply add_le_add (h p.1 hp.1.1)
        rw [hp.2.2, dist_comm]
        exact h p.2 hp.1.2
      _ = 2 * r := by ring
  calc
    _ ≤ (Fintype.card κ : ℝ) * ((repeatedPairs s f).card + (s.card : ℝ)) :=
      repeated_bin_lower_bound s f
    _ ≤ _ := by
      exact mul_le_mul_of_nonneg_left (add_le_add
        (Nat.cast_le.mpr (Finset.card_le_card hsub))
        (Nat.cast_le.mpr (Finset.card_le_univ s))) (Nat.cast_nonneg _)

/-- The normalized source estimate `q² / #bins - 1/#indices`. -/
theorem normalized_close_pair_lower_bound [Nonempty ι] [Nonempty κ]
    (s : Finset ι) (f : ι → κ) (v : ι → V) (w : κ → V) (r : ℝ)
    (h : ∀ i ∈ s, dist (v i) (w (f i)) ≤ r) :
    ((s.card : ℝ) / Fintype.card ι) ^ 2 / Fintype.card κ - 1 / Fintype.card ι ≤
      (closePairs v (2 * r)).card / (Fintype.card ι : ℝ) ^ 2 := by
  have hn : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hm : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.mpr Fintype.card_pos
  have hc := close_pair_lower_bound s f v w r h
  apply (le_div_iff₀ (sq_pos_of_pos hn)).mpr
  field_simp
  nlinarith

end

open MeasureTheory
open scoped BigOperators

variable {Ω ι κ V : Type*} [MeasurableSpace Ω]
variable [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] [PseudoMetricSpace V]

/-- Larger than 95 percent average phase coverage forces a colliding pair.
The bins and assignments may depend on the sampled point; no measurable
choice of assignments is required. -/
theorem average_cover_forces_collision (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Ω → Finset ι) (f : Ω → ι → κ) (v : Ω → ι → V) (w : Ω → κ → V)
    (r : ℝ)
    (hcov : ∀ᵐ x ∂μ, ∀ i ∈ s x, dist (v x i) (w x (f x i)) ≤ r)
    (hm : ∀ i j, Measurable (fun x => dist (v x i) (v x j)))
    (hq : Measurable (fun x => ((s x).card : ℝ) / Fintype.card ι))
    (hlarge : 10 * Fintype.card κ < Fintype.card ι)
    (havg : (19/20 : ℝ) < ∫ x, ((s x).card : ℝ) / Fintype.card ι ∂μ) :
    ∃ i j : ι, i ≠ j ∧
      1 / (4 * (Fintype.card κ : ℝ)) ≤ μ.real {x | dist (v x i) (v x j) ≤ 2*r} := by
  classical
  let n : ℝ := Fintype.card ι
  let k : ℝ := Fintype.card κ
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hk : 0 < k := Nat.cast_pos.mpr Fintype.card_pos
  have hlarge' : 10*k < n := by dsimp [k, n]; exact_mod_cast hlarge
  let q : Ω → ℝ := fun x => (s x).card / n
  have hq0 (x) : 0 ≤ q x := div_nonneg (Nat.cast_nonneg _) hn.le
  have hq1 (x) : q x ≤ 1 := by
    apply (div_le_one hn).mpr
    dsimp [n]
    exact_mod_cast Finset.card_le_univ (s x)
  have hiq : Integrable q μ := Integrable.of_bound hq.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_of_nonneg (hq0 x)]; exact hq1 x))
  have hiq2 : Integrable (fun x => (q x)^2) μ := Integrable.of_bound
    (hq.pow_const 2).aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (hq0 x) (hq1 x)))
  have hsq : (19/20 : ℝ)^2 < ∫ x, (q x)^2 ∂μ := by
    have hv : 0 ≤ ∫ x, (q x-19/20)^2 ∂μ :=
      integral_nonneg (fun x => sq_nonneg (q x - 19/20))
    have he : (fun x => (q x-19/20)^2) =
        (fun x => (q x)^2 - (19/10)*q x + (19/20)^2) := by funext x; ring
    have hsub : Integrable (fun x => (q x)^2 - (19/10)*q x) μ :=
      hiq2.sub (hiq.const_mul (19/10))
    rw [he, integral_add hsub (integrable_const ((19/20 : ℝ)^2)),
      integral_sub hiq2 (hiq.const_mul (19/10)), integral_const_mul] at hv
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul] at hv
    change 19/20 < ∫ x, q x ∂μ at havg
    linarith
  let a : (ι × ι) → Ω → ℝ := fun p x =>
    if p.1 ≠ p.2 ∧ dist (v x p.1) (v x p.2) ≤ 2*r then 1 else 0
  have hma (p : ι × ι) : Measurable (a p) := by
    have hset : MeasurableSet {x | p.1 ≠ p.2 ∧ dist (v x p.1) (v x p.2) ≤ 2*r} := by
      by_cases h : p.1 = p.2
      · simp [h]
      · simpa [h] using
          (measurableSet_le (hm p.1 p.2) (measurable_const (a := 2*r)))
    exact measurable_const.ite hset measurable_const
  have hia (p : ι × ι) : Integrable (a p) μ := Integrable.of_bound
    (hma p).aestronglyMeasurable 1 (Filter.Eventually.of_forall (fun x => by
      dsimp [a]; split_ifs <;> norm_num))
  have hcnt (x : Ω) : ((closePairs (v x) (2*r)).card : ℝ) = ∑ p, a p x := by
    simp only [closePairs, a, Finset.cast_card, Finset.sum_filter]
  have hic : Integrable (fun x => ((closePairs (v x) (2*r)).card : ℝ)/n^2) μ := by
    simp_rw [hcnt]
    exact (integrable_finsetSum _ (fun p _ => hia p)).div_const _
  have hlow := integral_mono_ae (μ := μ) ((hiq2.div_const k).sub (integrable_const (1/n))) hic
    (hcov.mono (fun x hx =>
      normalized_close_pair_lower_bound (s x) (f x) (v x) (w x) r hx))
  simp only [Pi.sub_apply] at hlow
  rw [integral_sub (hiq2.div_const k) (integrable_const (1/n)), integral_div,
    integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hlow
  have hstrict : 1/(4*k) < (∫ x, (q x)^2 ∂μ)/k - 1/n := by
    have hi : 1/n < 1/(10*k) := one_div_lt_one_div_of_lt (by positivity) hlarge'
    have hsq' := (div_lt_div_iff_of_pos_right hk).mpr hsq
    apply lt_of_lt_of_le _ (le_of_lt (sub_lt_sub hsq' hi))
    field_simp
    norm_num
  by_contra hh
  push Not at hh
  have hailt (p : ι × ι) : ∫ x, a p x ∂μ < 1/(4*k) := by
    by_cases hp : p.1 = p.2
    · simp only [a, hp, ne_eq, not_true_eq_false, false_and, ↓reduceIte, integral_zero]
      positivity
    · have he : a p = Set.indicator {x | dist (v x p.1) (v x p.2) ≤ 2*r}
          (fun _ => (1 : ℝ)) := by
        funext x
        simp [a, hp, Set.indicator_apply]
      rw [he, integral_indicator (measurableSet_le (hm p.1 p.2) measurable_const)]
      simpa only [setIntegral_const, Measure.real, smul_eq_mul, mul_one] using hh p.1 p.2 hp
  have hiupper : (∫ x, ((closePairs (v x) (2*r)).card : ℝ)/n^2 ∂μ) < 1/(4*k) := by
    simp_rw [hcnt]
    rw [integral_div, integral_finsetSum _ (fun p _ => hia p)]
    have hsum := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (ι × ι)))
      Finset.univ_nonempty (fun p _ => hailt p)
    have hnum : (∑ _p : ι × ι, 1/(4*k)) = n^2/(4*k) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
        Nat.cast_mul, n, pow_two, mul_div_assoc]
      ring
    rw [hnum] at hsum
    apply (div_lt_iff₀ (sq_pos_of_pos hn)).mpr
    convert hsum using 1
    ring
  exact (not_lt_of_ge (hstrict.le.trans hlow)) hiupper

end EuclideanFiveColor.PhaseCollision

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial

open MeasureTheory
open scoped BigOperators
namespace EuclideanFiveColor.AverageErrors
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

/-- The fraction of indices whose nonnegative error is below a threshold. -/
def goodFraction (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) : ℝ := by
  classical
  exact ((Finset.univ.filter (fun i => e i x < t)).card : ℝ) / Fintype.card ι

omit [MeasurableSpace Ω] [Nonempty ι] in
lemma goodFraction_eq_sum (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) :
    goodFraction e t x = (∑ i, if e i x < t then (1 : ℝ) else 0) / Fintype.card ι := by
  classical
  simp only [goodFraction, Finset.cast_card, Finset.sum_filter]

omit [Nonempty ι] in
lemma measurable_goodFraction (e : ι → Ω → ℝ) (t : ℝ)
    (he : ∀ i, Measurable (e i)) : Measurable (goodFraction e t) := by
  classical
  change Measurable (fun x => goodFraction e t x)
  simp_rw [goodFraction_eq_sum]
  exact (Finset.measurable_sum _ (fun i _ => measurable_const.ite
    (measurableSet_lt (he i) measurable_const) measurable_const)).div_const _

omit [MeasurableSpace Ω] [Nonempty ι] in
lemma goodFraction_nonneg (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) :
    0 ≤ goodFraction e t x := by unfold goodFraction; positivity

omit [MeasurableSpace Ω] in
lemma goodFraction_le_one (e : ι → Ω → ℝ) (t : ℝ) (x : Ω) :
    goodFraction e t x ≤ 1 := by
  classical
  apply (div_le_one (Nat.cast_pos.mpr Fintype.card_pos)).mpr
  exact_mod_cast Finset.card_le_univ (Finset.univ.filter (fun i => e i x < t))

lemma integrable_goodFraction (μ : Measure Ω) [IsFiniteMeasure μ]
    (e : ι → Ω → ℝ) (t : ℝ) (he : ∀ i, Measurable (e i)) :
    Integrable (goodFraction e t) μ :=
  Integrable.of_bound (measurable_goodFraction e t he).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (goodFraction_nonneg e t x)]
      exact goodFraction_le_one e t x)

/-- Less than 5% average error gives more than 95% good indices on average. -/
theorem average_goodFraction (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : ι → Ω → ℝ) (t : ℝ) (ht : 0 < t)
    (he : ∀ i, Measurable (e i)) (hi : ∀ i, Integrable (e i) μ)
    (hn : ∀ᵐ x ∂μ, ∀ i, 0 ≤ e i x)
    (havg : ∀ i, ∫ x, e i x ∂μ < t/20) :
    (19/20 : ℝ) < ∫ x, goodFraction e t x ∂μ := by
  classical
  let n : ℝ := Fintype.card ι
  have hnpos : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hpoint : ∀ᵐ x ∂μ,
      1 - (∑ i, e i x) / (n*t) ≤ goodFraction e t x := by
    filter_upwards [hn] with x hx
    have hi' (i) : 1 - e i x / t ≤ if e i x < t then (1 : ℝ) else 0 := by
      split_ifs with h
      · have : 0 ≤ e i x / t := div_nonneg (hx i) ht.le
        linarith
      · have : 1 ≤ e i x / t := (le_div_iff₀ ht).mpr (by simpa using le_of_not_gt h)
        linarith
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi' i)
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ← Finset.sum_div] at hs
    rw [goodFraction_eq_sum]
    apply (le_div_iff₀ hnpos).mpr
    have heq : (1 - (∑ i, e i x)/(n*t))*n = n - (∑ i, e i x)/t := by
      field_simp
    rw [heq]
    exact hs
  have hil : Integrable (fun x => 1 - (∑ i, e i x)/(n*t)) μ :=
    (integrable_const 1).sub ((integrable_finsetSum _ (fun i _ => hi i)).div_const _)
  have hlow := integral_mono_ae hil (integrable_goodFraction μ e t he) hpoint
  rw [integral_sub (integrable_const 1) ((integrable_finsetSum _ (fun i _ => hi i)).div_const _),
    integral_div, integral_finsetSum _ (fun i _ => hi i)] at hlow
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hlow
  have hu := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset ι))
    Finset.univ_nonempty (fun i _ => havg i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hu
  have hr : (∑ i, ∫ x, e i x ∂μ) / (n*t) < 1/20 := by
    apply (div_lt_iff₀ (mul_pos hnpos ht)).mpr
    convert hu using 1
    dsimp [n]
    ring
  linarith

end EuclideanFiveColor.AverageErrors

namespace EuclideanFiveColor.PhaseCollision
open MeasureTheory
open scoped BigOperators

variable {Ω ι κ V : Type*} [MeasurableSpace Ω]
variable [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ] [PseudoMetricSpace V]

/-- The assignment itself need not be measurable and may be chosen separately
at every sample. Only the phase distances and fraction are measured. -/
theorem average_exists_cover_forces_collision (μ : Measure Ω) [IsProbabilityMeasure μ]
    (s : Ω → Finset ι) (v : Ω → ι → V) (w : Ω → κ → V) (r : ℝ)
    (hcov : ∀ᵐ x ∂μ, ∀ i ∈ s x, ∃ j, dist (v x i) (w x j) ≤ r)
    (hm : ∀ i j, Measurable (fun x => dist (v x i) (v x j)))
    (hq : Measurable (fun x => ((s x).card : ℝ) / Fintype.card ι))
    (hlarge : 10 * Fintype.card κ < Fintype.card ι)
    (havg : (19/20 : ℝ) < ∫ x, ((s x).card : ℝ) / Fintype.card ι ∂μ) :
    ∃ i j : ι, i ≠ j ∧
      1 / (4 * (Fintype.card κ : ℝ)) ≤ μ.real {x | dist (v x i) (v x j) ≤ 2*r} := by
  classical
  let f : Ω → ι → κ := fun x i =>
    if h : ∃ j, dist (v x i) (w x j) ≤ r then h.choose else Classical.choice inferInstance
  apply average_cover_forces_collision μ s f v w r _ hm hq hlarge havg
  filter_upwards [hcov] with x hx
  intro i hi
  dsimp [f]
  rw [dite_eq_left (hx i hi)]
  exact (hx i hi).choose_spec

omit [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
  [PseudoMetricSpace V] in
lemma circle_product_dist (a b c d : Circle) :
    dist ((a : ℂ)*(b : ℂ)) ((c : ℂ)*(d : ℂ)) ≤
      dist (a : ℂ) (c : ℂ) + dist (b : ℂ) (d : ℂ) := by
  simp only [dist_eq_norm]
  have he : (a : ℂ)*(b : ℂ)-(c : ℂ)*(d : ℂ) =
      ((a : ℂ)-(c : ℂ))*(b : ℂ) + (c : ℂ)*((b : ℂ)-(d : ℂ)) := by ring
  rw [he]
  simpa only [norm_mul, Circle.norm_coe, mul_one, one_mul] using
    norm_add_le (((a : ℂ)-(c : ℂ))*(b : ℂ)) ((c : ℂ)*((b : ℂ)-(d : ℂ)))

end EuclideanFiveColor.PhaseCollision

namespace EuclideanFiveColor.EncodedCollision
local instance : MeasurableSpace Circle := borel Circle
local instance : BorelSpace Circle := ⟨rfl⟩
open MeasureTheory
open scoped BigOperators
open PhaseEncoding AverageErrors PhaseCollision
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]

/-- This is the source's collision contradiction on one selected predecessor
fiber. The lists need not be measurably enumerated. Measurability is required
only of their symmetric encodings and the actual sampled phases. -/
theorem collision_from_close_encodings (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (zp zm : Ω → ι → Fin m → Circle) (ap am : ι → Ω → Circle) (j₀ : ι)
    (hap : ∀ j, Measurable (ap j)) (ham : ∀ j, Measurable (am j))
    (hDp : ∀ j, Measurable (fun x => dist (encoding (zp x j)) (encoding (zp x j₀))))
    (hDm : ∀ j, Measurable (fun x => dist (encoding (zm x j)) (encoding (zm x j₀))))
    (hmem : ∀ᵐ x ∂μ, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r))
    (hi : ∀ j, Integrable (fun x =>
       dist (encoding (zp x j)) (encoding (zp x j₀))^2 +
       dist (encoding (zm x j)) (encoding (zm x j₀))^2) μ)
    (he : ∀ j, (∫ x,
       dist (encoding (zp x j)) (encoding (zp x j₀))^2 +
       dist (encoding (zm x j)) (encoding (zm x j₀))^2 ∂μ) <
       (ρ^m / m)^2 / 20)
    (hlarge : 10 * m^2 < Fintype.card ι) :
    ∃ i j : ι, i ≠ j ∧ 1/(4*(m : ℝ)^2) ≤ μ.real {x |
      dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ} := by
  classical
  let δ : ℝ := ρ^m / m
  have hδ : 0 < δ := div_pos (pow_pos hρ _) (Nat.cast_pos.mpr hm)
  let e : ι → Ω → ℝ := fun j x =>
    dist (encoding (zp x j)) (encoding (zp x j₀))^2 +
    dist (encoding (zm x j)) (encoding (zm x j₀))^2
  have hem (i) : Measurable (e i) :=
    (hDp i |>.pow_const 2).add (hDm i |>.pow_const 2)
  have hen (x) (i) : 0 ≤ e i x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have havg := average_goodFraction μ e (δ^2) (sq_pos_of_pos hδ) hem hi
    (Filter.Eventually.of_forall hen) he
  let s : Ω → Finset ι := fun x => Finset.univ.filter (fun i => e i x < δ^2)
  let v : Ω → ι → ℂ := fun x i => (ap i x : ℂ)*(am i x : ℂ)
  let w : Ω → (Fin m × Fin m) → ℂ := fun x p =>
    (zp x j₀ p.1 : ℂ)*(zm x j₀ p.2 : ℂ)
  have hcover : ∀ᵐ x ∂μ, ∀ i ∈ s x, ∃ p, dist (v x i) (w x p) ≤ 2*ρ := by
    filter_upwards [hmem] with x hx
    intro i hi'
    have hie : e i x < δ^2 := (Finset.mem_filter.mp hi').2
    have hp : dist (encoding (zp x i)) (encoding (zp x j₀)) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (encoding (zm x i)) (encoding (zm x j₀))), dist_nonneg
        (x := encoding (zp x i)) (y := encoding (zp x j₀))]
    have hm' : dist (encoding (zm x i)) (encoding (zm x j₀)) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (encoding (zp x i)) (encoding (zp x j₀))), dist_nonneg
        (x := encoding (zm x i)) (y := encoding (zm x j₀))]
    obtain ⟨⟨rp, hrp⟩, ⟨rm, hrm⟩⟩ := hx i
    obtain ⟨cp, hcp⟩ := close_encoding_each_phase hm (zp x i) (zp x j₀) hρ hp rp
    obtain ⟨cm, hcm⟩ := close_encoding_each_phase hm (zm x i) (zm x j₀) hρ hm' rm
    refine ⟨(cp, cm), ?_⟩
    dsimp [v, w]
    rw [hrp, hrm]
    exact (circle_product_dist _ _ _ _).trans (by linarith)
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hv' (i j) : Measurable (fun x => dist (v x i) (v x j)) := by
    have hco : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
    have hvm (i) : Measurable (fun x => v x i) :=
      (hco.measurable.comp (hap i)).mul (hco.measurable.comp (ham i))
    exact (hvm i).dist (hvm j)
  obtain ⟨i, j, hij, hc⟩ := average_exists_cover_forces_collision μ s v w (2*ρ)
    hcover hv' (measurable_goodFraction e (δ^2) hem)
    (by simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hlarge) havg
  refine ⟨i, j, hij, ?_⟩
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two,
    v, show 2*(2*ρ)=4*ρ by ring] using hc

/-- This is the source's collision contradiction on one selected predecessor
fiber. The lists need not be measurably enumerated. Measurability is required
only of their symmetric encodings and the actual sampled phases. -/
theorem collision_from_measurable_encodings (μ : Measure Ω) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ : 0 < ρ)
    (zp zm : Ω → ι → Fin m → Circle) (ap am : ι → Ω → Circle) (j₀ : ι)
    (Hp Hm : ι → Ω → Fin m → ℂ)
    (henc : ∀ᵐ x ∂μ, ∀ j, encoding (zp x j) = Hp j x ∧ encoding (zm x j) = Hm j x)
    (hap : ∀ j, Measurable (ap j)) (ham : ∀ j, Measurable (am j))
    (hDp : ∀ j, Measurable (fun x => dist (Hp j x) (Hp j₀ x)))
    (hDm : ∀ j, Measurable (fun x => dist (Hm j x) (Hm j₀ x)))
    (hmem : ∀ᵐ x ∂μ, ∀ j, (∃ r, ap j x = zp x j r) ∧ (∃ r, am j x = zm x j r))
    (hi : ∀ j, Integrable (fun x =>
       dist (Hp j x) (Hp j₀ x)^2 +
       dist (Hm j x) (Hm j₀ x)^2) μ)
    (he : ∀ j, (∫ x,
       dist (Hp j x) (Hp j₀ x)^2 +
       dist (Hm j x) (Hm j₀ x)^2 ∂μ) <
       (ρ^m / m)^2 / 20)
    (hlarge : 10 * m^2 < Fintype.card ι) :
    ∃ i j : ι, i ≠ j ∧ 1/(4*(m : ℝ)^2) ≤ μ.real {x |
      dist ((ap i x : ℂ)*(am i x : ℂ)) ((ap j x : ℂ)*(am j x : ℂ)) ≤ 4*ρ} := by
  classical
  let δ : ℝ := ρ^m / m
  have hδ : 0 < δ := div_pos (pow_pos hρ _) (Nat.cast_pos.mpr hm)
  let e : ι → Ω → ℝ := fun j x =>
    dist (Hp j x) (Hp j₀ x)^2 +
    dist (Hm j x) (Hm j₀ x)^2
  have hem (i) : Measurable (e i) :=
    (hDp i |>.pow_const 2).add (hDm i |>.pow_const 2)
  have hen (x) (i) : 0 ≤ e i x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have havg := average_goodFraction μ e (δ^2) (sq_pos_of_pos hδ) hem hi
    (Filter.Eventually.of_forall hen) he
  let s : Ω → Finset ι := fun x => Finset.univ.filter (fun i => e i x < δ^2)
  let v : Ω → ι → ℂ := fun x i => (ap i x : ℂ)*(am i x : ℂ)
  let w : Ω → (Fin m × Fin m) → ℂ := fun x p =>
    (zp x j₀ p.1 : ℂ)*(zm x j₀ p.2 : ℂ)
  have hcover : ∀ᵐ x ∂μ, ∀ i ∈ s x, ∃ p, dist (v x i) (w x p) ≤ 2*ρ := by
    filter_upwards [hmem, henc] with x hx hxe
    intro i hi'
    have hie : e i x < δ^2 := (Finset.mem_filter.mp hi').2
    have hp : dist (Hp i x) (Hp j₀ x) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (Hm i x) (Hm j₀ x)), dist_nonneg
        (x := Hp i x) (y := Hp j₀ x)]
    have hm' : dist (Hm i x) (Hm j₀ x) < δ := by
      dsimp [e] at hie
      nlinarith [sq_nonneg (dist (Hp i x) (Hp j₀ x)), dist_nonneg
        (x := Hm i x) (y := Hm j₀ x)]
    have hp' : dist (encoding (zp x i)) (encoding (zp x j₀)) < δ := by
      rw [(hxe i).1, (hxe j₀).1]; exact hp
    have hm'' : dist (encoding (zm x i)) (encoding (zm x j₀)) < δ := by
      rw [(hxe i).2, (hxe j₀).2]; exact hm'
    obtain ⟨⟨rp, hrp⟩, ⟨rm, hrm⟩⟩ := hx i
    obtain ⟨cp, hcp⟩ := close_encoding_each_phase hm (zp x i) (zp x j₀) hρ hp' rp
    obtain ⟨cm, hcm⟩ := close_encoding_each_phase hm (zm x i) (zm x j₀) hρ hm'' rm
    refine ⟨(cp, cm), ?_⟩
    dsimp [v, w]
    rw [hrp, hrm]
    exact (circle_product_dist _ _ _ _).trans (by linarith)
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hv' (i j) : Measurable (fun x => dist (v x i) (v x j)) := by
    have hco : Continuous (fun z : Circle => (z : ℂ)) := continuous_subtype_val
    have hvm (i) : Measurable (fun x => v x i) :=
      (hco.measurable.comp (hap i)).mul (hco.measurable.comp (ham i))
    exact (hvm i).dist (hvm j)
  obtain ⟨i, j, hij, hc⟩ := average_exists_cover_forces_collision μ s v w (2*ρ)
    hcover hv' (measurable_goodFraction e (δ^2) hem)
    (by simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using hlarge) havg
  refine ⟨i, j, hij, ?_⟩
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two,
    v, show 2*(2*ρ)=4*ρ by ring] using hc

end EuclideanFiveColor.EncodedCollision

end

end OAI
