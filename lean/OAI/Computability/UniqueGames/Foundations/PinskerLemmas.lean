import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Std
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Model

namespace OAI

section

/-!
A finite Pinsker inequality with a nonoptimal constant, sufficient for the
information bound used by Holenstein: TV(p,q)^2 ≤ D_nat(p || q).
The proof factors the L1 distance through square roots and uses log t ≤ t-1.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

noncomputable def hellingerSquared (p q : α → ℝ) : ℝ :=
  ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2

theorem sqrt_distance_le_relativeEntropy_term {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : x ≠ 0 → y ≠ 0) :
    (Real.sqrt x - Real.sqrt y)^2 ≤ x * Real.log (x / y) - x + y := by
  by_cases hxzero : x = 0
  · subst x
    simp [Real.sq_sqrt hy]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hxzero)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm (hs hxzero))
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hlog := Real.log_le_sub_one_of_pos (div_pos hsy hsx)
  have hlogid : Real.log (Real.sqrt y / Real.sqrt x) =
      -(Real.log (x / y)) / 2 := by
    rw [Real.log_div hsy.ne' hsx.ne', Real.log_sqrt hy, Real.log_sqrt hx,
      Real.log_div hxzero (hs hxzero)]
    ring
  have hprod : x * (Real.sqrt y / Real.sqrt x) = Real.sqrt x * Real.sqrt y := by
    calc
      x * (Real.sqrt y / Real.sqrt x) = (Real.sqrt x)^2 * (Real.sqrt y / Real.sqrt x) := by
        rw [Real.sq_sqrt hx]
      _ = Real.sqrt x * Real.sqrt y := by field_simp [hsx.ne']
  have hm := mul_le_mul_of_nonneg_left hlog hx
  rw [hlogid, mul_sub, mul_one, hprod] at hm
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy]

theorem hellingerSquared_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    hellingerSquared p q ≤ relativeEntropy p q := by
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) =>
    sqrt_distance_le_relativeEntropy_term (hp.1 a) (hq.1 a) (hs a))
  simpa only [hellingerSquared, relativeEntropy, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hp.2, hq.2, sub_add_cancel] using hsum

theorem totalVariation_sq_le_hellingerSquared (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) : totalVariation p q ^ 2 ≤ hellingerSquared p q := by
  have hfactor : ∀ a, |Real.sqrt (p a) - Real.sqrt (q a)| *
      (Real.sqrt (p a) + Real.sqrt (q a)) = |p a - q a| := by
    intro a
    rw [← abs_of_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)),
      ← abs_mul]
    congr 1
    nlinarith [Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => |Real.sqrt (p a) - Real.sqrt (q a)|)
    (fun a => Real.sqrt (p a) + Real.sqrt (q a))
  simp only [hfactor, sq_abs] at hcs
  have hpoint : ∀ a, (Real.sqrt (p a) + Real.sqrt (q a)) ^ 2 ≤ 2 * (p a + q a) := by
    intro a
    nlinarith [sq_nonneg (Real.sqrt (p a) - Real.sqrt (q a)),
      Real.sq_sqrt (hp.1 a), Real.sq_sqrt (hq.1 a)]
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hpoint a)
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, hp.2, hq.2] at hsum
  have hnonneg : 0 ≤ ∑ a, (Real.sqrt (p a) - Real.sqrt (q a)) ^ 2 :=
    Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hsum hnonneg
  dsimp [totalVariation, hellingerSquared]
  nlinarith

theorem totalVariation_sq_le_relativeEntropy (p q : α → ℝ) (hp : IsProbability p)
    (hq : IsProbability q) (hs : SupportedBy p q) :
    totalVariation p q ^ 2 ≤ relativeEntropy p q :=
  (totalVariation_sq_le_hellingerSquared p q hp hq).trans
    (hellingerSquared_le_relativeEntropy p q hp hq hs)

theorem posterior_totalVariation_sq_le_log (p w : α → ℝ) (hp : IsProbability p)
    (hw : ∀ a, 0 ≤ w a) (hw_one : ∀ a, w a ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ a, p a * w a = z) :
    totalVariation (posterior p w z) p ^ 2 ≤ Real.log (1 / z) := by
  exact (totalVariation_sq_le_relativeEntropy _ _ (posterior_isProbability p w hp hw hz hmass)
    hp (posterior_supportedBy p w z)).trans
      (posterior_relativeEntropy_le p w hp hw hw_one hz hmass)

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Tensorization and conditioning for finite independent coordinates. -/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]

noncomputable def coordinateMarginal (p : (ι → α) → ℝ) (i : ι) (a : α) : ℝ := by
  classical
  exact ∑ x, if x i = a then p x else 0

noncomputable def independentProduct (q : ι → α → ℝ) (x : ι → α) : ℝ := ∏ i, q i (x i)

theorem coordinateMarginal_isProbability (p : (ι → α) → ℝ) (hp : IsProbability p) (i : ι) :
    IsProbability (coordinateMarginal p i) := by
  classical
  constructor
  · intro a
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hp.1 x
    · exact le_rfl
  · simp only [coordinateMarginal]
    rw [Finset.sum_comm]
    simpa using hp.2

theorem point_le_coordinateMarginal (p : (ι → α) → ℝ) (hp : IsProbability p)
    (i : ι) (x : ι → α) : p x ≤ coordinateMarginal p i (x i) := by
  classical
  have h := Finset.single_le_sum
    (f := fun y : ι → α => if y i = x i then p y else 0)
    (fun y _ => by split_ifs; exact hp.1 y; exact le_rfl) (Finset.mem_univ x)
  simpa [coordinateMarginal] using h

theorem marginal_expectation (p : (ι → α) → ℝ) (i : ι) (f : α → ℝ) :
    (∑ x, p x * f (x i)) = ∑ a, coordinateMarginal p i a * f a := by
  classical
  simp only [coordinateMarginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

theorem independentProduct_isProbability (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) :
    IsProbability (independentProduct q) := by
  classical
  constructor
  · intro x
    exact Finset.prod_nonneg (fun i _ => (hq i).1 (x i))
  · simp only [independentProduct, ← Fintype.prod_sum, (hq _).2, Finset.prod_const_one]

theorem joint_supportedBy_product_coordinateMarginals (p : (ι → α) → ℝ)
    (hp : IsProbability p) : SupportedBy p (independentProduct (coordinateMarginal p)) := by
  intro x hx
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
    (point_le_coordinateMarginal p hp i x))

theorem relativeEntropy_independent_reference (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (_hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    relativeEntropy p (independentProduct q) =
      relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
  classical
  have hpoint : ∀ x : ι → α, p x * Real.log (p x / independentProduct q x) =
      p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
        ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
    intro x
    by_cases hx : p x = 0
    · simp [hx]
    have hm : ∀ i, coordinateMarginal p i (x i) ≠ 0 := by
      intro i
      exact ne_of_gt ((lt_of_le_of_ne (hp.1 x) (Ne.symm hx)).trans_le
        (point_le_coordinateMarginal p hp i x))
    have hqne : ∀ i, q i (x i) ≠ 0 := fun i => hs i (x i) (hm i)
    have hmp : (∏ i, coordinateMarginal p i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hm i)
    have hqp : (∏ i, q i (x i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => hqne i)
    simp only [independentProduct, Real.log_div hx hmp, Real.log_div hx hqp,
      Real.log_prod (fun i _ => hm i), Real.log_prod (fun i _ => hqne i)]
    simp_rw [Real.log_div (hm _) (hqne _)]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    ring
  calc
    relativeEntropy p (independentProduct q) =
        ∑ x, (p x * Real.log (p x / independentProduct (coordinateMarginal p) x) +
          ∑ i, p x * Real.log (coordinateMarginal p i (x i) / q i (x i))) := by
      exact Finset.sum_congr rfl (fun x _ => hpoint x)
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, ∑ x, p x * Real.log (coordinateMarginal p i (x i) / q i (x i)) := by
      rw [Finset.sum_add_distrib, Finset.sum_comm]
      rfl
    _ = relativeEntropy p (independentProduct (coordinateMarginal p)) +
        ∑ i, relativeEntropy (coordinateMarginal p i) (q i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact marginal_expectation p i (fun a => Real.log (coordinateMarginal p i a / q i a))

theorem coordinate_relativeEntropy_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, relativeEntropy (coordinateMarginal p i) (q i)) ≤
      relativeEntropy p (independentProduct q) := by
  rw [relativeEntropy_independent_reference p q hp hq hs]
  exact le_add_of_nonneg_left (relativeEntropy_nonneg _ _ hp
    (independentProduct_isProbability _ (coordinateMarginal_isProbability p hp))
    (joint_supportedBy_product_coordinateMarginals p hp))

theorem coordinate_totalVariation_sq_sum_le (p : (ι → α) → ℝ) (q : ι → α → ℝ)
    (hp : IsProbability p) (hq : ∀ i, IsProbability (q i))
    (hs : ∀ i, SupportedBy (coordinateMarginal p i) (q i)) :
    (∑ i, totalVariation (coordinateMarginal p i) (q i) ^ 2) ≤
      relativeEntropy p (independentProduct q) := by
  exact (Finset.sum_le_sum (fun i _ => totalVariation_sq_le_relativeEntropy _ _
    (coordinateMarginal_isProbability p hp i) (hq i) (hs i))).trans
      (coordinate_relativeEntropy_sum_le p q hp hq hs)

theorem posterior_coordinate_supportedBy (q : ι → α → ℝ) (w : (ι → α) → ℝ)
    (z : ℝ) (i : ι) :
    SupportedBy (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) := by
  classical
  intro a ha hqa
  apply ha
  unfold coordinateMarginal
  apply Finset.sum_eq_zero
  intro x _
  by_cases hxa : x i = a
  · have hzprod : independentProduct q x = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa only [hxa] using hqa)
    simp [hxa, posterior, hzprod]
  · simp [hxa]

/-- The finite independent-coordinate conditioning inequality underlying
Holenstein Lemma 4.1, with natural logarithms. `w x` is the conditional
probability of the event given the coordinate tuple `x`. -/
theorem posterior_coordinate_totalVariation_sq_sum_le_log
    (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) (w : (ι → α) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw_one : ∀ x, w x ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ x, independentProduct q x * w x = z) :
    (∑ i, totalVariation
      (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) ^ 2) ≤
        Real.log (1 / z) := by
  have hp := independentProduct_isProbability q hq
  exact (coordinate_totalVariation_sq_sum_le _ q
    (posterior_isProbability _ w hp hw hz hmass) hq
    (posterior_coordinate_supportedBy q w z)).trans
      (posterior_relativeEntropy_le _ w hp hw hw_one hz hmass)

/-- The summed-distance form (4.2), with natural logarithms. -/
theorem posterior_coordinate_totalVariation_sum_le_sqrt
    (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) (w : (ι → α) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw_one : ∀ x, w x ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ x, independentProduct q x * w x = z) :
    (∑ i, totalVariation
      (coordinateMarginal (posterior (independentProduct q) w z) i) (q i)) ≤
        Real.sqrt ((Fintype.card ι : ℝ) * Real.log (1 / z)) := by
  let d : ι → ℝ := fun i => totalVariation
    (coordinateMarginal (posterior (independentProduct q) w z) i) (q i)
  have hsq := posterior_coordinate_totalVariation_sq_sum_le_log q hq w hw hw_one hz hmass
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) d (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hln : 0 ≤ Real.log (1 / z) := by
    have hp := independentProduct_isProbability q hq
    exact (relativeEntropy_nonneg _ _ (posterior_isProbability _ w hp hw hz hmass) hp
      (posterior_supportedBy _ w z)).trans
        (posterior_relativeEntropy_le _ w hp hw hw_one hz hmass)
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hsq hcard
  have hsqrt := Real.sq_sqrt (mul_nonneg hcard hln)
  have hsqrtpos := Real.sqrt_nonneg ((Fintype.card ι : ℝ) * Real.log (1 / z))
  change (∑ i, d i) ≤ _
  change (∑ i, d i ^ 2) ≤ _ at hsq
  change (Fintype.card ι : ℝ) * (∑ i, d i ^ 2) ≤ _ at hmul
  nlinarith

/-- The base-two-logarithm normalization of the squared-distance bound. -/
theorem posterior_coordinate_totalVariation_sq_sum_le_binaryLog
    (q : ι → α → ℝ) (hq : ∀ i, IsProbability (q i)) (w : (ι → α) → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw_one : ∀ x, w x ≤ 1) {z : ℝ} (hz : 0 < z)
    (hmass : ∑ x, independentProduct q x * w x = z) :
    (∑ i, totalVariation
      (coordinateMarginal (posterior (independentProduct q) w z) i) (q i) ^ 2) ≤
        Real.log (1 / z) / Real.log 2 := by
  exact le_binaryLog_of_le_log (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (posterior_coordinate_totalVariation_sq_sum_le_log q hq w hw hw_one hz hmass)

end UniqueGamesTheorem.Foundations.Information

end

section

/-! Finite side-information conditioning bound from tensorization and log-sum.
All zero likelihood rows have an explicit normalized fallback. -/
namespace UniqueGamesTheorem.Foundations.Information
open scoped BigOperators

noncomputable def posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ) (z : ℝ) : A → ℝ := by
  classical
  exact if 0 < z then posterior p e z else p

theorem posteriorOrOriginal_isProbability
    {A : Type*} [Fintype A] (p e : A → ℝ)
    (hp : IsProbability p) (he : ∀ a, 0 ≤ e a)
    {z : ℝ} (hmass : ∑ a, p a * e a = z) :
    IsProbability (posteriorOrOriginal p e z) := by
  classical
  by_cases hz : 0 < z
  · simpa only [posteriorOrOriginal, ite_eq_left hz] using
      posterior_isProbability p e hp he hz hmass
  · simpa only [posteriorOrOriginal, ite_eq_right hz] using hp

theorem mass_mul_posteriorOrOriginal
    {A : Type*} [Fintype A] (p e : A → ℝ)
    (hp : IsProbability p) (he : ∀ a, 0 ≤ e a)
    {c : ℝ} (hmass : ∑ a, p a * e a = c) (x : A) :
    c * posteriorOrOriginal p e c x = p x * e x := by
  classical
  by_cases hc : 0 < c
  · simp only [posteriorOrOriginal, ite_eq_left hc, posterior]
    field_simp [hc.ne']
  · have hcnonneg : 0 ≤ c := by
      rw [← hmass]
      exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp.1 a) (he a))
    have hc0 : c = 0 := le_antisymm (le_of_not_gt hc) hcnonneg
    have hpoint := Finset.single_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset A)) => mul_nonneg (hp.1 a) (he a))
      (Finset.mem_univ x)
    rw [hmass, hc0] at hpoint
    have hzero : p x * e x = 0 := le_antisymm hpoint (mul_nonneg (hp.1 x) (he x))
    simp [posteriorOrOriginal, hc0, hzero]

theorem weighted_coordinate_posterior_recombine
    {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A]
    (p e : (I → A) → ℝ) (hp : IsProbability p) (he : ∀ x, 0 ≤ e x)
    {c : ℝ} (hmass : ∑ x, p x * e x = c) (b z : ℝ) (i : I) (a : A) :
    (b * c / z) * coordinateMarginal (posteriorOrOriginal p e c) i a =
      (b / z) * ∑ x, if x i = a then p x * e x else 0 := by
  classical
  simp only [coordinateMarginal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxa : x i = a
  · simp only [ite_eq_left hxa]
    calc
      (b * c / z) * posteriorOrOriginal p e c x =
          (b / z) * (c * posteriorOrOriginal p e c x) := by ring
      _ = (b / z) * (p x * e x) := by
        rw [mass_mul_posteriorOrOriginal p e hp he hmass x]
  · simp [hxa]

variable {J I A : Type*}
variable [Fintype J] [Fintype I] [Fintype A] [DecidableEq I]

theorem side_information_bound
    (w b c : J → ℝ)
    (q : J → I → A → ℝ)
    (e : J → (I → A) → ℝ)
    (hw : IsProbability w)
    (hb : ∀ j, 0 ≤ b j)
    (hq : ∀ j i, IsProbability (q j i))
    (he : ∀ j x, 0 ≤ e j x)
    (he_one : ∀ j x, e j x ≤ 1)
    (hmass : ∀ j, ∑ x, independentProduct (q j) x * e j x = c j)
    {z B : ℝ} (hz : 0 < z) (hB : 0 < B)
    (hbase : ∑ j, b j = B)
    (hweight : ∀ j, w j = b j * c j / z) :
    (∑ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) (c ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) * Real.log (B / z)) := by
  classical
  let d : J → I → ℝ := fun j i => totalVariation
    (coordinateMarginal
      (posteriorOrOriginal (independentProduct (q j)) (e j) (c j)) i)
    (q j i)
  have hbudget : ∀ j,
      w j * (∑ i, d j i ^ 2) ≤ w j * Real.log (1 / c j) := by
    intro j
    by_cases hwzero : w j = 0
    · simp [hwzero]
    have hcne : c j ≠ 0 := by
      intro hczero
      apply hwzero
      rw [hweight j, hczero, mul_zero, zero_div]
    have hcnonneg : 0 ≤ c j := by
      rw [← hmass j]
      exact Finset.sum_nonneg (fun x _ => mul_nonneg
        ((independentProduct_isProbability (q j) (hq j)).1 x) (he j x))
    have hcpos : 0 < c j := lt_of_le_of_ne hcnonneg (Ne.symm hcne)
    have hlocal := posterior_coordinate_totalVariation_sq_sum_le_log
      (q j) (hq j) (e j) (he j) (he_one j) hcpos (hmass j)
    have hweighted := mul_le_mul_of_nonneg_left hlocal (hw.1 j)
    simpa only [d, posteriorOrOriginal, ite_eq_left hcpos] using hweighted
  have hcs := weighted_coordinate_sum_sq_le
    w d (fun j => Real.log (1 / c j)) hw hbudget
  have hlog := posterior_weighted_log_inverse_le w b c hw hb hz hB hbase hweight
  have hsq : (∑ i, ∑ j, w j * d j i)^2 ≤
      (Fintype.card I : ℝ) * Real.log (B / z) :=
    hcs.trans (mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _))
  have htv : ∀ i, totalVariation
      (fun ja : J × A => w ja.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q ja.1))
          (e ja.1) (c ja.1)) i ja.2)
      (fun ja : J × A => w ja.1 * q ja.1 i ja.2) =
      ∑ j, w j * d j i := by
    intro i
    exact totalVariation_joint_common_weights w
      (fun j => coordinateMarginal
        (posteriorOrOriginal (independentProduct (q j)) (e j) (c j)) i)
      (fun j => q j i) hw.1
  simp_rw [htv]
  have hradicand : 0 ≤ (Fintype.card I : ℝ) * Real.log (B / z) :=
    (sq_nonneg _).trans hsq
  have hsqrt := Real.sq_sqrt hradicand
  have hsqrt_nonneg := Real.sqrt_nonneg ((Fintype.card I : ℝ) * Real.log (B / z))
  nlinarith

variable {T V : Type*} [Fintype T] [Fintype V] [Nonempty V]

/-- Finite Corollary 4.3 in natural-log normalization, for actual likelihood
profiles of the event jointly with the finite side label. -/
theorem finite_side_information_bound
    (pT : T → ℝ) (q : T → I → A → ℝ)
    (e : T × V → (I → A) → ℝ) (c w : T × V → ℝ)
    (hpT : IsProbability pT)
    (hq : ∀ t i, IsProbability (q t i))
    (he : ∀ tv x, 0 ≤ e tv x)
    (he_sum : ∀ t x, (∑ v, e (t, v) x) ≤ 1)
    (hc : ∀ tv, ∑ x, independentProduct (q tv.1) x * e tv x = c tv)
    {z : ℝ} (hz : 0 < z)
    (hZ : ∑ tv, pT tv.1 * c tv = z)
    (hweight : ∀ tv, w tv = pT tv.1 * c tv / z) :
    (∑ i, totalVariation
      (fun tva : (T × V) × A => w tva.1 * coordinateMarginal
        (posteriorOrOriginal (independentProduct (q tva.1.1))
          (e tva.1) (c tva.1)) i tva.2)
      (fun tva : (T × V) × A => w tva.1 * q tva.1.1 i tva.2)) ≤
      Real.sqrt ((Fintype.card I : ℝ) *
        (Real.log (Fintype.card V : ℝ) + Real.log (1 / z))) := by
  classical
  have hcnonneg : ∀ tv, 0 ≤ c tv := by
    intro tv
    rw [← hc tv]
    exact Finset.sum_nonneg (fun x _ => mul_nonneg
      ((independentProduct_isProbability (q tv.1) (hq tv.1)).1 x) (he tv x))
  have hw : IsProbability w := by
    constructor
    · intro tv
      rw [hweight tv]
      exact div_nonneg (mul_nonneg (hpT.1 tv.1) (hcnonneg tv)) hz.le
    · simp_rw [hweight, div_eq_mul_inv]
      rw [← Finset.sum_mul, hZ, mul_inv_cancel₀ hz.ne']
  have he_one : ∀ tv x, e tv x ≤ 1 := by
    intro tv x
    have hsingle : e tv x ≤ ∑ v, e (tv.1, v) x :=
      Finset.single_le_sum (fun v _ => he (tv.1, v) x) (Finset.mem_univ tv.2)
    exact hsingle.trans (he_sum tv.1 x)
  have hB : 0 < (Fintype.card V : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hbase : (∑ tv : T × V, pT tv.1) = (Fintype.card V : ℝ) := by
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, ← Finset.mul_sum, hpT.2, mul_one]
  have h := side_information_bound w (fun tv : T × V => pT tv.1) c
    (fun tv => q tv.1) e hw (fun tv => hpT.1 tv.1) (fun tv => hq tv.1)
    he he_one hc hz hB hbase hweight
  have hlog : Real.log ((Fintype.card V : ℝ) / z) =
      Real.log (Fintype.card V : ℝ) + Real.log (1 / z) := by
    rw [Real.log_div hB.ne' hz.ne', Real.log_div one_ne_zero hz.ne', Real.log_one]
    ring
  simpa only [hlog] using h

end UniqueGamesTheorem.Foundations.Information

end

section

namespace UniqueGamesTheorem.Foundations.Target

structure Literal («variables» : Nat) where
  variableIndex : Fin «variables»
  positive : Bool
  deriving DecidableEq

def Literal.eval {n : Nat} (literal : Literal n) (assignment : Fin n → Bool) : Bool :=
  if literal.positive then assignment literal.variableIndex else !(assignment literal.variableIndex)

abbrev Clause («variables» : Nat) := Vector (Literal «variables») 3

def Clause.eval {n : Nat} (clause : Clause n) (assignment : Fin n → Bool) : Bool :=
  (clause[0].eval assignment || clause[1].eval assignment) || clause[2].eval assignment

/-- A finite conjunction of clauses with exactly three literal slots each.
Repeated variables and repeated literals are allowed. -/
structure Formula where
  «variables» : Nat
  clauses : List (Clause «variables»)

def Formula.Satisfiable (formula : Formula) : Prop :=
  ∃ assignment : Fin formula.variables → Bool,
    ∀ clause ∈ formula.clauses, clause.eval assignment = true

/-- Finite forward and inverse tables make totality and invertibility explicit.
An eventual external encoding only needs to serialize the forward table. -/

theorem PermutationTable.images_injective {q : Nat} (table : PermutationTable q)
    {x y : Fin q} (h : table.images[x] = table.images[y]) : x = y := by
  have inverseEquality := congrArg (fun label : Fin q => table.inverseImages[label]) h
  simpa only [table.leftInverse] using inverseEquality

theorem PermutationTable.images_surjective {q : Nat} (table : PermutationTable q)
    (label : Fin q) : ∃ preimage : Fin q, table.images[preimage] = label :=
  ⟨table.inverseImages[label], table.rightInverse label⟩

/-- Constraint occurrences are list entries, so repeated parallel edges retain
their multiplicity. No weights are hidden in this representation. -/

theorem countSatisfied_le_length {n q : Nat} (labeling : Fin n → Fin q)
    (constraints : List (Constraint n q)) :
    countSatisfied labeling constraints ≤ constraints.length := by
  induction constraints with
  | nil => simp [countSatisfied]
  | cons constraint rest ih =>
      simp only [countSatisfied, List.length_cons]
      split <;> omega

theorem Instance.constraintCount_positive {q : Nat} (game : Instance q) :
    0 < game.constraints.length := by
  cases h : game.constraints with
  | nil => exact False.elim (game.nonempty h)
  | cons constraint rest => simp

/-- The rational number `numerator / denominator` lies strictly between 0 and
1/2. No normalization to lowest terms is needed for the gap predicates. -/
structure RationalError where
  numerator : Nat
  denominator : Nat
  numeratorPositive : 0 < numerator
  denominatorPositive : 0 < denominator
  belowHalf : 2 * numerator < denominator

/-- At least one labeling satisfies a fraction at least `1 - error`. -/
def CompleteAt {q : Nat} (error : RationalError) (game : Instance q) : Prop :=
  ∃ labeling : Fin game.vertices → Fin q,
    error.denominator * game.constraints.length ≤
      error.denominator * countSatisfied labeling game.constraints +
      error.numerator * game.constraints.length

/-- Every labeling satisfies a fraction at most `error`. -/
def SoundAt {q : Nat} (error : RationalError) (game : Instance q) : Prop :=
  ∀ labeling : Fin game.vertices → Fin q,
    error.denominator * countSatisfied labeling game.constraints ≤
      error.numerator * game.constraints.length

/-- Only the semantic part of a reduction. This is not a definition of an
efficient reduction or an NP-hardness certificate. -/
structure SemanticGapReduction (completenessError soundnessError : RationalError) where
  alphabet : Nat
  alphabetAtLeastTwo : 2 ≤ alphabet
  reduce : Formula → Instance alphabet
  completeness : ∀ formula : Formula,
    formula.Satisfiable → CompleteAt completenessError (reduce formula)
  soundness : ∀ formula : Formula,
    ¬ formula.Satisfiable → SoundAt soundnessError (reduce formula)

end UniqueGamesTheorem.Foundations.Target

end

end OAI
