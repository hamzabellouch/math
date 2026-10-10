import OAI.Analysis.OInfinity.ClockedBands

namespace OAI

/-! # Finite clock corrections and their multiplication defects

Clock powers remove the finite homogeneous degrees. They are not treated
as central: every multiplication defect is an explicit commutator. Terms
of degree divisible by the clock period are preserved exactly. The final
formula applies this correction to the actual three-term cancellation
path and preserves both endpoint values.
-/

noncomputable section
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

/-- Left correction of an integer homogeneous degree by a unitary clock. -/
def clockDegreeCorrection (k : unitary E) (d : ℤ) (x : E) : E :=
  ((k ^ (-d) : unitary E) : E) * x

lemma clockDegreeCorrection_norm (k : unitary E) (d : ℤ) (x : E) :
    ‖clockDegreeCorrection k d x‖ = ‖x‖ :=
  CStarRing.norm_coe_unitary_mul _ _

lemma clockDegreeCorrection_zero (k : unitary E) (x : E) :
    clockDegreeCorrection k 0 x = x := by
  simp only [clockDegreeCorrection, neg_zero, zpow_zero, Submonoid.coe_one, one_mul]

lemma clockDegreeCorrection_period (k : unitary E) (N : ℕ)
    (hN : k ^ N = 1) (d : ℤ) (x : E) :
    clockDegreeCorrection k ((N : ℤ) * d) x = x := by
  have hpow : k ^ (-((N : ℤ) * d)) = 1 := by
    rw [show -((N : ℤ) * d) = (N : ℤ) * (-d) by ring, zpow_mul,
      zpow_natCast, hN, one_zpow]
  rw [clockDegreeCorrection, hpow, Submonoid.coe_one, one_mul]

/-- No centrality is suppressed in this identity. -/
lemma clockDegreeCorrection_mul_defect (k : unitary E) (d e : ℤ) (x y : E) :
    clockDegreeCorrection k d x * clockDegreeCorrection k e y -
      clockDegreeCorrection k (d + e) (x * y) =
        ((k ^ (-d) : unitary E) : E) *
          (x * ((k ^ (-e) : unitary E) : E) - ((k ^ (-e) : unitary E) : E) * x) * y := by
  have hpow : ((k ^ (-(d + e)) : unitary E) : E) =
      ((k ^ (-d) : unitary E) : E) * ((k ^ (-e) : unitary E) : E) := by
    simp only [neg_add, zpow_add, Submonoid.coe_mul]
  unfold clockDegreeCorrection
  rw [hpow]
  noncomm_ring

lemma clockDegreeCorrection_mul_error (k : unitary E) (d e : ℤ) (x y : E) :
    ‖clockDegreeCorrection k d x * clockDegreeCorrection k e y -
      clockDegreeCorrection k (d + e) (x * y)‖ ≤
        ‖x * ((k ^ (-e) : unitary E) : E) - ((k ^ (-e) : unitary E) : E) * x‖ * ‖y‖ := by
  rw [clockDegreeCorrection_mul_defect]
  exact (norm_mul_le _ _).trans_eq (by rw [CStarRing.norm_coe_unitary_mul])

lemma clockDegreeCorrection_mul_of_commute (k : unitary E) (d e : ℤ) (x y : E)
    (hc : Commute x ((k ^ (-e) : unitary E) : E)) :
    clockDegreeCorrection k d x * clockDegreeCorrection k e y =
      clockDegreeCorrection k (d + e) (x * y) := by
  apply sub_eq_zero.mp
  rw [clockDegreeCorrection_mul_defect, hc.eq, sub_self, mul_zero, zero_mul]

lemma clockDegreeCorrection_star_defect (k : unitary E) (d : ℤ) (x : E) :
    star (clockDegreeCorrection k d x) - clockDegreeCorrection k (-d) (star x) =
      star x * ((k ^ d : unitary E) : E) - ((k ^ d : unitary E) : E) * star x := by
  have hs : star (((k ^ (-d) : unitary E) : E)) = ((k ^ d : unitary E) : E) := by
    change ((star (k ^ (-d)) : unitary E) : E) = _
    rw [Unitary.star_eq_inv, ← zpow_neg, neg_neg]
  simp only [clockDegreeCorrection, star_mul, hs, neg_neg]

lemma clockDegreeCorrection_add (k : unitary E) (d : ℤ) (x y : E) :
    clockDegreeCorrection k d (x + y) =
      clockDegreeCorrection k d x + clockDegreeCorrection k d y := by
  simp only [clockDegreeCorrection, mul_add]

lemma clockDegreeCorrection_smul (k : unitary E) (d : ℤ) (r : ℂ) (x : E) :
    clockDegreeCorrection k d (r • x) = r • clockDegreeCorrection k d x := by
  simp only [clockDegreeCorrection, mul_smul_comm]

lemma clock_commutator_inverse (k : unitary E) (x : E) :
    ‖x * ((k⁻¹ : unitary E) : E) - ((k⁻¹ : unitary E) : E) * x‖ =
      ‖x * (k : E) - (k : E) * x‖ := by
  have hl : ((k⁻¹ : unitary E) : E) * (k : E) = 1 := k.prop.1
  have hr : (k : E) * ((k⁻¹ : unitary E) : E) = 1 := k.prop.2
  have he : x * ((k⁻¹ : unitary E) : E) - ((k⁻¹ : unitary E) : E) * x =
      ((k⁻¹ : unitary E) : E) * ((k : E) * x - x * (k : E)) *
        ((k⁻¹ : unitary E) : E) := by
    symm
    calc
      _ = (((k⁻¹ : unitary E) : E) * (k : E)) * x * ((k⁻¹ : unitary E) : E) -
          ((k⁻¹ : unitary E) : E) * x * ((k : E) * ((k⁻¹ : unitary E) : E)) := by
        noncomm_ring
      _ = _ := by rw [hl, hr, one_mul, mul_one]
  rw [he, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, norm_sub_rev]

lemma clock_commutator_pow (k : unitary E) (x : E) (n : ℕ) :
    ‖x * ((k ^ n : unitary E) : E) - ((k ^ n : unitary E) : E) * x‖ ≤
      (n : ℝ) * ‖x * (k : E) - (k : E) * x‖ := by
  induction n with
  | zero => simp only [pow_zero, Submonoid.coe_one, mul_one, one_mul, sub_self,
      norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
      have he : x * ((k ^ (n + 1) : unitary E) : E) -
          ((k ^ (n + 1) : unitary E) : E) * x =
          (x * ((k ^ n : unitary E) : E) - ((k ^ n : unitary E) : E) * x) * (k : E) +
          ((k ^ n : unitary E) : E) * (x * (k : E) - (k : E) * x) := by
        rw [pow_succ, Submonoid.coe_mul]
        noncomm_ring
      rw [he]
      calc
        _ ≤ ‖(x * ((k ^ n : unitary E) : E) - ((k ^ n : unitary E) : E) * x) * (k : E)‖ +
            ‖((k ^ n : unitary E) : E) * (x * (k : E) - (k : E) * x)‖ := norm_add_le _ _
        _ = ‖x * ((k ^ n : unitary E) : E) - ((k ^ n : unitary E) : E) * x‖ +
            ‖x * (k : E) - (k : E) * x‖ := by
          rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
        _ ≤ _ := by
          rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
          exact add_le_add ih le_rfl

lemma clock_commutator_zpow (k : unitary E) (x : E) (d : ℤ) :
    ‖x * ((k ^ d : unitary E) : E) - ((k ^ d : unitary E) : E) * x‖ ≤
      (d.natAbs : ℝ) * ‖x * (k : E) - (k : E) * x‖ := by
  cases d with
  | ofNat n =>
      change ‖x * ((k ^ (n : ℤ) : unitary E) : E) - ((k ^ (n : ℤ) : unitary E) : E) * x‖ ≤
        (n : ℝ) * ‖x * (k : E) - (k : E) * x‖
      simpa only [zpow_natCast] using clock_commutator_pow k x n
  | negSucc n =>
      have he : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
      rw [he, zpow_neg, zpow_natCast, clock_commutator_inverse]
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using clock_commutator_pow k x (n + 1)

lemma clockDegreeCorrection_mul_error_of_commutator
    (k : unitary E) (d e : ℤ) (x y : E) (δ : ℝ)
    (hc : ‖x * (k : E) - (k : E) * x‖ ≤ δ) :
    ‖clockDegreeCorrection k d x * clockDegreeCorrection k e y -
      clockDegreeCorrection k (d + e) (x * y)‖ ≤
        (e.natAbs : ℝ) * δ * ‖y‖ := by
  apply (clockDegreeCorrection_mul_error k d e x y).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (clock_commutator_zpow k x (-e)).trans (by
    rw [Int.natAbs_neg]
    exact mul_le_mul_of_nonneg_left hc (by positivity))

/-- The full finite product estimate, with the actual pairwise commutators. -/
lemma clockDegreeCorrection_sum_product_error
    {I J : Type*} [Fintype I] [Fintype J]
    (k : unitary E) (d : I → ℤ) (e : J → ℤ) (x : I → E) (y : J → E) :
    ‖(∑ i, clockDegreeCorrection k (d i) (x i)) *
        (∑ j, clockDegreeCorrection k (e j) (y j)) -
      ∑ i, ∑ j, clockDegreeCorrection k (d i + e j) (x i * y j)‖ ≤
      ∑ i, ∑ j,
        ‖x i * ((k ^ (-e j) : unitary E) : E) -
          ((k ^ (-e j) : unitary E) : E) * x i‖ * ‖y j‖ := by
  have heq : (∑ i, clockDegreeCorrection k (d i) (x i)) *
        (∑ j, clockDegreeCorrection k (e j) (y j)) -
      ∑ i, ∑ j, clockDegreeCorrection k (d i + e j) (x i * y j) =
      ∑ i, ∑ j, (clockDegreeCorrection k (d i) (x i) *
          clockDegreeCorrection k (e j) (y j) -
        clockDegreeCorrection k (d i + e j) (x i * y j)) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  exact clockDegreeCorrection_mul_error k (d i) (e j) (x i) (y j)

/-- The explicit correction of the degree `0,1,-1` cancellation formula. -/
def clockCorrectedCancellation (k : unitary E) (a b u : E) (θ : ℝ) : E :=
  1 + (Real.cos θ ^ 2) •
    (a * (u - 1) * star a + b * (star u - 1) * star b) +
  (Real.sin θ * Real.cos θ) •
    (clockDegreeCorrection k 1 (a * (u - 1) * star b) -
      clockDegreeCorrection k (-1) (b * (star u - 1) * star a))

lemma clockCorrectedCancellation_zero (k : unitary E) (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1)
    (hab : star a * b = 0) (hu : u * star u = 1) :
    clockCorrectedCancellation k a b u 0 = cornerCancellationPath a b u 0 := by
  rw [cornerCancellationPath_three_terms a b u ha hb hab hu]
  simp only [clockCorrectedCancellation, Real.cos_zero, Real.sin_zero,
    one_pow, zero_mul, zero_smul, add_zero]

lemma clockCorrectedCancellation_pi_div_two (k : unitary E) (a b u : E) :
    clockCorrectedCancellation k a b u (Real.pi / 2) = 1 := by
  simp only [clockCorrectedCancellation, Real.cos_pi_div_two, Real.sin_pi_div_two,
    zero_pow (by decide : 2 ≠ 0), one_mul, zero_smul, add_zero]

lemma clockCorrectedCancellation_continuous (k : unitary E) (a b u : E) :
    Continuous (clockCorrectedCancellation k a b u) := by
  unfold clockCorrectedCancellation
  fun_prop

/-- At every angle the alteration is exactly the two degree corrections;
this bound does not treat the clock as central. -/
lemma clockCorrectedCancellation_sub_bound (k : unitary E) (a b u : E)
    (ha : star a * a = 1) (hb : star b * b = 1)
    (hab : star a * b = 0) (hu : u * star u = 1) (θ : ℝ) :
    ‖clockCorrectedCancellation k a b u θ - cornerCancellationPath a b u θ‖ ≤
      |Real.sin θ * Real.cos θ| *
        (‖clockDegreeCorrection k 1 (a * (u - 1) * star b) - a * (u - 1) * star b‖ +
         ‖clockDegreeCorrection k (-1) (b * (star u - 1) * star a) -
            b * (star u - 1) * star a‖) := by
  rw [cornerCancellationPath_three_terms a b u ha hb hab hu]
  have heq : clockCorrectedCancellation k a b u θ -
      (1 + (Real.cos θ ^ 2) • (a * (u - 1) * star a + b * (star u - 1) * star b) +
        (Real.sin θ * Real.cos θ) •
          (a * (u - 1) * star b - b * (star u - 1) * star a)) =
      (Real.sin θ * Real.cos θ) •
        ((clockDegreeCorrection k 1 (a * (u - 1) * star b) - a * (u - 1) * star b) -
          (clockDegreeCorrection k (-1) (b * (star u - 1) * star a) -
            b * (star u - 1) * star a)) := by
    unfold clockCorrectedCancellation
    module
  rw [heq, norm_smul, Real.norm_eq_abs]
  gcongr
  exact norm_sub_le _ _

end WeakPureInfiniteness

end

end OAI
