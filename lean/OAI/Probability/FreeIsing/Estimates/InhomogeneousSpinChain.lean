import OAI.Probability.FreeIsing.Cavity.LogOdds
import OAI.Probability.FreeIsing.Estimates.FiniteChain
import OAI.Probability.FreeIsing.Estimates.ThresholdArithmetic
import OAI.Probability.FreeIsing.Spins.Kernel

namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem367.InhomogeneousChain

variable {A : Type*}

def weight (K : ℕ → A → A → ℝ) : (n : ℕ) → A → (Fin n → A) → ℝ
  | 0, _, _ => 1
  | n + 1, a, x => K 0 a (x 0) *
      weight (fun i => K (i + 1)) n (x 0) (Fin.tail x)

@[simp] theorem weight_zero (K : ℕ → A → A → ℝ) (a : A) (x : Fin 0 → A) :
    weight K 0 a x = 1 := rfl

@[simp] theorem weight_cons (K : ℕ → A → A → ℝ)
    (n : ℕ) (a b : A) (x : Fin n → A) :
    weight K (n + 1) a (Fin.cons b x) =
      K 0 a b * weight (fun i => K (i + 1)) n b x := by
  simp [weight]

theorem weight_eq_prod (K : ℕ → A → A → ℝ) (n : ℕ)
    (a : A) (x : Fin n → A) :
    weight K n a x = ∏ i : Fin n,
      K i ((Fin.cons a x : Fin (n + 1) → A) i.castSucc) (x i) := by
  induction n generalizing K a with
  | zero => simp
  | succ n ih =>
    rw [weight, Fin.prod_univ_succ, ih]
    simp [Fin.tail]

theorem weight_nonneg (K : ℕ → A → A → ℝ)
    (hK : ∀ i a b, 0 ≤ K i a b) (n : ℕ) (a : A) (x : Fin n → A) :
    0 ≤ weight K n a x := by
  rw [weight_eq_prod]
  exact Finset.prod_nonneg fun i _ => hK i _ _

def jointWeight (K : ℕ → A → A → ℝ) (w : A → ℝ) (n : ℕ)
    (x : Fin (n + 1) → A) : ℝ :=
  w (x 0) * ∏ i : Fin n, K i (x i.castSucc) (x i.succ)

@[simp] theorem jointWeight_cons (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (n : ℕ) (a : A) (x : Fin n → A) :
    jointWeight K w n (Fin.cons a x) = w a * weight K n a x := by
  rw [weight_eq_prod]
  simp [jointWeight]

theorem jointWeight_nonneg (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (hK : ∀ i a b, 0 ≤ K i a b) (hw : ∀ a, 0 ≤ w a)
    (n : ℕ) (x : Fin (n + 1) → A) : 0 ≤ jointWeight K w n x := by
  exact mul_nonneg (hw _) (Finset.prod_nonneg fun i _ => hK i _ _)

variable [Fintype A]

def expectation (K : ℕ → A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) : ℝ :=
  ∑ x : Fin n → A, weight K n a x * f (FiniteChain.endpoint n a x)

@[simp] theorem expectation_zero (K : ℕ → A → A → ℝ) (f : A → ℝ) (a : A) :
    expectation K 0 f a = f a := by
  simp [expectation]

theorem expectation_succ (K : ℕ → A → A → ℝ) (n : ℕ) (f : A → ℝ) (a : A) :
    expectation K (n + 1) f a =
      ∑ b, K 0 a b * expectation (fun i => K (i + 1)) n f b := by
  unfold expectation
  rw [FiniteChain.sum_cons]
  simp only [weight_cons, FiniteChain.endpoint_cons, mul_assoc, Finset.mul_sum]

theorem sum_weight (K : ℕ → A → A → ℝ)
    (hK : ∀ i a, ∑ b, K i a b = 1) (n : ℕ) (a : A) :
    ∑ x : Fin n → A, weight K n a x = 1 := by
  induction n generalizing K a with
  | zero => simp
  | succ n ih =>
    rw [FiniteChain.sum_cons]
    simp only [weight_cons, ← Finset.mul_sum]
    simp only [ih (fun i => K (i + 1)) (fun i => hK (i + 1)), mul_one]
    exact hK 0 a

theorem sum_jointWeight (K : ℕ → A → A → ℝ) (w : A → ℝ)
    (hK : ∀ i a, ∑ b, K i a b = 1) (hw : ∑ a, w a = 1) (n : ℕ) :
    ∑ x : Fin (n + 1) → A, jointWeight K w n x = 1 := by
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, ← Finset.mul_sum, sum_weight K hK, mul_one]
  exact hw

theorem sum_jointWeight_endpoints (K : ℕ → A → A → ℝ) (w f g : A → ℝ) (n : ℕ) :
    (∑ x : Fin (n + 1) → A,
      jointWeight K w n x * f (x 0) * g (x (Fin.last n))) =
    ∑ a, w a * f a * expectation K n g a := by
  rw [FiniteChain.sum_cons]
  simp only [jointWeight_cons, Fin.cons_zero, ← FiniteChain.endpoint_eq_last]
  apply Finset.sum_congr rfl
  intro a _
  rw [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem expectation_affine (K : ℕ → A → A → ℝ) (f : A → ℝ)
    (p q : ℕ → ℝ) (hK : ∀ i a, ∑ b, K i a b = 1)
    (hmean : ∀ i a, ∑ b, K i a b * f b = p i + q i * f a) (n : ℕ) :
    ∃ c : ℝ, ∀ a, expectation K n f a =
      c + (∏ i ∈ Finset.range n, q i) * f a := by
  induction n generalizing K p q with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih (fun i => K (i + 1))
      (fun i => p (i + 1)) (fun i => q (i + 1))
      (fun i => hK (i + 1)) (fun i => hmean (i + 1))
    let Q := ∏ i ∈ Finset.range n, q (i + 1)
    refine ⟨c + Q * p 0, ?_⟩
    intro a
    rw [expectation_succ]
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib]
    have hconst : (∑ b, K 0 a b * c) = c := by
      rw [← Finset.sum_mul, hK, one_mul]
    have hlinear : (∑ b, K 0 a b * (Q * f b)) =
        Q * (p 0 + q 0 * f a) := by
      calc
        _ = Q * ∑ b, K 0 a b * f b := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
        _ = _ := by rw [hmean]
    change (∑ b, K 0 a b * c) + (∑ b, K 0 a b * (Q * f b)) = _
    rw [hconst, hlinear, Finset.prod_range_succ']
    dsimp [Q]
    ring

theorem covariance_eq_variance_mul_prod
    (K : ℕ → A → A → ℝ) (f : A → ℝ) (p q : ℕ → ℝ)
    (w : A → ℝ) (hw : ∑ a, w a = 1)
    (hK : ∀ i a, ∑ b, K i a b = 1)
    (hmean : ∀ i a, ∑ b, K i a b * f b = p i + q i * f a) (n : ℕ) :
    (∑ a, w a * f a * expectation K n f a) -
      (∑ a, w a * f a) * (∑ a, w a * expectation K n f a) =
    ((∑ a, w a * (f a) ^ 2) - (∑ a, w a * f a) ^ 2) *
      (∏ i ∈ Finset.range n, q i) := by
  obtain ⟨c, hc⟩ := expectation_affine K f p q hK hmean n
  let Q := ∏ i ∈ Finset.range n, q i
  have hfirst : (∑ a, w a * expectation K n f a) =
      c + Q * (∑ a, w a * f a) := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib]
    calc
      _ = (∑ a, w a) * c + Q * (∑ a, w a * f a) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = _ := by rw [hw, one_mul]
  have hsecond : (∑ a, w a * f a * expectation K n f a) =
      c * (∑ a, w a * f a) + Q * (∑ a, w a * (f a) ^ 2) := by
    simp_rw [hc, mul_add]
    rw [Finset.sum_add_distrib]
    simp only [Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro a _ <;> ring
  rw [hfirst, hsecond]
  dsimp [Q]
  ring

end Problem367.InhomogeneousChain

namespace Problem367.PosteriorChain

def transition (beta z : ℝ) (a b : IsingSpin) : ℝ :=
  (1 + spinSign b * Real.tanh (z + beta * spinSign a)) / 2

@[simp] theorem transition_sum (beta z : ℝ) (a : IsingSpin) :
    ∑ b, transition beta z a b = 1 := by
  rw [sum_isingSpin]
  simp only [transition, spinSign_neg, spinSign_pos]
  ring

@[simp] theorem transition_spinMean (beta z : ℝ) (a : IsingSpin) :
    ∑ b, transition beta z a b * spinSign b =
      Real.tanh (z + beta * spinSign a) := by
  rw [sum_isingSpin]
  simp only [transition, spinSign_neg, spinSign_pos]
  ring

theorem transition_pos (beta z : ℝ) (a b : IsingSpin) :
    0 < transition beta z a b := by
  have h := Real.abs_tanh_lt_one (z + beta * spinSign a)
  have hh := abs_lt.mp h
  cases b <;> simp only [transition, spinSign_neg, spinSign_pos] <;> linarith

def intercept (beta z : ℝ) : ℝ :=
  (Real.tanh (z + beta) + Real.tanh (z - beta)) / 2

def slope (beta z : ℝ) : ℝ :=
  (Real.tanh (z + beta) - Real.tanh (z - beta)) / 2

theorem transition_spinMean_affine (beta z : ℝ) (a : IsingSpin) :
    ∑ b, transition beta z a b * spinSign b =
      intercept beta z + slope beta z * spinSign a := by
  rw [transition_spinMean]
  cases a <;> simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one,
    ← sub_eq_add_neg, intercept, slope] <;> ring

theorem slope_eq_responseAttenuation (beta z : ℝ) :
    slope beta z = Real.tanh beta * responseAttenuation (Real.tanh beta) z := by
  simpa only [slope, responseAttenuation, mul_div_assoc] using
    tanh_field_difference_eq beta z

theorem slope_mem_Icc {beta : ℝ} (hbeta : 0 ≤ beta) (z : ℝ) :
    slope beta z ∈ Set.Icc 0 (Real.tanh beta) := by
  rw [slope_eq_responseAttenuation]
  have hθ : 0 ≤ Real.tanh beta := by
    exact tanh_nonneg_of_beta_nonneg hbeta
  have hs : Real.tanh beta ^ 2 ≤ 1 := (Real.tanh_sq_lt_one beta).le
  exact ⟨mul_nonneg hθ (responseAttenuation_pos hs z).le,
    by simpa using mul_le_mul_of_nonneg_left (responseAttenuation_le_one hs z) hθ⟩

theorem covariance_eq_response_product (beta : ℝ) (z : ℕ → ℝ)
    (w : IsingSpin → ℝ) (hw : ∑ a, w a = 1) (n : ℕ) :
    (∑ a, w a * spinSign a *
      InhomogeneousChain.expectation (fun i => transition beta (z i)) n spinSign a) -
      (∑ a, w a * spinSign a) *
        (∑ a, w a * InhomogeneousChain.expectation
          (fun i => transition beta (z i)) n spinSign a) =
    (1 - (∑ a, w a * spinSign a) ^ 2) * Real.tanh beta ^ n *
      (∏ i ∈ Finset.range n, responseAttenuation (Real.tanh beta) (z i)) := by
  have h := InhomogeneousChain.covariance_eq_variance_mul_prod
    (fun i => transition beta (z i)) spinSign
    (fun i => intercept beta (z i)) (fun i => slope beta (z i)) w hw
    (fun i => transition_sum beta (z i))
    (fun i => transition_spinMean_affine beta (z i)) n
  simp only [spinSign_sq, mul_one, hw] at h
  rw [h]
  simp_rw [slope_eq_responseAttenuation]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_range]
  ring

theorem initial_variance_mem_Icc (w : IsingSpin → ℝ)
    (hw0 : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1) :
    1 - (∑ a, w a * spinSign a) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
  rw [sum_isingSpin] at hw
  rw [sum_isingSpin]
  simp only [spinSign_neg, spinSign_pos, mul_neg_one, mul_one]
  have hn := hw0 .neg
  have hp := hw0 .pos
  constructor <;> nlinarith [sq_nonneg (w .pos - w .neg), mul_nonneg hn hp]

theorem covariance_mem_Icc {beta : ℝ} (hbeta : 0 ≤ beta) (z : ℕ → ℝ)
    (w : IsingSpin → ℝ) (hw0 : ∀ a, 0 ≤ w a) (hw : ∑ a, w a = 1) (n : ℕ) :
    ((∑ a, w a * spinSign a *
      InhomogeneousChain.expectation (fun i => transition beta (z i)) n spinSign a) -
      (∑ a, w a * spinSign a) *
        (∑ a, w a * InhomogeneousChain.expectation
          (fun i => transition beta (z i)) n spinSign a)) ∈
      Set.Icc 0 (Real.tanh beta ^ n) := by
  rw [covariance_eq_response_product beta z w hw]
  have hv := initial_variance_mem_Icc w hw0 hw
  have hθ := tanh_nonneg_of_beta_nonneg hbeta
  have hs : Real.tanh beta ^ 2 ≤ 1 := (Real.tanh_sq_lt_one beta).le
  have ha0 : 0 ≤ ∏ i ∈ Finset.range n,
      responseAttenuation (Real.tanh beta) (z i) :=
    Finset.prod_nonneg fun i _ => (responseAttenuation_pos hs (z i)).le
  have ha1 : (∏ i ∈ Finset.range n,
      responseAttenuation (Real.tanh beta) (z i)) ≤ 1 :=
    Finset.prod_le_one₀ (fun index _ => (responseAttenuation_pos hs (z index)).le)
      (fun i _ => responseAttenuation_le_one hs (z i))
  constructor
  · exact mul_nonneg (mul_nonneg hv.1 (pow_nonneg hθ n)) ha0
  · calc
      _ ≤ (1 - (∑ a, w a * spinSign a) ^ 2) * Real.tanh beta ^ n :=
        mul_le_of_le_one_right (mul_nonneg hv.1 (pow_nonneg hθ n)) ha1
      _ ≤ Real.tanh beta ^ n :=
        mul_le_of_le_one_left (pow_nonneg hθ n) hv.2

end Problem367.PosteriorChain

end

end OAI
