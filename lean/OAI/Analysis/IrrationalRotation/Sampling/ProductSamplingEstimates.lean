import Mathlib

namespace OAI

open scoped BigOperators

namespace Invariant233.ProductSampling

theorem abs_prod_sub_prod_le {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (ha : ∀ i ∈ s, |a i| ≤ B) (hb : ∀ i ∈ s, |b i| ≤ B)
    (hab : ∀ i ∈ s, |a i - b i| ≤ ε) :
    |(∏ i ∈ s, a i) - ∏ i ∈ s, b i| ≤
      (s.card : ℝ) * ε * B ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hai : |a i| ≤ B := ha i (Finset.mem_insert_self _ _)
      have habi : |a i - b i| ≤ ε := hab i (Finset.mem_insert_self _ _)
      have has : ∀ j ∈ s, |a j| ≤ B := fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hbs : ∀ j ∈ s, |b j| ≤ B := fun j hj => hb j (Finset.mem_insert_of_mem hj)
      have habs : ∀ j ∈ s, |a j - b j| ≤ ε :=
        fun j hj => hab j (Finset.mem_insert_of_mem hj)
      rcases s.eq_empty_or_nonempty with rfl | hs
      · simpa using habi
      have hprod : |∏ j ∈ s, b j| ≤ B ^ s.card := by
        rw [Finset.abs_prod]
        calc
          ∏ j ∈ s, |b j| ≤ ∏ _j ∈ s, B :=
            Finset.prod_le_prod₀ (fun index _ => abs_nonneg (b index)) hbs
          _ = B ^ s.card := by simp
      have hpow : B * B ^ (s.card - 1) = B ^ s.card := by
        rw [← pow_succ', Nat.sub_add_cancel (Finset.card_pos.mpr hs)]
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
      calc
        |a i * (∏ j ∈ s, a j) - b i * ∏ j ∈ s, b j| =
            |a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j) +
              (a i - b i) * ∏ j ∈ s, b j| := by congr 1; ring
        _ ≤ |a i| * |(∏ j ∈ s, a j) - ∏ j ∈ s, b j| +
              |a i - b i| * |∏ j ∈ s, b j| := by
          simpa only [abs_mul] using abs_add_le
            (a i * ((∏ j ∈ s, a j) - ∏ j ∈ s, b j))
            ((a i - b i) * ∏ j ∈ s, b j)
        _ ≤ B * ((s.card : ℝ) * ε * B ^ (s.card - 1)) + ε * B ^ s.card := by
          exact add_le_add
            (mul_le_mul hai (ih has hbs habs) (abs_nonneg _) hB)
            (mul_le_mul habi hprod (abs_nonneg _) hε)
        _ = (s.card : ℝ) * ε * (B * B ^ (s.card - 1)) + ε * B ^ s.card := by ring
        _ = ((s.card + 1 : ℕ) : ℝ) * ε * B ^ ((s.card + 1) - 1) := by
          rw [hpow, Nat.add_sub_cancel]
          push_cast
          ring

theorem abs_prod_add_error_sub_prod_le {ι : Type*} (s : Finset ι)
    (A e : ι → ℝ) {B ε : ℝ} (hB : 0 ≤ B) (hε : 0 ≤ ε)
    (hA : ∀ i ∈ s, 0 ≤ A i ∧ A i ≤ B)
    (he : ∀ i ∈ s, |e i| ≤ ε) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * ε * (B + ε) ^ (s.card - 1) := by
  apply abs_prod_sub_prod_le s (fun i => A i + e i) A (add_nonneg hB hε) hε
  · intro i hi
    calc
      |A i + e i| ≤ |A i| + |e i| := abs_add_le _ _
      _ ≤ B + ε := add_le_add (by simpa [abs_of_nonneg (hA i hi).1] using (hA i hi).2)
        (he i hi)
  · intro i hi
    rw [abs_of_nonneg (hA i hi).1]
    exact le_trans (hA i hi).2 (le_add_of_nonneg_right hε)
  · intro i hi
    simpa using he i hi

theorem abs_prod_add_error_sub_prod_le_exp {ι : Type*} (s : Finset ι)
    (A e : ι → ℝ) {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hA : ∀ i ∈ s, 0 ≤ A i ∧ A i ≤ 1 + δ)
    (he : ∀ i ∈ s, |e i| ≤ ε) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * ε * Real.exp ((s.card : ℝ) * (δ + ε)) := by
  have hbase : 1 ≤ 1 + δ + ε := by linarith
  have hpow : (1 + δ + ε) ^ (s.card - 1) ≤
      Real.exp ((s.card : ℝ) * (δ + ε)) := by
    calc
      (1 + δ + ε) ^ (s.card - 1) ≤ (1 + δ + ε) ^ s.card :=
        pow_le_pow_right₀ hbase (Nat.sub_le _ _)
      _ ≤ Real.exp (δ + ε) ^ s.card := by
        apply pow_le_pow_left₀ (by linarith)
        simpa [add_comm, add_left_comm, add_assoc] using Real.add_one_le_exp (δ + ε)
      _ = Real.exp ((s.card : ℝ) * (δ + ε)) := (Real.exp_nat_mul _ _).symm
  exact (abs_prod_add_error_sub_prod_le s A e (by linarith) hε hA he).trans
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg (Nat.cast_nonneg _) hε))

theorem abs_prod_add_error_sub_prod_le_of_total_le {ι : Type*} (s : Finset ι)
    (A e : ι → ℝ) {δ ε C : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hA : ∀ i ∈ s, 0 ≤ A i ∧ A i ≤ 1 + δ)
    (he : ∀ i ∈ s, |e i| ≤ ε)
    (htotal : (s.card : ℝ) * (δ + ε) ≤ C) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * ε * Real.exp C := by
  exact (abs_prod_add_error_sub_prod_le_exp s A e hδ hε hA he).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htotal)
      (mul_nonneg (Nat.cast_nonneg _) hε))

theorem mul_rpow_le_one {m r : ℝ} (hm : 1 ≤ m) (hr : r ≤ -1) :
    m * m ^ r ≤ 1 := by
  have hpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  calc
    m * m ^ r = m ^ (1 + r) := by rw [Real.rpow_add hpos, Real.rpow_one]
    _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm (by linarith)

theorem growing_product_error_bound {ι : Type*} (s : Finset ι)
    (A e : ι → ℝ) {m c : ℝ} (hm : 1 ≤ m) (hc : 0 ≤ c)
    (hd : (s.card : ℝ) ≤ (101 / 100 : ℝ) * m)
    (hA : ∀ i ∈ s, 0 ≤ A i ∧ A i ≤ 1 + c * m ^ (-6 / 5 : ℝ))
    (he : ∀ i ∈ s, |e i| ≤ c * m ^ (-50 : ℝ)) :
    |(∏ i ∈ s, (A i + e i)) - ∏ i ∈ s, A i| ≤
      (s.card : ℝ) * (c * m ^ (-50 : ℝ)) * Real.exp ((101 / 50 : ℝ) * c) := by
  have hm0 : 0 ≤ m := le_trans zero_le_one hm
  have hδ : 0 ≤ c * m ^ (-6 / 5 : ℝ) := mul_nonneg hc (Real.rpow_nonneg hm0 _)
  have hε : 0 ≤ c * m ^ (-50 : ℝ) := mul_nonneg hc (Real.rpow_nonneg hm0 _)
  apply abs_prod_add_error_sub_prod_le_of_total_le s A e hδ hε hA he
  calc
    (s.card : ℝ) * (c * m ^ (-6 / 5 : ℝ) + c * m ^ (-50 : ℝ)) ≤
        ((101 / 100 : ℝ) * m) *
          (c * m ^ (-6 / 5 : ℝ) + c * m ^ (-50 : ℝ)) :=
      mul_le_mul_of_nonneg_right hd (add_nonneg hδ hε)
    _ = ((101 / 100 : ℝ) * c) *
        (m * m ^ (-6 / 5 : ℝ) + m * m ^ (-50 : ℝ)) := by ring
    _ ≤ ((101 / 100 : ℝ) * c) * (1 + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (mul_rpow_le_one hm (by norm_num))
        (mul_rpow_le_one hm (by norm_num))
    _ = (101 / 50 : ℝ) * c := by ring

end Invariant233.ProductSampling

end OAI
