import OAI.NumberTheory.CubicMoment.Estimates.SmoothNormPartition

namespace OAI

/-! The explicit smooth partition inserted into finite convolution tuples.
Nonzero pieces automatically have the required product-length comparability. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normTupleWeight {N : ℕ} (k : ι → Fin N) (x : ι → ℝ) : ℂ :=
  ∏ i, normPartitionWeight (2*x i/(4/3:ℝ)^(k i).val)

lemma normTupleWeight_partition {B : ℝ} {N : ℕ} (x : ι → ℝ)
    (hx : ∀ i, 1 ≤ x i) (hB : ∀ i, x i ≤ B) (hN : 2*B ≤ (4/3:ℝ)^N) :
    (∑ k : ι → Fin N, normTupleWeight k x) = 1 := by
  unfold normTupleWeight
  rw [← Fintype.prod_sum (fun (i : ι) (k : Fin N) =>
    normPartitionWeight (2*x i/(4/3:ℝ)^k.val))]
  have hi (i : ι) : (∑ k : Fin N, normPartitionWeight (2*x i/(4/3:ℝ)^k.val)) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => normPartitionWeight (2*x i/(4/3:ℝ)^k))]
    exact normPartitionWeight_partition (hx i) (hB i) hN
  simp_rw [hi]
  simp

theorem finite_sum_normTupleWeight {κ : Type*} (S : Finset κ) (f : κ → ℂ)
    (x : κ → ι → ℝ) {B : ℝ} {N : ℕ}
    (hx : ∀ a ∈ S, ∀ i, 1 ≤ x a i) (hB : ∀ a ∈ S, ∀ i, x a i ≤ B)
    (hN : 2*B ≤ (4/3:ℝ)^N) :
    (∑ a ∈ S, f a) = ∑ k : ι → Fin N, ∑ a ∈ S, f a*normTupleWeight k (x a) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.mul_sum,normTupleWeight_partition (x a) (hx a ha) (hB a ha) hN,mul_one]

lemma normPartitionWeight_nonzero_scale {x : ℝ} {k : ℕ}
    (h : normPartitionWeight (2*x/(4/3:ℝ)^k) ≠ 0) :
    x ≤ (4/3:ℝ)^k ∧ (4/3:ℝ)^k ≤ 2*x := by
  have hp : 0 < (4/3:ℝ)^k := pow_pos (by norm_num) _
  have hlo : 1 ≤ 2*x/(4/3:ℝ)^k := by
    by_contra hn
    exact h (normPartitionWeight_low (lt_of_not_ge hn))
  have hhi : 2*x/(4/3:ℝ)^k ≤ 2 := by
    by_contra hn
    exact h (normPartitionWeight_high (lt_of_not_ge hn))
  constructor
  · have := (div_le_iff₀ hp).mp hhi
    linarith
  · have := (le_div_iff₀ hp).mp hlo
    linarith

omit [DecidableEq ι] in
theorem normTupleWeight_product_lengths {N : ℕ} (k : ι → Fin N) (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (h : normTupleWeight k x ≠ 0) :
    (∏ i, x i) ≤ (∏ i, (4/3:ℝ)^(k i).val) ∧
      (∏ i, (4/3:ℝ)^(k i).val) ≤ 2^(Fintype.card ι)*(∏ i, x i) := by
  have hi (i : ι) : normPartitionWeight (2*x i/(4/3:ℝ)^(k i).val) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp h) i (Finset.mem_univ i)
  have hb (i : ι) := normPartitionWeight_nonzero_scale (hi i)
  constructor
  · exact Finset.prod_le_prod₀ (fun i _ => hx i) (fun i _ => (hb i).1)
  · calc
      _ ≤ ∏ i, 2*x i := Finset.prod_le_prod₀
        (fun i _ => (pow_pos (by norm_num : (0:ℝ) < 4/3) _).le) (fun i _ => (hb i).2)
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

end CubicFirstMoment

end

end OAI
