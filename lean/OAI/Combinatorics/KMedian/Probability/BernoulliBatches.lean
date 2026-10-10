import Mathlib
import OAI.Combinatorics.KMedian.Probability.FiniteLaws

namespace OAI

namespace MetricKMedian
namespace FiniteLaw
variable {I : Type*} [Fintype I] [DecidableEq I]

def coinWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

@[simp] theorem coinWeight_true (p : ℝ) : coinWeight p true = p := rfl
@[simp] theorem coinWeight_false (p : ℝ) : coinWeight p false = 1-p := rfl

theorem coinWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ coinWeight p b := by cases b <;> simp [hp, hp1, sub_nonneg]

@[simp] theorem coinWeight_total (p : ℝ) : ∑ b : Bool, coinWeight p b = 1 := by
  simp

noncomputable def bernoulli (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    FiniteLaw (I → Bool) where
  weight ω := ∏ i, coinWeight (p i) (ω i)
  nonneg ω := Finset.prod_nonneg (fun i _ => coinWeight_nonneg (hp i) (hp1 i) (ω i))
  total := by rw [← Fintype.prod_sum]; simp

theorem bernoulli_expect_prod (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (f : I → Bool → ℝ) :
    (bernoulli p hp hp1).expect (fun ω => ∏ i, f i (ω i)) =
       ∏ i, ((1-p i)*f i false+p i*f i true) := by
  unfold expect bernoulli
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => coinWeight (p i) b * f i b)]
  simp only [Fintype.sum_bool, coinWeight_true, coinWeight_false]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem bernoulli_cylinder (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (S : Finset I) (c : I → Bool) :
    (bernoulli p hp hp1).prob (fun ω => ∀ i ∈ S, ω i = c i) =
      ∏ i ∈ S, coinWeight (p i) (c i) := by
  classical
  have hpoint : ∀ ω : I → Bool,
      (if ∀ i ∈ S, ω i = c i then (1:ℝ) else 0) =
      ∏ i, (if i ∈ S then if ω i = c i then (1:ℝ) else 0 else 1) := by
    intro ω
    by_cases h : ∀ i ∈ S, ω i = c i
    · rw [ite_eq_left h]
      symm
      apply Finset.prod_eq_one
      intro i _
      by_cases hi : i ∈ S <;> simp [hi, h]
    · rw [ite_eq_right h]
      push Not at h
      obtain ⟨i, hi, hne⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi, hne]
  unfold prob
  simp_rw [hpoint]
  rw [bernoulli_expect_prod p hp hp1 (fun i b => if i ∈ S then if b = c i then 1 else 0 else 1)]
  have hfactor : ∀ i,
      (1-p i)*(if i ∈ S then if false = c i then (1:ℝ) else 0 else 1)+
      p i*(if i ∈ S then if true = c i then (1:ℝ) else 0 else 1) =
      if i ∈ S then coinWeight (p i) (c i) else 1 := by
    intro i
    by_cases hi : i ∈ S
    · cases hc : c i <;> simp [hi]
    · simp [hi]
  simp_rw [hfactor]
  simp only [← Finset.prod_filter, Finset.filter_univ_mem]

theorem bernoulli_marginal (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : I) :
    (bernoulli p hp hp1).prob (fun ω => ω i = true) = p i := by
  simpa only [Finset.mem_singleton, forall_eq, Finset.prod_singleton, coinWeight_true] using
    bernoulli_cylinder p hp hp1 {i} (fun _ => true)

theorem bernoulli_pair (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {i j : I} (hij : i ≠ j) :
    (bernoulli p hp hp1).prob (fun ω => ω i = true ∧ ω j = true) = p i*p j := by
  simpa [hij] using
    bernoulli_cylinder p hp hp1 {i,j} (fun _ => true)

noncomputable def selected (C : I → Finset I) (ω : I → Bool) : Finset I :=
  Finset.univ.filter (fun i => ω i = true ∧ ∀ j ∈ C i, ω j = false)

theorem filtered_marginal (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (C : I → Finset I) (i : I) (hself : i ∉ C i) :
    (bernoulli (fun _ : I => p) (fun _ => hp) (fun _ => hp1)).prob
      (fun ω => i ∈ selected C ω) = p*(1-p)^(C i).card := by
  classical
  let c : I → Bool := fun j => if j=i then true else false
  have hevent : (fun ω : I → Bool => i ∈ selected C ω) =
      (fun ω => ∀ j ∈ insert i (C i), ω j = c j) := by
    funext ω
    apply propext
    simp only [selected, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.forall_mem_insert]
    constructor
    · rintro ⟨hi, hC⟩
      refine ⟨by simpa only [c, ite_eq_left rfl] using hi, ?_⟩
      intro j hj
      have hji : j ≠ i := by rintro rfl; exact hself hj
      simpa only [c, ite_eq_right hji] using hC j hj
    · rintro ⟨hi, hC⟩
      refine ⟨by simpa only [c, ite_eq_left rfl] using hi, ?_⟩
      intro j hj
      have hji : j ≠ i := by rintro rfl; exact hself hj
      simpa only [c, ite_eq_right hji] using hC j hj
  rw [(bernoulli (fun _ : I => p) (fun _ => hp) (fun _ => hp1)).prob_congr
    (fun ω => Iff.of_eq (congrFun hevent ω)), bernoulli_cylinder, Finset.prod_insert hself]
  simp only [c, ite_eq_left rfl, coinWeight_true]
  congr 1
  calc
    (∏ j ∈ C i, coinWeight p (if j=i then true else false)) = ∏ _j ∈ C i, (1-p) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := by rintro rfl; exact hself hj
      simp only [ite_eq_right hji, coinWeight_false]
    _ = (1-p)^(C i).card := Finset.prod_const _

theorem filtered_pair_le (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (C : I → Finset I) {i j : I} (hij : i ≠ j) :
    (bernoulli (fun _ : I => p) (fun _ => hp) (fun _ => hp1)).prob
      (fun ω => i ∈ selected C ω ∧ j ∈ selected C ω) ≤ p^2 := by
  have hevent : ∀ ω, i ∈ selected C ω ∧ j ∈ selected C ω →
      ω i = true ∧ ω j = true := by
    intro ω h
    exact ⟨(Finset.mem_filter.mp h.1).2.1, (Finset.mem_filter.mp h.2).2.1⟩
  have hb := (bernoulli (fun _ : I => p) (fun _ => hp) (fun _ => hp1)).prob_mono hevent
  rw [bernoulli_pair _ _ _ hij] at hb
  simpa only [pow_two] using hb

theorem filtered_marginal_error (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (C : I → Finset I) (i : I) (hself : i ∉ C i) :
    |(bernoulli (fun _ : I => p) (fun _ => hp) (fun _ => hp1)).prob
      (fun ω => i ∈ selected C ω)-p| ≤ (C i).card*p^2 := by
  rw [filtered_marginal p hp hp1 C i hself]
  have hpow : (1-p)^(C i).card ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hbern := one_add_mul_le_pow (show (-2:ℝ) ≤ -p by linarith) (C i).card
  have hlower := mul_le_mul_of_nonneg_left hbern hp
  simp only [← sub_eq_add_neg] at hlower
  have hupper := mul_le_mul_of_nonneg_left hpow hp
  have hnonneg : 0 ≤ (C i).card*p^2 := mul_nonneg (Nat.cast_nonneg _) (sq_nonneg p)
  apply abs_le.mpr
  constructor <;> nlinarith only [hlower, hupper, hnonneg]

end FiniteLaw
end MetricKMedian

end OAI
