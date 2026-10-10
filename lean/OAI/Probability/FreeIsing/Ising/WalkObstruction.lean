import OAI.Probability.FreeIsing.Estimates.RadialRepresentation
import OAI.Probability.FreeIsing.Spectral.PowerObstruction

namespace OAI

noncomputable section

namespace Problem367
namespace IsingWalk

def conjugateRoot (b theta : ℝ) : ℝ := (b * theta)⁻¹

def eigenRate (b theta : ℝ) : ℝ := (b * theta + theta⁻¹) / (b + 1)

def eigenWeight (b theta : ℝ) (n : ℕ) : ℝ :=
  (eigenRate b theta - conjugateRoot b theta) * theta ^ n -
    (eigenRate b theta - theta) * conjugateRoot b theta ^ n

theorem conjugateRoot_pos {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta) :
    0 < conjugateRoot b theta := by
  exact inv_pos.mpr (mul_pos hb ht)

theorem conjugateRoot_lt {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta)
    (hcritical : 1 < b * theta ^ 2) : conjugateRoot b theta < theta := by
  unfold conjugateRoot
  rw [inv_eq_one_div]
  apply (div_lt_iff₀ (mul_pos hb ht)).2
  nlinarith

theorem theta_le_eigenRate {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta)
    (ht1 : theta ≤ 1) : theta ≤ eigenRate b theta := by
  have hi : theta ≤ theta⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ ht).2
    nlinarith
  unfold eigenRate
  apply (le_div_iff₀ (by linarith : 0 < b + 1)).2
  nlinarith

theorem eigenRate_pos {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta) :
    0 < eigenRate b theta := by
  unfold eigenRate
  positivity

theorem theta_characteristic {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta) :
    1 + b * theta ^ 2 = (b + 1) * eigenRate b theta * theta := by
  unfold eigenRate
  field_simp
  ring

theorem conjugate_characteristic {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta) :
    1 + b * conjugateRoot b theta ^ 2 =
      (b + 1) * eigenRate b theta * conjugateRoot b theta := by
  unfold conjugateRoot eigenRate
  field_simp

@[simp] theorem eigenWeight_zero (b theta : ℝ) :
    eigenWeight b theta 0 = theta - conjugateRoot b theta := by
  simp [eigenWeight]

theorem eigenWeight_one (b theta : ℝ) :
    eigenWeight b theta 1 = eigenRate b theta * eigenWeight b theta 0 := by
  simp only [eigenWeight, pow_one, pow_zero]
  ring

theorem eigenWeight_recurrence {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta)
    (n : ℕ) :
    eigenWeight b theta n + b * eigenWeight b theta (n + 2) =
      (b + 1) * eigenRate b theta * eigenWeight b theta (n + 1) := by
  have h1 := theta_characteristic hb ht
  have h2 := conjugate_characteristic hb ht
  unfold eigenWeight
  simp only [pow_add, pow_one, pow_two]
  linear_combination
    (eigenRate b theta - conjugateRoot b theta) * theta ^ n * h1 -
    (eigenRate b theta - theta) * conjugateRoot b theta ^ n * h2

theorem eigenWeight_le {b theta : ℝ} (hb : 0 < b) (ht : 0 < theta)
    (ht1 : theta ≤ 1) (n : ℕ) :
    eigenWeight b theta n ≤ (eigenRate b theta - conjugateRoot b theta) * theta ^ n := by
  unfold eigenWeight
  have := mul_nonneg (sub_nonneg.mpr (theta_le_eigenRate hb ht ht1))
    (pow_nonneg (conjugateRoot_pos hb ht).le n)
  linarith

theorem critical_square_lt {b theta : ℝ} (hb : 0 < b)
    (ht : 1 / Real.sqrt b < theta) : 1 < b * theta ^ 2 := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hp : 1 < theta * Real.sqrt b := (div_lt_iff₀ hs).mp ht
  have he : (theta * Real.sqrt b) ^ 2 = b * theta ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb.le]
    ring
  nlinarith

theorem eigenRate_gt_critical {b theta : ℝ} (hb : 0 < b)
    (ht : 1 / Real.sqrt b < theta) :
    2 * Real.sqrt b / (b + 1) < eigenRate b theta := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have ht0 : 0 < theta := lt_trans (one_div_pos.mpr hs) ht
  have hp : 1 < theta * Real.sqrt b := (div_lt_iff₀ hs).mp ht
  have hsq : 0 < (theta * Real.sqrt b - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have he : (theta * Real.sqrt b) ^ 2 = b * theta ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb.le]
    ring
  have hc := theta_characteristic hb ht0
  apply (div_lt_iff₀ (by linarith : 0 < b + 1)).2
  nlinarith

def treeEigenWeight (d : ℕ) (theta : ℝ) (v : TreeVertex d) : ℝ :=
  eigenWeight ((d : ℝ) - 1) theta v.1.length

theorem average_treeEigenWeight {d : ℕ} (hd : 3 ≤ d) {theta : ℝ} (ht : 0 < theta)
    (v : TreeVertex d) :
    RadialWalk.average treeStep (treeEigenWeight d theta) v =
      eigenRate ((d : ℝ) - 1) theta * treeEigenWeight d theta v := by
  classical
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  have hsum := sum_treeNeighborFinset_radial v (eigenWeight ((d : ℝ) - 1) theta)
  rw [treeNeighborFinset, Finset.sum_image (treeStep_injective v).injOn] at hsum
  unfold RadialWalk.average treeEigenWeight
  rw [hsum]
  by_cases hv : v.1.length = 0
  · rw [ite_eq_left hv, hv]
    rw [mul_div_cancel_left₀ _ hd0]
    exact eigenWeight_one _ _
  · rw [ite_eq_right hv]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hv
    rw [hn]
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
    apply (div_eq_iff hd0).2
    have hr := eigenWeight_recurrence hb ht n
    convert hr using 1
    ring

theorem iterate_eigenfunction {V : Type*} {d : ℕ} (step : V → Fin d → V)
    (q : V → ℝ) (lambda : ℝ)
    (hq : ∀ v, RadialWalk.average step q v = lambda * q v) (n : ℕ) :
    ∀ v, ((RadialWalk.average step)^[n]) q v = lambda ^ n * q v := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [Function.iterate_succ_apply']
    have hi : ((RadialWalk.average step)^[n]) q = fun w => lambda ^ n * q w := funext ih
    rw [hi, RadialWalk.average_mul, hq, pow_succ]
    ring

theorem ising_walk_lower_bound {d : ℕ} (hd : 3 ≤ d) {theta : ℝ}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (n : ℕ)
    (o : TreeVertex d) (ho : o.1.length = 0) :
    eigenRate ((d : ℝ) - 1) theta ^ n *
        (theta - conjugateRoot ((d : ℝ) - 1) theta) ≤
      (eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta) *
        ((RadialWalk.average treeStep)^[n]) (fun v : TreeVertex d => theta ^ v.1.length) o := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hle := RadialWalk.iterate_average_mono treeStep
    (fun v : TreeVertex d => eigenWeight_le hb ht ht1 v.1.length) n o
  have he := iterate_eigenfunction treeStep (treeEigenWeight d theta)
    (eigenRate ((d : ℝ) - 1) theta) (average_treeEigenWeight hd ht) n o
  change ((RadialWalk.average treeStep)^[n]) (treeEigenWeight d theta) o ≤ _ at hle
  rw [he, RadialWalk.iterate_average_mul] at hle
  simpa only [treeEigenWeight, ho, eigenWeight_zero] using hle

theorem le_of_exponential_bound {a b delta K : ℝ} (hb : 0 < b) (hd : 0 < delta)
    (h : ∀ n : ℕ, a ^ n * delta ≤ K * b ^ n) : a ≤ b := by
  have hq : a / b ≤ 1 := le_one_of_pow_le_affine (a := K / delta) (c := 0) (by
    intro n
    simp only [zero_mul, add_zero, div_pow]
    apply (div_le_iff₀ (pow_pos hb n)).2
    calc
      a ^ n ≤ (K * b ^ n) / delta := (le_div_iff₀ hd).2 (h n)
      _ = K / delta * b ^ n := by ring)
  exact (div_le_one hb).mp hq

theorem threshold_of_ising_walk_bound {d : ℕ} (hd : 3 ≤ d) {theta : ℝ}
    (ht1 : theta ≤ 1) (o : TreeVertex d) (ho : o.1.length = 0)
    (C : ℝ)
    (hbound : ∀ n : ℕ,
      ((RadialWalk.average treeStep)^[n]) (fun v : TreeVertex d => theta ^ v.1.length) o ≤
        C * RadialWalk.rate d ^ n) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  by_contra hnot
  have hcritical : 1 / Real.sqrt ((d : ℝ) - 1) < theta := lt_of_not_ge hnot
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hb
  have ht : 0 < theta := (one_div_pos.mpr hs).trans hcritical
  have hr : conjugateRoot ((d : ℝ) - 1) theta < theta :=
    conjugateRoot_lt hb ht (critical_square_lt hb hcritical)
  have hdelta : 0 < theta - conjugateRoot ((d : ℝ) - 1) theta := sub_pos.mpr hr
  have hA : 0 < eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta := by
    have := theta_le_eigenRate hb ht ht1
    linarith
  have hrho : 0 < RadialWalk.rate d := by
    unfold RadialWalk.rate
    positivity
  have hlarge : RadialWalk.rate d < eigenRate ((d : ℝ) - 1) theta := by
    simpa only [RadialWalk.rate, sub_add_cancel] using eigenRate_gt_critical hb hcritical
  apply (not_le_of_gt hlarge)
  apply le_of_exponential_bound hrho hdelta
    (K := (eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta) * C)
  intro n
  calc
    eigenRate ((d : ℝ) - 1) theta ^ n *
        (theta - conjugateRoot ((d : ℝ) - 1) theta) ≤
        (eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta) *
          ((RadialWalk.average treeStep)^[n])
            (fun v : TreeVertex d => theta ^ v.1.length) o :=
      ising_walk_lower_bound hd ht ht1 n o ho
    _ ≤ (eigenRate ((d : ℝ) - 1) theta - conjugateRoot ((d : ℝ) - 1) theta) *
        (C * RadialWalk.rate d ^ n) := mul_le_mul_of_nonneg_left (hbound n) hA.le
    _ = _ := by ring

theorem threshold_of_operatorAverage_norm {d : ℕ} (hd : 3 ≤ d) {theta : ℝ}
    (ht1 : theta ≤ 1) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : Fin d → H →L[ℝ] H) (hS : ∀ c, S c * S c = 1) (x : H)
    (hnorm : ‖RadialWalk.operatorAverage S‖ ≤ RadialWalk.rate d)
    (hcov : ∀ v : TreeVertex d,
      inner ℝ x (RadialWalk.wordOperator S v x) = theta ^ v.1.length) :
    theta ≤ 1 / Real.sqrt ((d : ℝ) - 1) := by
  let o : TreeVertex d := ⟨[], List.IsChain.nil⟩
  have hxx : inner ℝ x x = 1 := by
    simpa [RadialWalk.wordOperator, o] using hcov o
  have hx0 : x ≠ 0 := by
    intro hx
    simp [hx] at hxx
  let : Nontrivial H := ⟨⟨x, 0, hx0⟩⟩
  apply threshold_of_ising_walk_bound hd ht1 o rfl (‖x‖ ^ 2)
  intro n
  have hi := congrFun (RadialWalk.inner_iterate_vectorAverage treeStep x
    (fun v => RadialWalk.wordOperator S v x) n) o
  rw [RadialWalk.iterate_vectorAverage_wordOperator S hS] at hi
  have hc : (fun v : TreeVertex d => inner ℝ x (RadialWalk.wordOperator S v x)) =
      (fun v : TreeVertex d => theta ^ v.1.length) := funext hcov
  rw [hc] at hi
  simp only [RadialWalk.wordOperator, o, List.map_nil, List.prod_nil,
    one_apply_eq_self] at hi
  rw [← hi]
  calc
    inner ℝ x ((RadialWalk.operatorAverage S ^ n) x) ≤
        ‖x‖ * ‖(RadialWalk.operatorAverage S ^ n) x‖ := real_inner_le_norm _ _
    _ ≤ ‖x‖ * (‖RadialWalk.operatorAverage S ^ n‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖x‖ * (‖RadialWalk.operatorAverage S‖ ^ n * ‖x‖) := by
      gcongr
      exact norm_pow_le _ _
    _ ≤ ‖x‖ * (RadialWalk.rate d ^ n * ‖x‖) := by
      gcongr
    _ = ‖x‖ ^ 2 * RadialWalk.rate d ^ n := by ring

end IsingWalk
end Problem367

end

end OAI
