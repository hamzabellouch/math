import OAI.Probability.FreeIsing.Trees.Regularity

namespace OAI

noncomputable section

namespace Problem367
namespace RadialWalk

variable {V : Type*} {d : ℕ}

def average (step : V → Fin d → V) (f : V → ℝ) (v : V) : ℝ :=
  (∑ c : Fin d, f (step v c)) / d

theorem average_mono (step : V → Fin d → V) {f g : V → ℝ}
    (h : ∀ v, f v ≤ g v) : ∀ v, average step f v ≤ average step g v := by
  intro v
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun c _ => h (step v c)))
    (Nat.cast_nonneg d)

theorem average_mul (step : V → Fin d → V) (a : ℝ) (f : V → ℝ) (v : V) :
    average step (fun w => a * f w) v = a * average step f v := by
  unfold average
  rw [← Finset.mul_sum]
  ring

theorem iterate_bound (step : V → Fin d → V) (q : V → ℝ)
    {rho : ℝ} (hrho : 0 ≤ rho) (hq : ∀ v, average step q v ≤ rho * q v)
    (n : ℕ) : ∀ v, ((average step)^[n]) q v ≤ rho ^ n * q v := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [Function.iterate_succ_apply']
    calc
      average step (((average step)^[n]) q) v ≤
          average step (fun w => rho ^ n * q w) v := average_mono step ih v
      _ = rho ^ n * average step q v := average_mul step _ _ _
      _ ≤ rho ^ n * (rho * q v) := mul_le_mul_of_nonneg_left (hq v) (pow_nonneg hrho n)
      _ = rho ^ (n + 1) * q v := by rw [pow_succ]; ring

theorem average_nonneg (step : V → Fin d → V) {f : V → ℝ}
    (hf : ∀ v, 0 ≤ f v) : ∀ v, 0 ≤ average step f v := by
  intro v
  exact div_nonneg (Finset.sum_nonneg (fun c _ => hf (step v c))) (Nat.cast_nonneg d)

theorem abs_average_le (step : V → Fin d → V) (f : V → ℝ) (v : V) :
    |average step f v| ≤ average step (fun w => |f w|) v := by
  unfold average
  rw [abs_div, show |(d : ℝ)| = d from abs_of_nonneg (Nat.cast_nonneg d)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg d)

theorem abs_iterate_average_le (step : V → Fin d → V) (f : V → ℝ) (n : ℕ) :
    ∀ v, |((average step)^[n]) f v| ≤
      ((average step)^[n]) (fun w => |f w|) v := by
  induction n with
  | zero => intro v; simp
  | succ n ih =>
    intro v
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (abs_average_le _ _ _).trans (average_mono step ih v)

theorem iterate_average_mono (step : V → Fin d → V) {f g : V → ℝ}
    (h : ∀ v, f v ≤ g v) (n : ℕ) :
    ∀ v, ((average step)^[n]) f v ≤ ((average step)^[n]) g v := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [Function.iterate_succ_apply']
    exact average_mono step ih

theorem iterate_average_mul (step : V → Fin d → V) (a : ℝ) (f : V → ℝ) (n : ℕ) :
    ((average step)^[n]) (fun w => a * f w) =
      fun v => a * ((average step)^[n]) f v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext v
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    exact average_mul step _ _ _

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def vectorAverage (step : V → Fin d → V) (f : V → H) (v : V) : H :=
  (d : ℝ)⁻¹ • ∑ c : Fin d, f (step v c)

theorem inner_vectorAverage (step : V → Fin d → V) (x : H) (f : V → H) (v : V) :
    inner ℝ x (vectorAverage step f v) = average step (fun w => inner ℝ x (f w)) v := by
  simp only [vectorAverage, inner_smul_right, inner_sum, average]
  ring

theorem inner_iterate_vectorAverage (step : V → Fin d → V) (x : H) (f : V → H)
    (n : ℕ) :
    (fun v => inner ℝ x (((vectorAverage step)^[n]) f v)) =
      ((average step)^[n]) (fun v => inner ℝ x (f v)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext v
    rw [Function.iterate_succ_apply', inner_vectorAverage, ih,
      Function.iterate_succ_apply']

theorem inner_iterate_bound (step : V → Fin d → V) (x : H) (f : V → H)
    (q : V → ℝ) {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (hq : ∀ v, average step q v ≤ rho * q v)
    (hf : ∀ v, |inner ℝ x (f v)| ≤ C * q v)
    (n : ℕ) (v : V) :
    |inner ℝ x (((vectorAverage step)^[n]) f v)| ≤ C * rho ^ n * q v := by
  have hinner := congrFun (inner_iterate_vectorAverage step x f n) v
  rw [hinner]
  calc
    |((average step)^[n]) (fun w => inner ℝ x (f w)) v| ≤
        ((average step)^[n]) (fun w => |inner ℝ x (f w)|) v :=
      abs_iterate_average_le step _ n v
    _ ≤ ((average step)^[n]) (fun w => C * q w) v := iterate_average_mono step hf n v
    _ = C * ((average step)^[n]) q v := congrFun (iterate_average_mul step C q n) v
    _ ≤ C * (rho ^ n * q v) := mul_le_mul_of_nonneg_left (iterate_bound step q hrho hq n v) hC
    _ = C * rho ^ n * q v := by ring

def weight (d : ℕ) (n : ℕ) : ℝ :=
  (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ n

def rate (d : ℕ) : ℝ := 2 * Real.sqrt ((d : ℝ) - 1) / d

theorem rate_nonneg (d : ℕ) : 0 ≤ rate d := by
  exact div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (Nat.cast_nonneg d)

theorem rate_lt_one {d : ℕ} (hd : 3 ≤ d) : rate d < 1 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 ≤ (d : ℝ) - 1 := by linarith
  have hs := Real.sq_sqrt hb
  have hs0 := Real.sqrt_nonneg ((d : ℝ) - 1)
  unfold rate
  apply (div_lt_one (by positivity : (0 : ℝ) < d)).2
  nlinarith [sq_nonneg ((d : ℝ) - 2)]

theorem root_bound {d : ℕ} (hd : 3 ≤ d) : weight d 1 ≤ rate d * weight d 0 := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr hb
  have hs2 := Real.sq_sqrt hb.le
  simp only [weight, rate, pow_one, pow_zero, mul_one]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hs (by positivity : (0 : ℝ) < d)).2
  nlinarith

theorem recurrence {d : ℕ} (hd : 3 ≤ d) (n : ℕ) :
    (weight d n + ((d : ℝ) - 1) * weight d (n + 2)) / d =
      rate d * weight d (n + 1) := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hb : 0 < (d : ℝ) - 1 := by linarith
  have hs : Real.sqrt ((d : ℝ) - 1) ≠ 0 := (Real.sqrt_pos.mpr hb).ne'
  have hs2 := Real.sq_sqrt hb.le
  unfold weight rate
  simp only [pow_succ]
  field_simp
  nlinarith

def treeWeight (d : ℕ) (v : TreeVertex d) : ℝ := weight d v.1.length

theorem average_treeWeight_le {d : ℕ} (hd : 3 ≤ d) (v : TreeVertex d) :
    average treeStep (treeWeight d) v ≤ rate d * treeWeight d v := by
  classical
  have hsum := sum_treeNeighborFinset_radial v (weight d)
  rw [treeNeighborFinset, Finset.sum_image (treeStep_injective v).injOn] at hsum
  unfold average treeWeight
  rw [hsum]
  by_cases hv : v.1.length = 0
  · rw [ite_eq_left hv, hv]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have hcancel : (d : ℝ) * weight d 1 / d = weight d 1 := by field_simp
    rw [hcancel]
    exact root_bound hd
  · rw [ite_eq_right hv]
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hv
    rw [hn]
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using (recurrence hd n).le

theorem iterate_treeWeight_le {d : ℕ} (hd : 3 ≤ d) (n : ℕ) (v : TreeVertex d) :
    ((average treeStep)^[n]) (treeWeight d) v ≤ rate d ^ n * treeWeight d v :=
  iterate_bound treeStep (treeWeight d) (rate_nonneg d) (average_treeWeight_le hd) n v

theorem covariance_walk_bound {d : ℕ} (hd : 3 ≤ d) (f : TreeVertex d → H)
    (o : TreeVertex d) (ho : o.1.length = 0) {C : ℝ} (hC : 0 ≤ C)
    (hcov : ∀ v, |inner ℝ (f o) (f v)| ≤ C * treeWeight d v) (n : ℕ) :
    |inner ℝ (f o) (((vectorAverage treeStep)^[n]) f o)| ≤ C * rate d ^ n := by
  simpa only [treeWeight, ho, weight, pow_zero, mul_one] using
    inner_iterate_bound treeStep (f o) f (treeWeight d) hC (rate_nonneg d)
      (average_treeWeight_le hd) hcov n o

end RadialWalk
end Problem367

end

end OAI
