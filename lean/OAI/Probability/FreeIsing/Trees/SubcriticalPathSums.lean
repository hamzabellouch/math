import OAI.Probability.FreeIsing.Critical.Comparison
import OAI.Probability.FreeIsing.Trees.CoupledPathDrift
import OAI.Probability.FreeIsing.Trees.Shells

namespace OAI

noncomputable section

open MeasureTheory Set

namespace Problem367

def regularPathWeight (d : ℕ) (theta : ℝ) (n : ℕ) : ℝ :=
  (Fintype.card (TreeShell d (n + 1)) : ℝ) * theta ^ (2 * (n + 1))

theorem regularPathWeight_eq (d : ℕ) (theta : ℝ) (n : ℕ) :
    regularPathWeight d theta n =
      (d : ℝ) * theta ^ 2 * (((d - 1 : ℕ) : ℝ) * theta ^ 2) ^ n := by
  simp only [regularPathWeight, card_treeShell_succ, Nat.cast_mul, Nat.cast_pow]
  rw [pow_mul, pow_succ, mul_pow]
  ring

theorem regularPathWeight_nonneg (d : ℕ) (theta : ℝ) (n : ℕ) :
    0 ≤ regularPathWeight d theta n := by
  rw [regularPathWeight_eq]
  positivity

theorem summable_regularPathWeight_mul_length_sq
    {d : ℕ} {theta : ℝ}
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) :
    Summable (fun n => regularPathWeight d theta n * ((n + 1 : ℕ) : ℝ) ^ 2) := by
  let q : ℝ := ((d - 1 : ℕ) : ℝ) * theta ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hq : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hsub
  have h0 := summable_pow_mul_geometric_of_norm_lt_one 0 hq
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 hq
  have hs : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ 2 * q ^ n) := by
    convert! (h2.add (h1.mul_left 2)).add h0 using 1
    funext n
    simp only [Nat.cast_add, Nat.cast_one, pow_one, pow_zero, one_mul]
    ring
  convert! hs.mul_left ((d : ℝ) * theta ^ 2) using 1
  funext n
  rw [regularPathWeight_eq]
  dsimp only [q]
  ring

def subcriticalPathConstant (d : ℕ) (theta C : ℝ) : ℝ :=
  2 + (3 * C + 6) * ∑' n : ℕ, regularPathWeight d theta n * ((n + 1 : ℕ) : ℝ) ^ 2

theorem subcriticalPathConstant_nonneg (d : ℕ) (theta : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ subcriticalPathConstant d theta C := by
  unfold subcriticalPathConstant
  have hs : 0 ≤ ∑' n : ℕ, regularPathWeight d theta n * ((n + 1 : ℕ) : ℝ) ^ 2 :=
    tsum_nonneg (fun n => mul_nonneg (regularPathWeight_nonneg d theta n) (sq_nonneg _))
  positivity

theorem path_noise_drift_le_length_sq
    {Q L V C : ℝ} (n : ℕ) (hQ : 0 ≤ Q) (_hL : 0 ≤ L) (hV : 0 ≤ V)
    (hQbound : Q ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2 * V) (hLbound : L ≤ V) :
    Q + 2 * L + 4 * Real.sqrt (2 * V) * Real.sqrt Q ≤
      (3 * C + 6) * ((n + 1 : ℕ) : ℝ) ^ 2 * V := by
  have hr : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hVr : V ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * V := by
    have hr2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    simpa using mul_le_mul_of_nonneg_right hr2 hV
  have hsV := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hV)
  have hsQ := Real.sq_sqrt hQ
  have hcross := sq_nonneg (Real.sqrt (2 * V) - Real.sqrt Q)
  nlinarith

theorem subcritical_noise_drift_bound
    {d : ℕ} {theta C V D : ℝ} {Q L : ℕ → ℝ}
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1)
    (_hC : 0 ≤ C) (hV : 0 ≤ V)
    (hQ : ∀ n, 0 ≤ Q n) (hL : ∀ n, 0 ≤ L n)
    (hQbound : ∀ n, Q n ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2 * V)
    (hLbound : ∀ n, L n ≤ V)
    (hD : D ≤ 2 * V + ∑' n : ℕ, regularPathWeight d theta n *
      (Q n + 2 * L n + 4 * Real.sqrt (2 * V) * Real.sqrt (Q n))) :
    Summable (fun n : ℕ => regularPathWeight d theta n *
      (Q n + 2 * L n + 4 * Real.sqrt (2 * V) * Real.sqrt (Q n))) ∧
      D ≤ subcriticalPathConstant d theta C * V := by
  let f := fun n : ℕ => regularPathWeight d theta n *
    (Q n + 2 * L n + 4 * Real.sqrt (2 * V) * Real.sqrt (Q n))
  let g := fun n : ℕ => ((3 * C + 6) * V) *
    (regularPathWeight d theta n * ((n + 1 : ℕ) : ℝ) ^ 2)
  have hf0 (n : ℕ) : 0 ≤ f n := by
    dsimp [f]
    exact mul_nonneg (regularPathWeight_nonneg d theta n)
      (add_nonneg (add_nonneg (hQ n) (mul_nonneg (by norm_num) (hL n))) (by positivity))
  have hfg (n : ℕ) : f n ≤ g n := by
    have h := mul_le_mul_of_nonneg_left
      (path_noise_drift_le_length_sq n (hQ n) (hL n) hV (hQbound n) (hLbound n))
      (regularPathWeight_nonneg d theta n)
    calc
      f n ≤ regularPathWeight d theta n *
          ((3 * C + 6) * ((n + 1 : ℕ) : ℝ) ^ 2 * V) := h
      _ = g n := by dsimp only [g]; ring
  have hg : Summable g :=
    (summable_regularPathWeight_mul_length_sq hsub).mul_left ((3 * C + 6) * V)
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hfg hg
  refine ⟨hf, hD.trans ?_⟩
  calc
    2 * V + ∑' n : ℕ, f n ≤ 2 * V + ∑' n : ℕ, g n :=
      add_le_add le_rfl (hf.tsum_le_tsum hfg hg)
    _ = subcriticalPathConstant d theta C * V := by
      dsimp only [g, subcriticalPathConstant]
      rw [tsum_mul_left]
      ring

theorem eq_zero_of_subcritical_path_estimates
    {d : ℕ} {theta C T : ℝ} {V : ℝ → ℝ} {Q L : ℝ → ℕ → ℝ}
    (hsub : ((d - 1 : ℕ) : ℝ) * theta ^ 2 < 1) (hC : 0 ≤ C)
    (hV : AbsolutelyContinuousOnInterval V 0 T) (hzero : V 0 = 0)
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ V t)
    (hQ : ∀ t ∈ Icc 0 T, ∀ n, 0 ≤ Q t n)
    (hL : ∀ t ∈ Icc 0 T, ∀ n, 0 ≤ L t n)
    (hQbound : ∀ t ∈ Icc 0 T, ∀ n,
      Q t n ≤ C * ((n + 1 : ℕ) : ℝ) ^ 2 * V t)
    (hLbound : ∀ t ∈ Icc 0 T, ∀ n, L t n ≤ V t)
    (hderiv : ∀ᵐ t : ℝ, t ∈ Icc 0 T →
      deriv V t ≤ 2 * V t + ∑' n : ℕ, regularPathWeight d theta n *
        (Q t n + 2 * L t n + 4 * Real.sqrt (2 * V t) * Real.sqrt (Q t n))) :
    ∀ t ∈ Icc 0 T, V t = 0 := by
  apply eq_zero_of_ae_deriv_le_mul_self
    (C := subcriticalPathConstant d theta C) hV hzero hnonneg
  filter_upwards [hderiv] with t ht hmem
  exact (subcritical_noise_drift_bound hsub hC (hnonneg t hmem)
    (hQ t hmem) (hL t hmem) (hQbound t hmem) (hLbound t hmem) (ht hmem)).2

end Problem367

end

end OAI
