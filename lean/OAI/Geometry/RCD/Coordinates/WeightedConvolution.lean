import OAI.Geometry.RCD.Coordinates.PositiveForms
import Mathlib.Analysis.SpecificLimits.Normed

namespace OAI

/-! # Finite weighted convolution estimates for changing inverse metrics -/

open scoped BigOperators InnerProductSpace

namespace RegularPointCoordinates

/-- A positive quadratic form of a finite sum is bounded by the number of
terms times their total energy. Degeneracy of the form is allowed. -/
theorem positive_form_sum_le_card {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (D : E →L[ℝ] E) (hD : D.IsPositive)
    (s : Finset ι) (v : ι → E) :
    ⟪∑ j ∈ s, v j, D (∑ j ∈ s, v j)⟫_ℝ ≤
      (s.card : ℝ) * ∑ j ∈ s, ⟪v j, D (v j)⟫_ℝ := by
  have hcross (x y : E) : ⟪x, D y⟫_ℝ ≤ (⟪x, D x⟫_ℝ + ⟪y, D y⟫_ℝ) / 2 := by
    have hp := hD.inner_nonneg_right (x - y)
    have hs : ⟪y, D x⟫_ℝ = ⟪x, D y⟫_ℝ := by
      rw [real_inner_comm, hD.inner_left_eq_inner_right]
    simp only [map_sub, inner_sub_left, inner_sub_right, hs] at hp
    linarith
  calc
    _ = ∑ j ∈ s, ∑ l ∈ s, ⟪v j, D (v l)⟫_ℝ := by
      simp only [map_sum, sum_inner, inner_sum]
      rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ s, ∑ l ∈ s, (⟪v j, D (v j)⟫_ℝ + ⟪v l, D (v l)⟫_ℝ) / 2 := by
      exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun l _ => hcross (v j) (v l)
    _ = _ := by
      simp only [add_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      simp only [← Finset.mul_sum, ← Finset.sum_div]
      ring

/-- Reindex the lower triangle by the lag and initial index, then enlarge
to the full square. -/
theorem triangular_sum_le_square (k : ℕ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ m j, 0 ≤ f m j) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1), f (i - j) j) ≤
      ∑ m ∈ Finset.range k, ∑ j ∈ Finset.range k, f m j := by
  classical
  let s := (Finset.range k).sigma (fun i => Finset.range (i + 1))
  let t := (Finset.range k) ×ˢ (Finset.range k)
  let g : (Σ _ : ℕ, ℕ) → ℕ × ℕ := fun p => (p.1 - p.2, p.2)
  have hg : Set.InjOn g s := by
    intro p hp q hq heq
    have hp' := Finset.mem_sigma.mp hp
    have hq' := Finset.mem_sigma.mp hq
    have hpj : p.2 ≤ p.1 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hp'.2
    have hqj : q.2 ≤ q.1 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hq'.2
    have heq1 := congrArg Prod.fst heq
    have heq2 := congrArg Prod.snd heq
    simp only [g] at heq1 heq2
    have hfirst : p.1 = q.1 := by omega
    cases p
    cases q
    simp_all
  have hsub : s.image g ⊆ t := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqi, hqj⟩ := Finset.mem_sigma.mp hq
    simp only [Finset.mem_range] at hqi hqj
    simp only [t, g, Finset.mem_product, Finset.mem_range]
    omega
  calc
    _ = ∑ p ∈ s, f (g p).1 (g p).2 := by simp only [s, g, Finset.sum_sigma']
    _ = ∑ p ∈ s.image g, f p.1 p.2 := by rw [Finset.sum_image hg]
    _ ≤ ∑ p ∈ t, f p.1 p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hf p.1 p.2)
    _ = _ := by simp only [t, Finset.sum_product]

/-- Each location belongs to at most `m` forward intervals of length `m`. -/
theorem sliding_interval_sum_le (k m : ℕ) (b : ℕ → ℝ) (hb : ∀ l, 0 ≤ b l) :
    (∑ j ∈ Finset.range k, ∑ l ∈ Finset.Ico j (min k (j + m)), b l) ≤
      (m : ℝ) * ∑ l ∈ Finset.range k, b l := by
  classical
  have hset (j : ℕ) : Finset.Ico j (min k (j + m)) =
      (Finset.range k).filter (fun l => j ≤ l ∧ l < j + m) := by
    ext l
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range, lt_min_iff]
    omega
  have hcount (l : ℕ) :
      (((Finset.range k).filter (fun j => j ≤ l ∧ l < j + m)).card : ℝ) ≤ m := by
    have hs : (Finset.range k).filter (fun j => j ≤ l ∧ l < j + m) ⊆
        Finset.Ico (l + 1 - m) (l + 1) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      simp only [Finset.mem_Ico]
      omega
    have hc := Finset.card_le_card hs
    have hc' : (Finset.Ico (l + 1 - m) (l + 1)).card ≤ m := by
      rw [Nat.card_Ico]
      omega
    exact_mod_cast hc.trans hc'
  calc
    _ = ∑ j ∈ Finset.range k, ∑ l ∈ Finset.range k,
        if j ≤ l ∧ l < j + m then b l else 0 := by
      simp only [hset, Finset.sum_filter]
    _ = ∑ l ∈ Finset.range k, ∑ j ∈ Finset.range k,
        if j ≤ l ∧ l < j + m then b l else 0 := Finset.sum_comm
    _ = ∑ l ∈ Finset.range k,
        (((Finset.range k).filter (fun j => j ≤ l ∧ l < j + m)).card : ℝ) * b l := by
      congr 1
      ext l
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ l ∈ Finset.range k, (m : ℝ) * b l :=
      Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_right (hcount l) (hb l)
    _ = _ := by rw [Finset.mul_sum]

/-- The interval-convolution coefficient is the first moment of the lag
kernel; no dependence on the final index remains. -/
theorem weighted_interval_convolution_le (k : ℕ) (w b : ℕ → ℝ)
    (hw : ∀ m, 0 ≤ w m) (hb : ∀ l, 0 ≤ b l) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1),
      w (i - j) * ∑ l ∈ Finset.Ico j i, b l) ≤
      (∑ m ∈ Finset.range k, (m : ℝ) * w m) * ∑ l ∈ Finset.range k, b l := by
  have heq : (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1),
      w (i - j) * ∑ l ∈ Finset.Ico j i, b l) =
      ∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1),
        w (i - j) * ∑ l ∈ Finset.Ico j (min k (j + (i - j))), b l := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hij : j ≤ i := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    have hi' : i < k := Finset.mem_range.mp hi
    rw [Nat.add_sub_of_le hij, min_eq_right hi'.le]
  rw [heq]
  calc
    _ ≤ ∑ m ∈ Finset.range k, ∑ j ∈ Finset.range k,
        w m * ∑ l ∈ Finset.Ico j (min k (j + m)), b l :=
      triangular_sum_le_square k _ (fun m j => mul_nonneg (hw m)
        (Finset.sum_nonneg fun l _ => hb l))
    _ = ∑ m ∈ Finset.range k,
        w m * (∑ j ∈ Finset.range k, ∑ l ∈ Finset.Ico j (min k (j + m)), b l) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ m ∈ Finset.range k, w m * ((m : ℝ) * ∑ l ∈ Finset.range k, b l) :=
      Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (sliding_interval_sum_le k m b hb) (hw m)
    _ = _ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro m _; ring

/-- The stationary part of the triangular convolution has its ordinary
geometric-series coefficient. -/
theorem weighted_stationary_convolution_le (k : ℕ) (w b : ℕ → ℝ)
    (hw : ∀ m, 0 ≤ w m) (hb : ∀ j, 0 ≤ b j) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1), w (i - j) * b j) ≤
      (∑ m ∈ Finset.range k, w m) * ∑ j ∈ Finset.range k, b j := by
  calc
    _ ≤ ∑ m ∈ Finset.range k, ∑ j ∈ Finset.range k, w m * b j :=
      triangular_sum_le_square k _ (fun m j => mul_nonneg (hw m) (hb j))
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]; rw [Finset.sum_comm]

/-- The constant controlling intervals with exponentially decaying lags. -/
noncomputable def geometricIntervalConstant (rho : ℝ) : ℝ :=
  ∑' m : ℕ, (m : ℝ) ^ 2 * rho ^ m

theorem geometricIntervalConstant_nonneg {rho : ℝ} (hrho : 0 ≤ rho) :
    0 ≤ geometricIntervalConstant rho :=
  tsum_nonneg (fun m => mul_nonneg (sq_nonneg _) (pow_nonneg hrho m))

theorem weighted_geometric_interval_convolution_le (k : ℕ) (b : ℕ → ℝ)
    (hb : ∀ l, 0 ≤ b l) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1),
      ((i - j : ℕ) : ℝ) * rho ^ (i - j) * ∑ l ∈ Finset.Ico j i, b l) ≤
      geometricIntervalConstant rho * ∑ l ∈ Finset.range k, b l := by
  have hs : Summable (fun m : ℕ => (m : ℝ) ^ 2 * rho ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by simpa [abs_of_nonneg hrho] using hrho1)
  have hsum : (∑ m ∈ Finset.range k, (m : ℝ) * ((m : ℝ) * rho ^ m)) ≤
      geometricIntervalConstant rho := by
    simpa only [geometricIntervalConstant, pow_two, mul_assoc] using
      hs.sum_le_tsum (Finset.range k) (fun m _ => mul_nonneg (sq_nonneg _) (pow_nonneg hrho m))
  exact (weighted_interval_convolution_le k (fun m => (m : ℝ) * rho ^ m) b
    (fun m => by positivity) hb).trans
      (mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg fun l _ => hb l))

theorem weighted_geometric_stationary_convolution_le (k : ℕ) (b : ℕ → ℝ)
    (hb : ∀ l, 0 ≤ b l) {rho : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) :
    (∑ i ∈ Finset.range k, ∑ j ∈ Finset.range (i + 1), rho ^ (i - j) * b j) ≤
      (1 - rho)⁻¹ * ∑ l ∈ Finset.range k, b l := by
  have hs : Summable (fun m : ℕ => rho ^ m) :=
    summable_geometric_of_abs_lt_one (by simpa [abs_of_nonneg hrho] using hrho1)
  have hsum : (∑ m ∈ Finset.range k, rho ^ m) ≤ (1 - rho)⁻¹ := by
    have h := hs.sum_le_tsum (Finset.range k) (fun m _ => pow_nonneg hrho m)
    rwa [tsum_geometric_of_norm_lt_one (by simpa [abs_of_nonneg hrho] using hrho1)] at h
  exact (weighted_stationary_convolution_le k (fun m => rho ^ m) b
    (fun m => pow_nonneg hrho m) hb).trans
      (mul_le_mul_of_nonneg_right hsum (Finset.sum_nonneg fun l _ => hb l))

end RegularPointCoordinates

end OAI
