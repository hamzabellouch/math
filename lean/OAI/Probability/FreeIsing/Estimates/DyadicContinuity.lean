import OAI.Probability.FreeIsing.Estimates.ContinuousModification

namespace OAI

noncomputable section
open Filter
open scoped Topology NNReal

namespace Problem367.DyadicContinuity

theorem geometric_limit {T : Type*} (u : ℕ → T → ℝ) (s : Set T)
    {C r : ℝ} (_hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ n t, t ∈ s → dist (u n t) (u (n+1) t) ≤ C * r^n) :
    ∀ t ∈ s,
      Tendsto (fun n => u n t) atTop (𝓝 (limUnder atTop (fun n => u n t))) ∧
      ∀ n, dist (u n t) (limUnder atTop (fun m => u m t)) ≤
        C * r^n * (1-r)⁻¹ := by
  intro t ht
  have hs : Summable (fun n : ℕ => C * r^n) :=
    (summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1)).mul_left C
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable (fun n => C*r^n) (fun n => hstep n t ht) hs)
  have hlim : Tendsto (fun n => u n t) atTop
      (𝓝 (limUnder atTop (fun n => u n t))) := by rwa [ha.limUnder_eq]
  refine ⟨hlim, fun n => ?_⟩
  have h := dist_le_tsum_of_dist_le_of_tendsto (fun n => C*r^n)
    (fun n => hstep n t ht) hs hlim n
  calc
    dist (u n t) (limUnder atTop (fun m => u m t)) ≤ ∑' m : ℕ, C*r^(n+m) := h
    _ = C*r^n*(1-r)⁻¹ := by
      simp only [pow_add, ← mul_assoc]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hr hr1]

theorem continuousOn_geometric_limit {T : Type*} [PseudoMetricSpace T]
    (u : ℕ → T → ℝ) (s : Set T) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hstep : ∀ n t, t ∈ s → dist (u n t) (u (n+1) t) ≤ C*r^n)
    (hosc : ∀ n x, x ∈ s → ∃ δ > 0, ∀ y ∈ s,
      dist y x < δ → dist (u n y) (u n x) ≤ C*r^n) :
    ContinuousOn (fun t => limUnder atTop (fun n => u n t)) s := by
  apply Metric.continuousOn_iff.mpr
  intro x hx ε hε
  have he : Tendsto (fun n : ℕ => (2*C*(1-r)⁻¹+C)*r^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul
      (2*C*(1-r)⁻¹+C)
  obtain ⟨n, hn⟩ := (he.eventually_lt_const hε).exists
  obtain ⟨δ, hδ, hδbound⟩ := hosc n x hx
  refine ⟨δ, hδ, fun y hy hxy => ?_⟩
  have hxerr := (geometric_limit u s hC hr hr1 hstep x hx).2 n
  have hyerr := (geometric_limit u s hC hr hr1 hstep y hy).2 n
  have htri := dist_triangle4
    (limUnder atTop (fun n => u n y)) (u n y) (u n x)
    (limUnder atTop (fun n => u n x))
  rw [dist_comm (limUnder atTop (fun n => u n y)) (u n y)] at htri
  have hosc' := hδbound y hy hxy
  nlinarith

private theorem floor_double_cases (x : ℝ) :
    ⌊2*x⌋ = 2*⌊x⌋ ∨ ⌊2*x⌋ = 2*⌊x⌋+1 := by
  have hlo : 2*⌊x⌋ ≤ ⌊2*x⌋ := Int.le_floor.mpr (by
    have := Int.floor_le x
    push_cast
    linarith)
  have hhi : ⌊2*x⌋ < 2*⌊x⌋+2 := Int.floor_lt.mpr (by
    have := Int.lt_floor_add_one x
    push_cast
    linarith)
  omega

private theorem floor_near_cases {x y : ℝ} (h : |x-y| < 1) :
    ⌊x⌋ = ⌊y⌋ ∨ ⌊x⌋ = ⌊y⌋+1 ∨ ⌊y⌋ = ⌊x⌋+1 := by
  have hxy := (abs_lt.mp h)
  have h1 : ⌊x⌋ < ⌊y⌋+2 := Int.floor_lt.mpr (by
    have := Int.lt_floor_add_one y
    push_cast
    linarith)
  have h2 : ⌊y⌋ < ⌊x⌋+2 := Int.floor_lt.mpr (by
    have := Int.lt_floor_add_one x
    push_cast
    linarith)
  omega

open ContinuousModification

theorem dyadicLeft_refinement (t : ℝ) (n : ℕ) :
    dyadicLeft t (n+1) = dyadicLeft t n ∨
      dyadicLeft t (n+1) = dyadicLeft t n + ((2 : ℝ)^(n+1))⁻¹ := by
  have hp : (2 : ℝ)^n ≠ 0 := by positivity
  rcases floor_double_cases ((2 : ℝ)^n*t) with h | h
  · left
    unfold dyadicLeft
    rw [pow_succ]
    have he : (2 : ℝ)^n*2*t = 2*((2 : ℝ)^n*t) := by ring
    rw [he, h]
    push_cast
    field_simp
  · right
    unfold dyadicLeft
    rw [pow_succ]
    have he : (2 : ℝ)^n*2*t = 2*((2 : ℝ)^n*t) := by ring
    rw [he, h]
    push_cast
    field_simp

theorem dyadic_refinement_bound (f : ℝ → ℝ) {H B : ℝ} (hB : 0 ≤ B)
    (n : ℕ)
    (hinc : ∀ k : ℤ, 0 ≤ k → (k : ℝ)/(2:ℝ)^(n+1) ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^(n+1)))
        (f (((k:ℝ)+1)/(2:ℝ)^(n+1))) ≤ B)
    {t : ℝ} (ht : t ∈ Set.Icc 0 H) :
    dist (f (dyadicLeft t n)) (f (dyadicLeft t (n+1))) ≤ B := by
  rcases dyadicLeft_refinement t n with h | h
  · rw [h, dist_self]
    exact hB
  · let k : ℤ := 2*⌊(2:ℝ)^n*t⌋
    have hk : 0 ≤ k := by
      dsimp [k]
      exact mul_nonneg (by norm_num) (Int.floor_nonneg.mpr (mul_nonneg (by positivity) ht.1))
    have he : (k:ℝ)/(2:ℝ)^(n+1) = dyadicLeft t n := by
      dsimp [k, dyadicLeft]
      rw [pow_succ]
      push_cast
      field_simp
    have he' : ((k:ℝ)+1)/(2:ℝ)^(n+1) = dyadicLeft t (n+1) := by
      rw [h, ←he, add_div]
      simp [one_div]
    rw [←he, ←he']
    exact hinc k hk (he ▸ (dyadicLeft_le t n).trans ht.2)

theorem dyadic_oscillation_bound (f : ℝ → ℝ) {H B : ℝ} (hB : 0 ≤ B)
    (n : ℕ)
    (hinc : ∀ k : ℤ, 0 ≤ k → (k : ℝ)/(2:ℝ)^n ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ B)
    {x y : ℝ} (hx : x ∈ Set.Icc 0 H) (hy : y ∈ Set.Icc 0 H)
    (hxy : dist x y < ((2:ℝ)^n)⁻¹) :
    dist (f (dyadicLeft x n)) (f (dyadicLeft y n)) ≤ B := by
  have hp : (0:ℝ) < 2^n := by positivity
  have hclose : |(2:ℝ)^n*x-(2:ℝ)^n*y| < 1 := by
    rw [←mul_sub, abs_mul, abs_of_pos hp]
    have h := (mul_lt_mul_of_pos_left hxy hp)
    rw [Real.dist_eq, mul_inv_cancel₀ hp.ne'] at h
    exact h
  rcases floor_near_cases hclose with h | h | h
  · simp only [dyadicLeft, h, dist_self]
    exact hB
  · have hk := Int.floor_nonneg.mpr (mul_nonneg hp.le hy.1)
    have hb := hinc ⌊(2:ℝ)^n*y⌋ hk ((dyadicLeft_le y n).trans hy.2)
    simpa only [dyadicLeft, h, Int.cast_add, Int.cast_one, dist_comm] using hb
  · have hk := Int.floor_nonneg.mpr (mul_nonneg hp.le hx.1)
    have hb := hinc ⌊(2:ℝ)^n*x⌋ hk ((dyadicLeft_le x n).trans hx.2)
    simpa only [dyadicLeft, h, Int.cast_add, Int.cast_one] using hb

theorem continuousOn_dyadicLimit (f : ℝ → ℝ) {H C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ)
    (hinc : ∀ n ≥ N, ∀ k : ℤ, 0 ≤ k → (k:ℝ)/(2:ℝ)^n ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ C*r^n) :
    ContinuousOn (fun t => limUnder atTop (fun n => f (dyadicLeft t n)))
      (Set.Icc 0 H) := by
  let u : ℕ → ℝ → ℝ := fun n t => f (dyadicLeft t (n+N))
  have hD : 0 ≤ C*r^N := mul_nonneg hC (pow_nonneg hr _)
  have hstep : ∀ n t, t ∈ Set.Icc 0 H →
      dist (u n t) (u (n+1) t) ≤ (C*r^N)*r^n := by
    intro n t ht
    have hh := dyadic_refinement_bound f
      (mul_nonneg hC (pow_nonneg hr (n+N+1))) (n+N)
      (hinc (n+N+1) (by omega)) ht
    have hp : C*r^(n+N+1) ≤ C*r^(n+N) := by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (pow_nonneg hr _) hr1.le) hC
    have he : C*r^(n+N) = (C*r^N)*r^n := by rw [pow_add]; ring
    simpa only [u, show n+1+N=n+N+1 by omega, he] using hh.trans hp
  have hosc : ∀ n x, x ∈ Set.Icc 0 H → ∃ δ > 0, ∀ y ∈ Set.Icc 0 H,
      dist y x < δ → dist (u n y) (u n x) ≤ (C*r^N)*r^n := by
    intro n x hx
    refine ⟨((2:ℝ)^(n+N))⁻¹, by positivity, fun y hy hxy => ?_⟩
    have hh := dyadic_oscillation_bound f
      (mul_nonneg hC (pow_nonneg hr (n+N))) (n+N)
      (hinc (n+N) (by omega)) hy hx hxy
    have he : C*r^(n+N) = (C*r^N)*r^n := by rw [pow_add]; ring
    simpa only [u, he] using hh
  have hc := continuousOn_geometric_limit u (Set.Icc 0 H) hD hr hr1 hstep hosc
  apply hc.congr
  intro t ht
  have hshift := (geometric_limit u (Set.Icc 0 H) hD hr hr1 hstep t ht).1
  have hfull := (tendsto_add_atTop_iff_nat (f := fun n => f (dyadicLeft t n)) N).mp hshift
  exact hfull.limUnder_eq

theorem tendsto_dyadic_sample (f : ℝ → ℝ) {H C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1) (N : ℕ)
    (hinc : ∀ n ≥ N, ∀ k : ℤ, 0 ≤ k → (k:ℝ)/(2:ℝ)^n ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ C*r^n)
    {t : ℝ} (ht : t ∈ Set.Icc 0 H) :
    Tendsto (fun n => f (dyadicLeft t n)) atTop
      (𝓝 (limUnder atTop (fun n => f (dyadicLeft t n)))) := by
  have hs : Summable (fun n : ℕ => C*r^(n+N+1)) := by
    have hh : Summable (fun n : ℕ => r^n) :=
      summable_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs, abs_of_nonneg hr] using hr1)
    simpa [pow_add, mul_assoc, mul_left_comm, mul_comm] using hh.mul_left (C*r^(N+1))
  have hstep (n : ℕ) : dist (f (dyadicLeft t (n+N)))
      (f (dyadicLeft t ((n+1)+N))) ≤ C*r^(n+N+1) := by
    simpa only [show n+1+N=n+N+1 by omega] using
      dyadic_refinement_bound f (mul_nonneg hC (pow_nonneg hr _)) (n+N)
        (hinc (n+N+1) (by omega)) ht
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable _ hstep hs)
  have hfull := (tendsto_add_atTop_iff_nat (f := fun n => f (dyadicLeft t n)) N).mp ha
  rwa [hfull.limUnder_eq]

theorem dyadicLeft_grid (k : ℤ) (n m : ℕ) (hnm : n ≤ m) :
    dyadicLeft ((k:ℝ)/(2:ℝ)^n) m = (k:ℝ)/(2:ℝ)^n := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have hp : (2:ℝ)^n ≠ 0 := by positivity
  have he : (2:ℝ)^(n+l)*((k:ℝ)/(2:ℝ)^n) = ((2:ℤ)^l*k:ℤ) := by
    push_cast
    rw [pow_add]
    field_simp
  unfold dyadicLeft
  rw [he, Int.floor_intCast]
  push_cast
  rw [pow_add]
  field_simp

theorem dyadicLimit_grid (f : ℝ → ℝ) (k : ℤ) (n : ℕ) :
    limUnder atTop (fun m => f (dyadicLeft ((k:ℝ)/(2:ℝ)^n) m)) =
      f ((k:ℝ)/(2:ℝ)^n) := by
  have he : (fun m => f (dyadicLeft ((k:ℝ)/(2:ℝ)^n) m)) =ᶠ[atTop]
      (fun _ => f ((k:ℝ)/(2:ℝ)^n)) := by
    apply eventually_atTop.mpr
    exact ⟨n, fun m hm => by dsimp; rw [dyadicLeft_grid k n m hm]⟩
  exact ((tendsto_congr' he).mpr tendsto_const_nhds).limUnder_eq

theorem continuousOn_Ici_dyadicLimit (f : ℝ → ℝ) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hinc : ∀ H : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℤ,
      0 ≤ k → (k:ℝ)/(2:ℝ)^n ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ C*r^n) :
    ContinuousOn (fun t => limUnder atTop (fun n => f (dyadicLeft t n)))
      (Set.Ici 0) := by
  intro t ht
  obtain ⟨H, hH⟩ := exists_nat_gt t
  obtain ⟨N, hN⟩ := hinc H
  have hc := continuousOn_dyadicLimit f hC hr hr1 N hN
  apply (hc t (show t ∈ Set.Icc 0 (H:ℝ) from ⟨ht, hH.le⟩)).mono_of_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
  refine ⟨Set.Iio (H:ℝ), Iio_mem_nhds hH, ?_⟩
  intro x hx
  exact ⟨hx.2, hx.1.le⟩

theorem continuous_nnreal_dyadicLimit (f : ℝ → ℝ) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hinc : ∀ H : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℤ,
      0 ≤ k → (k:ℝ)/(2:ℝ)^n ≤ H →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ C*r^n) :
    Continuous (fun t : ℝ≥0 => limUnder atTop (fun n => f (dyadicLeft t n))) := by
  exact (continuousOn_Ici_dyadicLimit f hC hr hr1 hinc).comp_continuous
    continuous_subtype_val (fun t => t.property)

theorem continuous_nnreal_dyadicLimit_of_nat_grid (f : ℝ → ℝ) {C r : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hr1 : r < 1)
    (hinc : ∀ H : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, k < H*2^n →
      dist (f ((k:ℝ)/(2:ℝ)^n)) (f (((k:ℝ)+1)/(2:ℝ)^n)) ≤ C*r^n) :
    Continuous (fun t : ℝ≥0 => limUnder atTop (fun n => f (dyadicLeft t n))) := by
  apply continuous_nnreal_dyadicLimit f hC hr hr1
  intro H
  obtain ⟨N, hN⟩ := hinc (H+1)
  refine ⟨N, fun n hn k hk hkH => ?_⟩
  have hcast : (k.toNat:ℝ) = (k:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk
  have hkR : (k:ℝ) ≤ (H:ℝ)*(2:ℝ)^n :=
    (div_le_iff₀ (by positivity : (0:ℝ)<2^n)).mp hkH
  have hb : (k.toNat:ℝ) < ((H+1:ℕ):ℝ)*(2:ℝ)^n := by
    rw [hcast]
    have hp : (0:ℝ)<2^n := by positivity
    push_cast
    nlinarith
  have hbNat : k.toNat < (H+1)*2^n := by exact_mod_cast hb
  simpa only [hcast] using hN n hn k.toNat hbNat

end Problem367.DyadicContinuity

end

end OAI
