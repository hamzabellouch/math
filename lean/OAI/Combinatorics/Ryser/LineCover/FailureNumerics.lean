import OAI.Combinatorics.Ryser.LineCover.TailNumerics
import OAI.Combinatorics.Ryser.LineCover.SamplingNumerics
import OAI.Combinatorics.Ryser.LineCover.FiniteFailureNumerics

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.LineCover

open Filter Topology

def lowFailureEnvelope (D : ℕ) (δ A κ q : ℝ) : ℝ :=
  let h := 10 * (D + 1)
  let t := (logarithmicSampleSize A q : ℝ)
  (16 / δ) * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) +
    (16 * (t ^ 2 * q ^ (-(1 / 2 - κ / 4))) +
      32 * (t ^ 3 * q ^ (-(1 / 2 - κ / 4)))) +
    ((D : ℝ) * (8 * (D : ℝ)) ^ h) *
      (t ^ (2 * h) * q ^ (-((h : ℝ) * (1 / 2 - κ / 4) - D)))

def highFailureEnvelope (D : ℕ) (δ ρ A κ q : ℝ) : ℝ :=
  let h := 10 * (D + 1)
  let t := (logarithmicSampleSize A q : ℝ)
  (4 * ((D : ℝ) + 4) / (δ * ρ)) * q ^ (-(3 * κ / 20)) +
    (t ^ 2 * q ^ (-(1 / 2 + κ / 4)) +
      t ^ 3 * q ^ (-(1 / 2 + κ / 4))) +
    ((D : ℝ) * (4 * (D : ℝ)) ^ h) *
      (t ^ (2 * h) * q ^ (-((h : ℝ) * (1 / 2 + κ / 4) - D)))

theorem low_occupancy_decay_pos (D : ℕ) {κ : ℝ} (hκ : κ ≤ 1) :
    0 < ((10 * (D + 1) : ℕ) : ℝ) * (1 / 2 - κ / 4) - D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_nonneg (by positivity : 0 ≤ (D : ℝ) + 1)
    (sub_nonneg.mpr hκ)
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem high_occupancy_decay_pos (D : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    0 < ((10 * (D + 1) : ℕ) : ℝ) * (1 / 2 + κ / 4) - D := by
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hmul := mul_pos (by positivity : 0 < (D : ℝ) + 1) hκ
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
  nlinarith

theorem tendsto_lowFailureEnvelope_atTop (D : ℕ) (δ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hκone : κ ≤ 1) :
    Tendsto (lowFailureEnvelope D δ A κ) atTop (𝓝 0) := by
  have hfirst := (tendsto_rpow_neg_atTop
    (by positivity : 0 < 7 * κ / 30)).const_mul ((D : ℝ) + 4)
  have hsecond := tendsto_rpow_neg_atTop (by positivity : 0 < 3 * κ / 4)
  have hsurvivors := (hfirst.add hsecond).const_mul (16 / δ)
  have hdecay : 0 < (1 / 2 : ℝ) - κ / 4 := by linarith
  have hparallel := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 2 hA hdecay).const_mul
    (16 : ℝ)
  have hconcurrent := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 3 hA hdecay).const_mul
    (32 : ℝ)
  have hoccupancy := (tendsto_sampleSize_pow_mul_rpow_neg_atTop
    (2 * (10 * (D + 1))) hA (low_occupancy_decay_pos D hκone)).const_mul
      ((D : ℝ) * (8 * (D : ℝ)) ^ (10 * (D + 1)))
  unfold lowFailureEnvelope
  simpa only [mul_zero, add_zero] using
    (hsurvivors.add (hparallel.add hconcurrent)).add hoccupancy

theorem tendsto_highFailureEnvelope_atTop (D : ℕ) (δ ρ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) :
    Tendsto (highFailureEnvelope D δ ρ A κ) atTop (𝓝 0) := by
  have hsurvivors := (tendsto_rpow_neg_atTop
    (by positivity : 0 < 3 * κ / 20)).const_mul (4 * ((D : ℝ) + 4) / (δ * ρ))
  have hdecay : 0 < (1 / 2 : ℝ) + κ / 4 := by positivity
  have hgeometry := (tendsto_sampleSize_pow_mul_rpow_neg_atTop 2 hA hdecay).add
    (tendsto_sampleSize_pow_mul_rpow_neg_atTop 3 hA hdecay)
  have hoccupancy := (tendsto_sampleSize_pow_mul_rpow_neg_atTop
    (2 * (10 * (D + 1))) hA (high_occupancy_decay_pos D hκ)).const_mul
      ((D : ℝ) * (4 * (D : ℝ)) ^ (10 * (D + 1)))
  unfold highFailureEnvelope
  simpa only [mul_zero, add_zero] using
    (hsurvivors.add hgeometry).add hoccupancy

theorem eventually_lowFailureEnvelope_lt_one (D : ℕ) (δ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) (hκone : κ ≤ 1) :
    ∀ᶠ q : ℝ in atTop, lowFailureEnvelope D δ A κ q < 1 :=
  (tendsto_order.mp (tendsto_lowFailureEnvelope_atTop D δ hA hκ hκone)).2 1
    (by norm_num)

theorem eventually_highFailureEnvelope_lt_one (D : ℕ) (δ ρ : ℝ) {A κ : ℝ}
    (hA : 0 < A) (hκ : 0 < κ) :
    ∀ᶠ q : ℝ in atTop, highFailureEnvelope D δ ρ A κ q < 1 :=
  (tendsto_order.mp (tendsto_highFailureEnvelope_atTop D δ ρ hA hκ)).2 1
    (by norm_num)

theorem low_concurrency_ratio_le {q m R κ : ℝ} (hq : 0 < q)
    (hm : q / 2 ≤ m) (hR : R ≤ q ^ (1 / 2 + κ / 4)) :
    R / m ≤ 2 * q ^ (-(1 / 2 - κ / 4)) := by
  calc
    R / m ≤ q ^ (1 / 2 + κ / 4) / (q / 2) :=
      div_le_div₀ (Real.rpow_nonneg hq.le _) hR (by positivity) hm
    _ = 2 * (q ^ (1 / 2 + κ / 4) / q) := by
      field_simp [hq.ne']

    _ = 2 * q ^ (-(1 / 2 - κ / 4)) := by
      rw [← Real.rpow_sub_one hq.ne']
      congr 2
      ring

theorem high_concurrency_inverse_le {q R κ : ℝ} (hq : 0 < q)
    (hR : q ^ (1 / 2 + κ / 4) ≤ R) :
    1 / R ≤ q ^ (-(1 / 2 + κ / 4)) := by
  calc
    1 / R ≤ 1 / q ^ (1 / 2 + κ / 4) :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hq _) hR
    _ = q ^ (-(1 / 2 + κ / 4)) := by rw [Real.rpow_neg hq.le, one_div]

theorem sampling_occupancy_le_power (D h t : ℕ) {q K B C β : ℝ}
    (hq : 0 < q) (hK0 : 0 ≤ K) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hK : K ≤ (D : ℝ) * q ^ (D : ℝ))
    (hbase : B ≤ C * (t : ℝ) ^ 2 * q ^ (-β)) :
    K * B ^ h ≤ ((D : ℝ) * C ^ h) *
      ((t : ℝ) ^ (2 * h) * q ^ (-((h : ℝ) * β - D))) := by
  let _ := hK0
  let _ := hC
  have hp := pow_le_pow_left₀ hB hbase h
  have hjoin : q ^ (D : ℝ) * (q ^ (-β)) ^ h =
      q ^ (-((h : ℝ) * β - D)) := by
    rw [← Real.rpow_mul_natCast hq.le, ← Real.rpow_add hq]
    congr 1
    ring
  calc
    K * B ^ h ≤ ((D : ℝ) * q ^ (D : ℝ)) *
        (C * (t : ℝ) ^ 2 * q ^ (-β)) ^ h :=
      mul_le_mul hK hp (pow_nonneg hB _) (by positivity)
    _ = ((D : ℝ) * C ^ h) * (t : ℝ) ^ (2 * h) *
        (q ^ (D : ℝ) * (q ^ (-β)) ^ h) := by
      simp only [mul_pow, pow_mul]
      ring
    _ = _ := by rw [hjoin]; ring

theorem high_survivor_term_le {q E R N δ ρ κ : ℝ} (D : ℕ)
    (hq : 0 < q) (hδ : 0 < δ) (hρ : 0 < ρ) (hE0 : 0 ≤ E)
    (hE : E ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : q ^ (1 / 2 + κ / 4) ≤ R) (hN : ρ * q / 2 ≤ N) :
    2 * E / (δ * R * N) ≤
      (4 * ((D : ℝ) + 4) / (δ * ρ)) * q ^ (-(3 * κ / 20)) := by
  let _ := hE0
  have hR0 : 0 < R := lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hR
  have hN0 : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hden : δ * q ^ (1 / 2 + κ / 4) * (ρ * q / 2) ≤ δ * R * N :=
    mul_le_mul (mul_le_mul_of_nonneg_left hR hδ.le) hN (by positivity)
      (mul_nonneg hδ.le hR0.le)
  have hratio : q ^ (3 / 2 + κ / 10) /
      (q ^ (1 / 2 + κ / 4) * q) = q ^ (-(3 * κ / 20)) := by
    rw [← Real.rpow_add_one hq.ne', ← Real.rpow_sub hq]
    congr 1
    ring
  calc
    2 * E / (δ * R * N) ≤
        (2 * (((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))) /
          (δ * q ^ (1 / 2 + κ / 4) * (ρ * q / 2)) :=
      div_le_div₀ (by positivity) (by linarith) (by positivity) hden
    _ = (4 * ((D : ℝ) + 4) / (δ * ρ)) *
        (q ^ (3 / 2 + κ / 10) / (q ^ (1 / 2 + κ / 4) * q)) := by
      field_simp
      ring
    _ = _ := by rw [hratio]

theorem low_coarse_failure_le_envelope (D m R K : ℕ) {δ A κ q P : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hm : q / 2 ≤ (m : ℝ))
    (hR : (R : ℝ) ≤ q ^ (1 / 2 + κ / 4))
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ))
    (hP : P / (m : ℝ) ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4)))) :
    let t := (logarithmicSampleSize A q : ℝ)
    let h := 10 * (D + 1)
    4 * P / (δ * (m : ℝ) ^ 2) + 8 * t ^ 2 * R / m +
      16 * t ^ 3 * R / m + (K : ℝ) * (4 * (D : ℝ) * t ^ 2 * R / m) ^ h ≤
      lowFailureEnvelope D δ A κ q := by
  let t := logarithmicSampleSize A q
  let h := 10 * (D + 1)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hm
  have hratio := low_concurrency_ratio_le hq hm hR
  have hpair : 4 * P / (δ * (m : ℝ) ^ 2) ≤
      (16 / δ) * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4))) := by
    have hh := mul_le_mul_of_nonneg_left hP (by positivity : 0 ≤ 4 / δ)
    calc
      _ = (4 / δ) * (P / (m : ℝ) ^ 2) := by
        field_simp [hδ.ne', hm0.ne']

      _ ≤ (4 / δ) *
          (4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4)))) := hh
      _ = _ := by ring
  have hparallel : 8 * (t : ℝ) ^ 2 * R / m ≤
      16 * ((t : ℝ) ^ 2 * q ^ (-(1 / 2 - κ / 4))) := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 8 * (t : ℝ) ^ 2)
    calc
      _ = (8 * (t : ℝ) ^ 2) * ((R : ℝ) / m) := by ring
      _ ≤ (8 * (t : ℝ) ^ 2) * (2 * q ^ (-(1 / 2 - κ / 4))) := hh
      _ = _ := by ring
  have hconcurrent : 16 * (t : ℝ) ^ 3 * R / m ≤
      32 * ((t : ℝ) ^ 3 * q ^ (-(1 / 2 - κ / 4))) := by
    have hh := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 16 * (t : ℝ) ^ 3)
    calc
      _ = (16 * (t : ℝ) ^ 3) * ((R : ℝ) / m) := by ring
      _ ≤ (16 * (t : ℝ) ^ 3) * (2 * q ^ (-(1 / 2 - κ / 4))) := hh
      _ = _ := by ring
  have hbase : 4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m ≤
      (8 * (D : ℝ)) * (t : ℝ) ^ 2 * q ^ (-(1 / 2 - κ / 4)) := by
    have hh := mul_le_mul_of_nonneg_left hratio
      (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2)
    calc
      _ = (4 * (D : ℝ) * (t : ℝ) ^ 2) * ((R : ℝ) / m) := by ring
      _ ≤ (4 * (D : ℝ) * (t : ℝ) ^ 2) * (2 * q ^ (-(1 / 2 - κ / 4))) := hh
      _ = _ := by ring
  have hoccupancy := sampling_occupancy_le_power D h t hq (Nat.cast_nonneg K)
    (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m)
    (by positivity : 0 ≤ 8 * (D : ℝ)) hK hbase
  dsimp only [lowFailureEnvelope]
  dsimp only [t, h] at hparallel hconcurrent hoccupancy
  linarith

theorem high_coarse_failure_le_envelope (D R N K : ℕ) {δ ρ A κ q E : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hρ : 0 < ρ) (hE0 : 0 ≤ E)
    (hE : E ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : q ^ (1 / 2 + κ / 4) ≤ (R : ℝ)) (hN : ρ * q / 2 ≤ (N : ℝ))
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ)) :
    let t := (logarithmicSampleSize A q : ℝ)
    let h := 10 * (D + 1)
    2 * E / (δ * R * N) + (t ^ 2 + t ^ 3) / R +
      (K : ℝ) * (4 * (D : ℝ) * t ^ 2 / R) ^ h ≤
      highFailureEnvelope D δ ρ A κ q := by
  let t := logarithmicSampleSize A q
  let h := 10 * (D + 1)
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hR
  have hsurvivors := high_survivor_term_le D hq hδ hρ hE0 hE hR hN
  have hinverse := high_concurrency_inverse_le hq hR
  have hgeometry : ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / R ≤
      (t : ℝ) ^ 2 * q ^ (-(1 / 2 + κ / 4)) +
        (t : ℝ) ^ 3 * q ^ (-(1 / 2 + κ / 4)) := by
    have hh := mul_le_mul_of_nonneg_left hinverse
      (by positivity : 0 ≤ (t : ℝ) ^ 2 + (t : ℝ) ^ 3)
    calc
      _ = ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) * (1 / (R : ℝ)) := by ring
      _ ≤ ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) * q ^ (-(1 / 2 + κ / 4)) := hh
      _ = _ := by ring
  have hbase : 4 * (D : ℝ) * (t : ℝ) ^ 2 / R ≤
      (4 * (D : ℝ)) * (t : ℝ) ^ 2 * q ^ (-(1 / 2 + κ / 4)) := by
    have hh := mul_le_mul_of_nonneg_left hinverse
      (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2)
    calc
      _ = (4 * (D : ℝ) * (t : ℝ) ^ 2) * (1 / (R : ℝ)) := by ring
      _ ≤ (4 * (D : ℝ) * (t : ℝ) ^ 2) * q ^ (-(1 / 2 + κ / 4)) := hh
      _ = _ := by ring
  have hoccupancy := sampling_occupancy_le_power D h t hq (Nat.cast_nonneg K)
    (by positivity : 0 ≤ 4 * (D : ℝ) * (t : ℝ) ^ 2 / R)
    (by positivity : 0 ≤ 4 * (D : ℝ)) hK hbase
  dsimp only [highFailureEnvelope]
  dsimp only [t, h] at hgeometry hoccupancy
  linarith

theorem low_sampling_failure_le_envelope (D m R K : ℕ) {δ A κ q P : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hm : q / 2 ≤ (m : ℝ))
    (hm4 : 4 ≤ m) (hlarge : 4 * (10 * (D + 1)) ≤ m) (hP0 : 0 ≤ P)
    (hR : (R : ℝ) ≤ q ^ (1 / 2 + κ / 4))
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ))
    (hP : P / (m : ℝ) ^ 2 ≤
      4 * (((D : ℝ) + 4) * q ^ (-(7 * κ / 30)) + q ^ (-(3 * κ / 4)))) :
    let t := logarithmicSampleSize A q
    let h := 10 * (D + 1)
    2 * P / (δ * (m.descFactorial 2 : ℝ)) +
      ((2 * t).descFactorial 2 : ℝ) * R / ((m - 1 : ℕ) : ℝ) +
      ((2 * t).descFactorial 3 : ℝ) * R / ((m - 2 : ℕ) : ℝ) +
      (K : ℝ) * (t : ℝ) ^ (2 * h) * ((m * D * R : ℕ) : ℝ) ^ h /
        (m.descFactorial (2 * h) : ℝ) ≤ lowFailureEnvelope D δ A κ q :=
  (low_sampling_failure_le_coarse m D R (logarithmicSampleSize A q)
    (10 * (D + 1)) K P δ hm4 hδ hlarge hP0).trans
      (low_coarse_failure_le_envelope D m R K hq hδ hm hR hK hP)

theorem high_sampling_failure_le_envelope (D R N K : ℕ) {δ ρ A κ q E : ℝ}
    (hq : 0 < q) (hδ : 0 < δ) (hρ : 0 < ρ) (hE0 : 0 ≤ E)
    (hE : E ≤ ((D : ℝ) + 4) * q ^ (3 / 2 + κ / 10))
    (hR : q ^ (1 / 2 + κ / 4) ≤ (R : ℝ)) (hN : ρ * q / 2 ≤ (N : ℝ))
    (hRlarge : 2 * (10 * (D + 1)) ≤ R) (hNlarge : 2 * (10 * (D + 1)) ≤ N)
    (hK : (K : ℝ) ≤ (D : ℝ) * q ^ (D : ℝ)) :
    let t := logarithmicSampleSize A q
    let h := 10 * (D + 1)
    2 * E / (δ * R * N) + ((t : ℝ) ^ 2 + (t : ℝ) ^ 3) / R +
      (K : ℝ) * (t.descFactorial h : ℝ) ^ 2 * ((D * N : ℕ) : ℝ) ^ h /
        ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
      highFailureEnvelope D δ ρ A κ q := by
  have hR0 : 0 < R := by
    exact_mod_cast lt_of_lt_of_le (Real.rpow_pos_of_pos hq _) hR
  have hN0 : 0 < N := by
    have hNreal : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
    exact_mod_cast hNreal
  exact (add_le_add (le_refl _)
    (high_occupancy_term_le_coarse R N D (logarithmicSampleSize A q)
      (10 * (D + 1)) K hR0 hN0 hRlarge hNlarge)).trans
        (high_coarse_failure_le_envelope (A := A) D R N K hq hδ hρ hE0 hE hR hN hK)

theorem eventually_sampleSize_le_mul_rpow {A a c : ℝ}
    (hA : 0 < A) (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ q : ℝ in atTop, (logarithmicSampleSize A q : ℝ) ≤ c * q ^ a := by
  have hlim := tendsto_sampleSize_pow_mul_rpow_neg_atTop 1 hA ha
  filter_upwards [(tendsto_order.mp hlim).2 c hc,
    eventually_gt_atTop (0 : ℝ)] with q hsmall hq
  rw [pow_one, Real.rpow_neg hq.le, ← div_eq_mul_inv] at hsmall
  exact ((div_lt_iff₀ (Real.rpow_pos_of_pos hq _)).mp hsmall).le

theorem eventually_sampling_size_bounds (D : ℕ) {A ρ κ : ℝ}
    (hA : 0 < A) (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∀ᶠ q : ℝ in atTop,
      8 ≤ q ∧
      10 * (D + 1) ≤ logarithmicSampleSize A q ∧
      (4 * (10 * (D + 1)) : ℝ) ≤ q / 2 ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ q / 2 ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ q ^ (1 / 2 + κ / 4) ∧
      2 * (logarithmicSampleSize A q : ℝ) ≤ ρ * q / 2 := by
  have hlog := (tendsto_logarithmicSampleSize_atTop hA).eventually_ge_atTop
    (((10 * (D + 1) : ℕ) : ℝ))
  have hlinear := eventually_sampleSize_le_mul_rpow hA (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hpencil := eventually_sampleSize_le_mul_rpow hA
    (by positivity : 0 < (1 / 2 : ℝ) + κ / 4) (by norm_num : (0 : ℝ) < 1 / 2)
  have hcomplement := eventually_sampleSize_le_mul_rpow hA (by norm_num : (0 : ℝ) < 1)
    (by positivity : 0 < ρ / 4)
  filter_upwards [eventually_ge_atTop (8 : ℝ), hlog, hlinear, hpencil, hcomplement,
    eventually_ge_atTop (8 * (10 * ((D : ℝ) + 1)))] with
      q hq ht hlo hhi hco hlarge
  have htNat : 10 * (D + 1) ≤ logarithmicSampleSize A q := by exact_mod_cast ht
  rw [Real.rpow_one] at hlo hco
  refine ⟨hq, htNat, ?_, ?_, ?_, ?_⟩ <;> nlinarith

end RyserCoveringCounterexample.LineCover

end

end OAI
