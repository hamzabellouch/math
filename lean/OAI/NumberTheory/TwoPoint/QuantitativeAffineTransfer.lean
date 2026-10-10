import OAI.NumberTheory.TwoPoint.Bounds.AffineTransfer
import OAI.NumberTheory.TwoPoint.Statements
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace OAI

/-! Quantitative passage from all progression classes to the main
affine Liouville statement. The logarithmic exponent is preserved. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped Classical Topology

lemma progressionSum_eq_residuePrefix (f g : ℕ → ℂ) (h l b N : ℕ) :
    progressionSum f g h l b N =
      residuePrefix (fun n => f n * g (n + h)) l b N := by
  have hs : Icc 1 N = Ioc 0 N := by
    ext n
    simp only [mem_Icc, mem_Ioc]
    omega
  simp only [progressionSum, residuePrefix, sum_filter, hs]

lemma liouville_affine_norm_le (a₁ a₂ b₁ b₂ N : ℕ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    ‖affineSum liouville liouville a₁ a₂ b₁ b₂ N‖ ≤ N := by
  unfold affineSum
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ‖liouville (a₁ * n + b₁) * liouville (a₂ * n + b₂)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _n ∈ Icc 1 N, (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      have hnpos := (mem_Icc.mp hn).1
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (liouville_oneBounded _ (by nlinarith))).trans
          (liouville_oneBounded _ (by nlinarith))
    _ = _ := by simp

lemma eventually_log_power_le_self (c : ℝ) :
    ∀ᶠ X : ℝ in atTop, (Real.log X) ^ c ≤ X := by
  have hb := (isLittleO_log_rpow_rpow_atTop c (show (0 : ℝ) < 1 by norm_num)).bound
    (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb, eventually_ge_atTop (1 : ℝ)] with X hb hX
  simpa only [Real.rpow_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hX) _),
    abs_of_nonneg (zero_le_one.trans hX), one_mul] using hb

lemma affine_cutoff_log_bound (c X : ℝ) (l b : ℕ)
    (hc : 0 ≤ c) (hX : 4 ≤ X) (hl : 0 < l) :
    ((l * ⌊X⌋₊ + b : ℕ) : ℝ) /
        (Real.log ((l * ⌊X⌋₊ + b : ℕ) : ℝ)) ^ c ≤
      ((l + b : ℕ) : ℝ) * (2 : ℝ) ^ c * X / (Real.log X) ^ c := by
  let Y : ℝ := (l * ⌊X⌋₊ + b : ℕ)
  have hXp : 0 < X := by linarith
  have hYlower : X / 2 ≤ Y := by
    have hf := Nat.lt_floor_add_one X
    have hl' : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have hn : (0 : ℝ) ≤ ⌊X⌋₊ := Nat.cast_nonneg _
    have hh : (⌊X⌋₊ : ℝ) ≤ Y := by
      dsimp only [Y]
      push_cast
      nlinarith [show (0 : ℝ) ≤ b from Nat.cast_nonneg b]
    linarith
  have hYupper : Y ≤ ((l + b : ℕ) : ℝ) * X := by
    have hf := Nat.floor_le hXp.le
    have hXone : 1 ≤ X := by linarith
    dsimp only [Y]
    push_cast
    nlinarith [show (0 : ℝ) ≤ l from Nat.cast_nonneg l,
      show (0 : ℝ) ≤ b from Nat.cast_nonneg b]
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlog4 : 2 * Real.log 2 ≤ Real.log X := by
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [← he]
    exact Real.log_le_log (by norm_num) hX
  have hlogY : Real.log X / 2 ≤ Real.log Y := by
    have hh := Real.log_le_log (by positivity : 0 < X / 2) hYlower
    rw [Real.log_div hXp.ne' (by norm_num)] at hh
    linarith
  have hden : (Real.log X / 2) ^ c ≤ (Real.log Y) ^ c :=
    Real.rpow_le_rpow (by positivity) hlogY hc
  change Y / (Real.log Y) ^ c ≤ _
  calc
    _ ≤ (((l + b : ℕ) : ℝ) * X) / (Real.log X / 2) ^ c :=
      div_le_div₀ (by positivity) hYupper (Real.rpow_pos_of_pos (by positivity) _) hden
    _ = _ := by
      rw [Real.div_rpow hlogX.le (by norm_num)]
      rw [div_div_eq_mul_div]
      ring

lemma real_log_saving_extend (F : ℝ → ℂ) (c : ℝ) (hc : 0 < c)
    (htrivial : ∀ X : ℝ, 3 ≤ X → ‖F X‖ ≤ X)
    (hlarge : ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
      ‖F X‖ ≤ C * X / (Real.log X) ^ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ‖F X‖ ≤ C * X / (Real.log X) ^ c := by
  obtain ⟨C, hC, hb⟩ := hlarge
  obtain ⟨B, hB⟩ := eventually_atTop.1 hb
  let Z : ℝ := max B 3
  let K : ℝ := C + (Real.log Z) ^ c + 1
  have hZ : 3 ≤ Z := le_max_right _ _
  have hlogZ : 0 < Real.log Z := Real.log_pos (by linarith)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro X hX
  have hXp : 0 < X := by linarith
  have hlogX : 0 < (Real.log X) ^ c := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  by_cases hx : Z ≤ X
  · apply (hB X ((le_max_left _ _).trans hx)).trans
    apply div_le_div_of_nonneg_right _ hlogX.le
    have hCK : C ≤ K := by
      dsimp only [K]
      have hp := Real.rpow_nonneg hlogZ.le c
      linarith
    exact mul_le_mul_of_nonneg_right hCK hXp.le
  · have hxl : (Real.log X) ^ c ≤ (Real.log Z) ^ c :=
      Real.rpow_le_rpow (Real.log_pos (by linarith)).le
        (Real.log_le_log hXp (le_of_not_ge hx)) hc.le
    apply (htrivial X hX).trans
    apply (le_div_iff₀ hlogX).mpr
    have hk : (Real.log X) ^ c ≤ K := by
      dsimp only [K]
      linarith
    nlinarith

theorem liouvilleLogSaving_of_progression
    (hprog : ∃ c : ℝ, 0 < c ∧ ∀ h l b : ℕ, 0 < h → 0 < l →
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in atTop,
        ‖progressionSum liouville liouville h l b ⌊X⌋₊‖ ≤
          C * X / (Real.log X) ^ c) : LiouvilleLogSaving := by
  obtain ⟨c, hc, hprog⟩ := hprog
  refine ⟨c, hc, ?_⟩
  intro a₁ a₂ b₁ b₂ ha₁ ha₂ hneq
  let l := a₁ * a₂
  let b := min (a₂ * b₁) (a₁ * b₂)
  let h := Nat.dist (a₁ * b₂) (a₂ * b₁)
  have hl : 0 < l := Nat.mul_pos ha₁ ha₂
  have hh : 0 < h := Nat.dist_pos_of_ne hneq
  obtain ⟨C, hC, hp⟩ := hprog h l b hh hl
  let u : ℕ → ℂ := fun m => liouville m * liouville (m + h)
  let d : ℝ := ‖residuePrefix u l b b‖
  have hd : 0 ≤ d := norm_nonneg _
  have hsample : Tendsto (fun X : ℝ => ((l * ⌊X⌋₊ + b : ℕ) : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [(tendsto_nat_floor_atTop (α := ℝ)).eventually
      (eventually_ge_atTop ⌈max B 0⌉₊)] with X hX
    have hn : ⌊X⌋₊ ≤ l * ⌊X⌋₊ + b := by nlinarith
    have hb : B ≤ (⌈max B 0⌉₊ : ℝ) :=
      (le_max_left _ _).trans (Nat.le_ceil _)
    exact hb.trans (by exact_mod_cast hX.trans hn)
  apply real_log_saving_extend _ c hc
    (fun X hX => (liouville_affine_norm_le a₁ a₂ b₁ b₂ ⌊X⌋₊ ha₁ ha₂).trans
      (Nat.floor_le (by linarith)))
  refine ⟨C * ((l + b : ℕ) : ℝ) * (2 : ℝ) ^ c + d, by
    have hlb : (0 : ℝ) < (l + b : ℕ) := by exact_mod_cast (by omega : 0 < l + b)
    positivity, ?_⟩
  filter_upwards [hsample.eventually hp, eventually_log_power_le_self c,
    eventually_ge_atTop (4 : ℝ)] with X hp hlog hX
  have hY := affine_cutoff_log_bound c X l b hc.le hX hl
  have hXp : 0 < X := by linarith
  have hden : 0 < (Real.log X) ^ c := Real.rpow_pos_of_pos (Real.log_pos (by linarith)) _
  have hboundary : d ≤ d * (X / (Real.log X) ^ c) := by
    have hr : 1 ≤ X / (Real.log X) ^ c := (one_le_div hden).mpr hlog
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hr hd
  have hprefix : ‖residuePrefix u l b (l * ⌊X⌋₊ + b)‖ ≤
      C * ((l * ⌊X⌋₊ + b : ℕ) : ℝ) /
        (Real.log ((l * ⌊X⌋₊ + b : ℕ) : ℝ)) ^ c := by
    simpa only [Nat.floor_natCast, progressionSum_eq_residuePrefix, u] using hp
  rw [liouville_affine_sum_endpoints_all a₁ a₂ b₁ b₂ ⌊X⌋₊ ha₁ ha₂]
  change ‖liouville l * (residuePrefix u l b (l * ⌊X⌋₊ + b) -
    residuePrefix u l b b)‖ ≤ _
  calc
    _ ≤ ‖residuePrefix u l b (l * ⌊X⌋₊ + b) - residuePrefix u l b b‖ :=
      (norm_mul_le _ _).trans (by
        exact mul_le_of_le_one_left (norm_nonneg _) (liouville_oneBounded l hl))
    _ ≤ ‖residuePrefix u l b (l * ⌊X⌋₊ + b)‖ + d := norm_sub_le _ _
    _ ≤ C * (((l + b : ℕ) : ℝ) * (2 : ℝ) ^ c * X / (Real.log X) ^ c) +
        d * (X / (Real.log X) ^ c) :=
      add_le_add (hprefix.trans (by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hY hC.le)) hboundary
    _ = _ := by ring

end TwoPointCorrelations

end OAI
