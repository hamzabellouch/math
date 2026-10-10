import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.NumberTheory.Ostmann.Construction.HarmonicInitialAmplitude

namespace OAI

/-! # The actual normalizer and multiplicity costs in repeat removal -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem doubledRole_normalizers {k m : ℕ} (Q : Fin k → Finset ℕ) (R : Fin m → Finset ℕ) :
    (∏ i, (∑ p ∈ Fin.append (Fin.append Q R) (Fin.append Q R) i, (p : ℝ)⁻¹)⁻¹) =
      (∏ i, (∑ p ∈ Q i, (p : ℝ)⁻¹)⁻¹) ^ 2 *
        (∏ i, (∑ p ∈ R i, (p : ℝ)⁻¹)⁻¹) ^ 2 := by
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right]
  ring

theorem bulk_top_normalizers {m c : ℕ} (B T : Finset ℕ) (R : Fin c → Finset ℕ) :
    (∏ i, (∑ p ∈ Fin.append
      (Fin.append (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R)
      (Fin.append (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R) i,
        (p : ℝ)⁻¹)⁻¹) =
      ((∑ p ∈ B, (p : ℝ)⁻¹)⁻¹) ^ (2 * m) *
        ((∑ p ∈ T, (p : ℝ)⁻¹)⁻¹) ^ 2 *
        (∏ i, (∑ p ∈ R i, (p : ℝ)⁻¹)⁻¹) ^ 2 := by
  rw [doubledRole_normalizers]
  simp only [Fin.prod_univ_add, Fin.append_left, Fin.append_right, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, pow_one]
  ring

theorem bulk_top_normalizers_le {m c : ℕ} (B T : Finset ℕ) (R : Fin c → Finset ℕ)
    (L a b J : ℝ) (hL : 0 < L) (ha : 0 < a) (hb : 0 < b)
    (hB : a * L ≤ ∑ p ∈ B, (p : ℝ)⁻¹)
    (hT : b ≤ ∑ p ∈ T, (p : ℝ)⁻¹)
    (hR : ∀ i, Real.exp (-J) ≤ ∑ p ∈ R i, (p : ℝ)⁻¹) :
    (∏ i, (∑ p ∈ Fin.append
      (Fin.append (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R)
      (Fin.append (Fin.append (fun _ : Fin m => B) (fun _ : Fin 1 => T)) R) i,
        (p : ℝ)⁻¹)⁻¹) ≤
      (a * L)⁻¹ ^ (2 * m) * b⁻¹ ^ 2 * Real.exp (2 * c * J) := by
  rw [bulk_top_normalizers]
  have hbi : (∑ p ∈ B, (p : ℝ)⁻¹)⁻¹ ≤ (a * L)⁻¹ :=
    inv_anti₀ (mul_pos ha hL) hB
  have hti : (∑ p ∈ T, (p : ℝ)⁻¹)⁻¹ ≤ b⁻¹ := inv_anti₀ hb hT
  have hri : (∏ i, (∑ p ∈ R i, (p : ℝ)⁻¹)⁻¹) ≤ Real.exp (c * J) := by
    calc
      _ ≤ ∏ _i : Fin c, Real.exp J := by
        apply Finset.prod_le_prod₀ (fun i _ => by positivity)
        intro i _
        have h := inv_anti₀ (Real.exp_pos (-J)) (hR i)
        simpa only [Real.exp_neg, inv_inv] using h
      _ = _ := by simp [← Real.exp_nat_mul, mul_comm]
  have hn : 0 ≤ ∏ i, (∑ p ∈ R i, (p : ℝ)⁻¹)⁻¹ := by positivity
  calc
    _ ≤ (a * L)⁻¹ ^ (2 * m) * b⁻¹ ^ 2 * (Real.exp (c * J)) ^ 2 := by
      gcongr
    _ = _ := by rw [← Real.exp_nat_mul]; congr 2; ring

/-- Extra roles cost only a fixed power of the number of bulk positions. -/
theorem repeated_positions_power (m b : ℕ) (L z : ℝ) (hL : 0 < L)
    (hn : ((2 * m + b : ℕ) : ℝ) ≤ z * L) :
    L⁻¹ ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ (2 * m + b) ≤
      z ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ b := by
  have hn0 : (0 : ℝ) ≤ (2 * m + b : ℕ) := Nat.cast_nonneg _
  have hz : 0 ≤ z := by nlinarith
  have hr : ((2 * m + b : ℕ) : ℝ) / L ≤ z := (div_le_iff₀ hL).mpr hn
  calc
    _ = (((2 * m + b : ℕ) : ℝ) / L) ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ b := by
      rw [pow_add, div_pow, div_eq_mul_inv]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hr _) (by positivity)

/-- A fixed polynomial loss is absorbed before the gap is chosen. -/
theorem eventual_fixed_role_cost (b : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ((2 * m + b : ℕ) : ℝ) ^ b ≤ Real.exp (ε * m) := by
  have ht : Tendsto (fun x : ℝ => (2 * x + b) ^ b / Real.exp (ε * x)) atTop (nhds 0) := by
    have hp := (isLittleO_pow_exp_pos_mul_atTop b (div_pos hε (by norm_num : (0 : ℝ) < 2))).tendsto_div_nhds_zero
    have hc := hp.comp (tendsto_atTop_add_const_right _ (b : ℝ) (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
    have he : ∀ x : ℝ, (2 * x + b) ^ b / Real.exp (ε * x) =
        Real.exp (ε / 2 * b) * ((2 * x + b) ^ b / Real.exp (ε / 2 * (2 * x + b))) := by
      intro x
      rw [show ε / 2 * (2 * x + b) = ε * x + ε / 2 * b by ring, Real.exp_add]
      field_simp
    simpa only [he, mul_zero, Function.comp_apply, id_eq] using hc.const_mul (Real.exp (ε / 2 * b))
  have hn := ht.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hn.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with m hm
  have h := (div_le_iff₀ (Real.exp_pos (ε * m))).mp hm
  simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, one_mul] using h

/-- The bulk normalizers cancel the powers of L in the ordered-tuple cost. -/
theorem eventual_repeat_multiplicity_cost (b : ℕ) (a z : ℝ) (ha : 0 < a) (hz : 0 < z) :
    ∀ᶠ m : ℕ in atTop, ∀ L : ℝ, 0 < L → (m : ℝ) ≤ z * L → b ≤ m →
      (a * L)⁻¹ ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ (2 * m + b) ≤
        Real.exp ((2 * Real.log (3 * z / a) + 1) * m) := by
  filter_upwards [eventual_fixed_role_cost b 1 (by norm_num)] with m hm L hL hmL hbm
  have hnr : ((2 * m + b : ℕ) : ℝ) ≤ 3 * z * L := by
    have hb : (b : ℝ) ≤ m := by exact_mod_cast hbm
    push_cast
    nlinarith
  have hp := repeated_positions_power m b L (3 * z) hL hnr
  have hb := mul_le_mul_of_nonneg_left hp (show 0 ≤ (a⁻¹ : ℝ) ^ (2 * m) by positivity)
  have hpow : (3 * z / a) ^ (2 * m) = Real.exp (((2 * m : ℕ) : ℝ) * Real.log (3 * z / a)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  calc
    _ = a⁻¹ ^ (2 * m) * (L⁻¹ ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ (2 * m + b)) := by
      rw [mul_inv, mul_pow]
      ring
    _ ≤ a⁻¹ ^ (2 * m) * ((3 * z) ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ b) := hb
    _ = (3 * z / a) ^ (2 * m) * ((2 * m + b : ℕ) : ℝ) ^ b := by
      rw [div_eq_mul_inv, mul_pow]
      ring
    _ ≤ (3 * z / a) ^ (2 * m) * Real.exp (1 * m) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = _ := by rw [hpow, ← Real.exp_add]; congr 1; push_cast; ring

end Ostmann

end OAI
