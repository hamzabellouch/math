import OAI.NumberTheory.Ostmann.Arithmetic.BulkResidueCRT
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticErrorRates

namespace OAI

/-! # The actual frequency/spectator modulus fits one progression cutoff -/

namespace Ostmann
open Filter
open scoped Classical BigOperators

noncomputable def bulkProgressionCutoff (L : ℝ) : ℕ :=
  ⌊Real.exp (Real.exp ((12 / 10000 : ℝ) * L))⌋₊

theorem modulus_le_exp_bulk_endpoint {M : ℕ} {L u : ℝ}
    (hM : M ≤ bulkProgressionCutoff L) (hL : 0 ≤ L)
    (hu : Real.exp ((39 / 10000 : ℝ) * L) ≤ u) :
    (M : ℝ) ≤ Real.exp u := by
  apply (Nat.cast_le.mpr hM).trans
  apply (Nat.floor_le (Real.exp_nonneg _)).trans
  apply Real.exp_le_exp.mpr
  exact (Real.exp_le_exp.mpr (by linarith)).trans hu

theorem bulkProgressionCutoff_bounds (L : ℝ) (hL : 2000 ≤ L) :
    2 ≤ bulkProgressionCutoff L ∧
      Real.log (4 * (bulkProgressionCutoff L : ℝ)) ≤
        2 * Real.exp ((12 / 10000 : ℝ) * L) := by
  have hx : (2 : ℝ) ≤ Real.exp ((12 / 10000 : ℝ) * L) := by
    have hh : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    exact hh.trans (Real.exp_le_exp.mpr (by linarith))
  have hbig : (3 : ℝ) ≤ Real.exp ((12 / 10000 : ℝ) * L) :=
    (by linarith [Real.add_one_le_exp 2] : (3 : ℝ) ≤ Real.exp 2).trans
      (Real.exp_le_exp.mpr (by linarith))
  have hQ : 2 ≤ bulkProgressionCutoff L := by
    apply Nat.le_floor
    exact hx.trans (by linarith [Real.add_one_le_exp (Real.exp ((12 / 10000 : ℝ) * L))])
  refine ⟨hQ, ?_⟩
  have hpos : (0 : ℝ) < bulkProgressionCutoff L := by exact_mod_cast (by omega : 0 < bulkProgressionCutoff L)
  have hf : (bulkProgressionCutoff L : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) :=
    Nat.floor_le (Real.exp_nonneg _)
  have hh := Real.log_le_log (mul_pos (by norm_num : (0 : ℝ) < 4) hpos)
    (mul_le_mul_of_nonneg_left hf (by norm_num : (0 : ℝ) ≤ 4))
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _), Real.log_exp] at hh
  have hlog : Real.log 4 ≤ 3 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith

theorem bulkResidueModulus_exp_bound (m r : ℕ) (p : Fin m → ℕ) (F V : ℝ)
    (hr : (r : ℝ) ≤ Real.exp (F * m)) (hp : ∀ i, (p i : ℝ) ≤ Real.exp V) :
    ((∏ i, bulkResidueModuli r p i : ℕ) : ℝ) ≤ Real.exp (F * m + (m : ℝ) * V) := by
  have hprod : (∏ i : Fin m, (p i : ℝ)) ≤ Real.exp ((m : ℝ) * V) := by
    calc
      _ ≤ ∏ _i : Fin m, Real.exp V := Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hp i)
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
  have he : ((∏ i, bulkResidueModuli r p i : ℕ) : ℝ) = (r : ℝ) * ∏ i, (p i : ℝ) := by
    rw [Fintype.prod_sum_type]
    simp only [bulkResidueModuli, Fintype.prod_unique, Nat.cast_mul, Nat.cast_prod]
  rw [he, Real.exp_add]
  exact mul_le_mul hr hprod (Finset.prod_nonneg fun i _ => Nat.cast_nonneg _) (Real.exp_nonneg _)

theorem bulkResidueModulus_progression_range (F K : ℝ) (hF : 0 ≤ F) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, ∀ (m r : ℕ) (p : Fin m → ℕ),
      (m : ℝ) ≤ K * L → (r : ℝ) ≤ Real.exp (F * m) →
      (∀ i, (p i : ℝ) ≤ Real.exp (Real.exp ((1 / 1000 : ℝ) * L))) →
      (∏ i, bulkResidueModuli r p i) ≤ bulkProgressionCutoff L := by
  filter_upwards [arithmetic_exponent_absorption (1 / 1000) (12 / 10000) 0 ((F + 1) * K) 1 1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    eventually_ge_atTop (0 : ℝ)] with L hrate hL
  intro m r p hm hr hp
  apply Nat.le_floor
  apply (bulkResidueModulus_exp_bound m r p F _ hr hp).trans
  apply Real.exp_le_exp.mpr
  have h₁ := mul_le_mul_of_nonneg_left hm hF
  have h₂ := mul_le_mul_of_nonneg_right hm (Real.exp_nonneg ((1 / 1000 : ℝ) * L))
  have h₃ : 0 ≤ K * L := mul_nonneg hK hL
  have h₄ : 0 ≤ F * K * L := mul_nonneg (mul_nonneg hF hK) hL
  simp only [pow_one, zero_mul, Real.exp_zero, one_mul] at hrate
  have h₅ := mul_nonneg h₄ (Real.exp_nonneg ((1 / 1000 : ℝ) * L))
  nlinarith

theorem bulkResidueModulus_unit_card {M Q : ℕ} [NeZero M] (hMQ : M ≤ Q)
    {L : ℝ} (hQ : (Q : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L))) :
    (Fintype.card (ZMod M)ˣ : ℝ) ≤ Real.exp (Real.exp ((12 / 10000 : ℝ) * L)) := by
  have hc : Fintype.card (ZMod M)ˣ ≤ M := by
    simpa only [ZMod.card] using Fintype.card_le_of_injective
      (fun u : (ZMod M)ˣ => (u : ZMod M)) Units.val_injective
  exact (Nat.cast_le.mpr (hc.trans hMQ)).trans hQ

end Ostmann

end OAI
