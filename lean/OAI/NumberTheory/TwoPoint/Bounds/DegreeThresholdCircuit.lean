import OAI.NumberTheory.TwoPoint.Bounds.ActiveStateExpansion
import OAI.NumberTheory.TwoPoint.Circuits.CircuitBooleanOps

namespace OAI

/-! The literal degree cutoffs are depth-two monotone circuits: a large
active set contains a subset of the prescribed size. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace AC0Circuit

noncomputable def disjunction {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : AC0Circuit n :=
  .orGate (fun i : Fin (Fintype.card ι) => c ((Fintype.equivFin ι).symm i))

lemma disjunction_eval {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) (x : BooleanCube n) :
    (disjunction c).eval x = true ↔ ∃ i, (c i).eval x = true := by
  simp only [disjunction, eval, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨(Fintype.equivFin ι) i, by simpa only [Equiv.symm_apply_apply] using hi⟩

lemma disjunction_depth {ι : Type*} [Fintype ι] {n d : ℕ}
    (c : ι → AC0Circuit n) (hc : ∀ i, (c i).depth ≤ d) :
    (disjunction c).depth ≤ d + 1 := by
  simp only [disjunction, depth]
  have hh : (univ.sup fun i : Fin (Fintype.card ι) =>
      (c ((Fintype.equivFin ι).symm i)).depth) ≤ d :=
    Finset.sup_le (fun i _ => hc _)
  omega

lemma disjunction_size {ι : Type*} [Fintype ι] {n : ℕ}
    (c : ι → AC0Circuit n) : (disjunction c).size = 1 + ∑ i, (c i).size := by
  simp only [disjunction, size]
  congr 1
  exact (Fintype.equivFin ι).symm.sum_comp (fun i => (c i).size)

end AC0Circuit

noncomputable def degreeSubsetCircuit {n : ℕ} (S : Finset (Fin n)) : AC0Circuit n :=
  AC0Circuit.conjunction (fun i : S => .literal i.val true)

lemma degreeSubsetCircuit_eval {n : ℕ} (S : Finset (Fin n)) (x : BooleanCube n) :
    (degreeSubsetCircuit S).eval x = true ↔ S ⊆ activeState x := by
  rw [degreeSubsetCircuit, AC0Circuit.conjunction_eval]
  simp only [AC0Circuit.eval, ite_true]
  constructor
  · intro h i hi
    exact mem_filter.mpr ⟨mem_univ i, h ⟨i, hi⟩⟩
  · intro h i
    exact (mem_filter.mp (h i.property)).2

lemma degreeSubsetCircuit_depth {n : ℕ} (S : Finset (Fin n)) :
    (degreeSubsetCircuit S).depth ≤ 1 :=
  AC0Circuit.conjunction_depth _ (fun _ => Nat.le_refl 0)

lemma degreeSubsetCircuit_size {n : ℕ} (S : Finset (Fin n)) :
    (degreeSubsetCircuit S).size = 1 + S.card := by
  simp [degreeSubsetCircuit, AC0Circuit.conjunction_size, AC0Circuit.size]

noncomputable def degreeThresholdCircuit (n r : ℕ) : AC0Circuit n :=
  AC0Circuit.disjunction (fun S : (univ : Finset (Fin n)).powersetCard r =>
    degreeSubsetCircuit S.val)

lemma degreeThresholdCircuit_eval (n r : ℕ) (x : BooleanCube n) :
    (degreeThresholdCircuit n r).eval x = true ↔ r ≤ (activeState x).card := by
  rw [degreeThresholdCircuit, AC0Circuit.disjunction_eval]
  constructor
  · rintro ⟨S, hS⟩
    have hsub := (degreeSubsetCircuit_eval S.val x).mp hS
    have hcard := (mem_powersetCard.mp S.property).2
    exact hcard ▸ card_le_card hsub
  · intro hr
    obtain ⟨S, hsub, hcard⟩ := exists_subset_card_eq hr
    refine ⟨⟨S, mem_powersetCard.mpr ⟨subset_univ S, hcard⟩⟩, ?_⟩
    exact (degreeSubsetCircuit_eval S x).mpr hsub

lemma degreeThresholdCircuit_depth (n r : ℕ) :
    (degreeThresholdCircuit n r).depth ≤ 2 :=
  AC0Circuit.disjunction_depth _ (fun S => degreeSubsetCircuit_depth S.val)

lemma degreeThresholdCircuit_size (n r : ℕ) :
    (degreeThresholdCircuit n r).size = 1 + n.choose r * (r + 1) := by
  rw [degreeThresholdCircuit, AC0Circuit.disjunction_size]
  have hs (S : (univ : Finset (Fin n)).powersetCard r) :
      (degreeSubsetCircuit S.val).size = r + 1 := by
    rw [degreeSubsetCircuit_size, (mem_powersetCard.mp S.property).2]
    omega
  simp only [hs, sum_const, card_univ, Fintype.card_coe, card_powersetCard,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]

lemma degreeThresholdCircuit_size_le (n r : ℕ) :
    (degreeThresholdCircuit n r).size ≤ 1 + (r + 1) * (n + 1) ^ r := by
  rw [degreeThresholdCircuit_size]
  have hb : n.choose r ≤ (n + 1) ^ r :=
    (Nat.choose_le_pow n r).trans (Nat.pow_le_pow_left (Nat.le_succ n) r)
  simpa only [Nat.mul_comm] using Nat.add_le_add_left
    (Nat.mul_le_mul_right (r + 1) hb) 1

lemma degreeThresholdCircuit_real_eval (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (x : BooleanCube n) :
    (degreeThresholdCircuit n (⌊t⌋₊ + 1)).eval x = true ↔
      t < ((activeState x).card : ℝ) := by
  rw [degreeThresholdCircuit_eval, ← Nat.lt_iff_add_one_le, Nat.floor_lt ht]

lemma degreeThresholdCircuit_size_exp (L : ℝ) (n r : ℕ)
    (hL : 2407 ≤ L) (hn : (n : ℝ) ≤ Real.exp L)
    (hr : (r : ℝ) ≤ 400 * Real.log L + 1) :
    ((degreeThresholdCircuit n r).size : ℝ) ≤ Real.exp (L ^ 3) := by
  have hL0 : 0 ≤ L := by linarith
  have hlog : Real.log L ≤ L :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hrL : (r : ℝ) ≤ 401 * L := by nlinarith
  have hexp : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hn' : (n : ℝ) + 1 ≤ Real.exp (2 * L) := by
    rw [show 2 * L = L + L by ring, Real.exp_add]
    nlinarith
  have hmass : ((r : ℝ) + 1) * ((n : ℝ) + 1) ^ r ≤
      Real.exp (1203 * L ^ 2) := by
    calc
      _ ≤ Real.exp (r : ℝ) * (Real.exp (2 * L)) ^ r :=
        mul_le_mul (Real.add_one_le_exp (r : ℝ))
          (pow_le_pow_left₀ (by positivity) hn' r) (by positivity) (by positivity)
      _ = Real.exp ((r : ℝ) * (1 + 2 * L)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hmul := mul_le_mul_of_nonneg_right hrL
          (show 0 ≤ 1 + 2 * L by positivity)
        have hsq := mul_nonneg hL0 (show 0 ≤ L - 1 by linarith)
        nlinarith)
  have hsize : ((degreeThresholdCircuit n r).size : ℝ) ≤
      1 + ((r : ℝ) + 1) * ((n : ℝ) + 1) ^ r := by
    exact_mod_cast degreeThresholdCircuit_size_le n r
  have hb : 1 ≤ Real.exp (1203 * L ^ 2) :=
    Real.one_le_exp (by positivity)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 1 + Real.exp (1203 * L ^ 2) := by linarith [hsize, hmass]
    _ ≤ Real.exp (1 + 1203 * L ^ 2) := by
      rw [Real.exp_add]
      nlinarith
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hsq : (1 : ℝ) ≤ L ^ 2 := by nlinarith
      have hc := mul_nonneg (sq_nonneg L) (show 0 ≤ L - 1204 by linarith)
      nlinarith)

end TwoPointCorrelations

end OAI
