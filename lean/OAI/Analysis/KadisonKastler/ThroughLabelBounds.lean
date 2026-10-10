import OAI.Analysis.KadisonKastler.ThroughLabel
import Mathlib.Analysis.Real.Sqrt

namespace OAI

/-! # Uniform square sums of projection-word bounds -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The two projection-word estimates, written with a square-root denominator. -/
def projectionWordWeight {r : ℕ} (C : ℝ) (s : Sym α r) : ℝ :=
  (if (s : Multiset α).Nodup then 7 * Real.sqrt ((r - 1).factorial : ℝ) else C) /
    Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1))

theorem projectionWordWeight_sq {r : ℕ} (C : ℝ) (s : Sym α r) :
    projectionWordWeight C s ^ 2 =
      if (s : Multiset α).Nodup then
        49 * ((r - 1).factorial : ℝ) / (Fintype.card α : ℝ) ^ (r - 1)
      else C ^ 2 / (Fintype.card α : ℝ) ^ (r - 1) := by
  unfold projectionWordWeight
  rw [div_pow, Real.sq_sqrt (pow_nonneg (Nat.cast_nonneg _) _)]
  split_ifs
  · rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    norm_num
  · rfl

/-- Summing a constant over each of the distinct and repeated parts. -/
theorem sum_throughLabel_ite (a : α) (r : ℕ) (D R : ℝ) :
    (∑ s : ThroughLabel a r, if (s.val : Multiset α).Nodup then D else R) =
      (Fintype.card (DistinctThroughLabel a r) : ℝ) * D +
        (Fintype.card (RepeatedThroughLabel a r) : ℝ) * R := by
  let p : ThroughLabel a r → Prop := fun s => (s.val : Multiset α).Nodup
  rw [← Fintype.sum_subtype_add_sum_subtype p (fun s => if p s then D else R)]
  have hd := Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun s : Sym α r => a ∈ s) (fun s => (s : Multiset α).Nodup))
  have hr := Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun s : Sym α r => a ∈ s) (fun s => ¬ (s : Multiset α).Nodup))
  have hD : (∑ s : {s : ThroughLabel a r // p s}, if p s.val then D else R) =
      (Fintype.card {s : ThroughLabel a r // p s} : ℝ) * D := by
    calc
      _ = ∑ _ : {s : ThroughLabel a r // p s}, D :=
        Finset.sum_congr rfl (fun s _ => ite_eq_left s.property)
      _ = _ := by simp
  have hR : (∑ s : {s : ThroughLabel a r // ¬ p s}, if p s.val then D else R) =
      (Fintype.card {s : ThroughLabel a r // ¬ p s} : ℝ) * R := by
    calc
      _ = ∑ _ : {s : ThroughLabel a r // ¬ p s}, R :=
        Finset.sum_congr rfl (fun s _ => ite_eq_right s.property)
      _ = _ := by simp
  rw [hD, hR, hd, hr]


/-- The distinct multisets use at most one unit of the factorial-normalized budget. -/
theorem factorial_mul_card_distinctThroughLabel_le (a : α) (r : ℕ) (hr : 1 ≤ r) :
    (r - 1).factorial * Fintype.card (DistinctThroughLabel a r) ≤ Fintype.card α ^ (r - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, card_distinctThroughLabel, ← Nat.descFactorial_eq_factorial_mul_choose]
  exact ((Fintype.card α - 1).descFactorial_le_pow k).trans
    (Nat.pow_le_pow_left (Nat.sub_le _ _) _)

/-- The entire through-label square sum is bounded by `49 + 2C²/d`. -/
theorem sum_projectionWordWeight_sq_le (a : α) (r : ℕ) (hr : 2 ≤ r) (C : ℝ) :
    (∑ s : ThroughLabel a r, projectionWordWeight C s.val ^ 2) ≤
      49 + 2 * C ^ 2 / Fintype.card α := by
  have hn : (0 : ℝ) < Fintype.card α := by
    have : Nonempty α := ⟨a⟩
    exact_mod_cast Fintype.card_pos (α := α)
  have hpow : 0 < (Fintype.card α : ℝ) ^ (r - 1) := pow_pos hn _
  simp_rw [projectionWordWeight_sq]
  rw [sum_throughLabel_ite]
  have hd : ((r - 1).factorial : ℝ) * Fintype.card (DistinctThroughLabel a r) ≤
      (Fintype.card α : ℝ) ^ (r - 1) := by
    exact_mod_cast factorial_mul_card_distinctThroughLabel_le a r (by omega)
  have he : (Fintype.card (RepeatedThroughLabel a r) : ℝ) ≤
      2 * (Fintype.card α : ℝ) ^ (r - 2) := by
    exact_mod_cast card_repeatedThroughLabel a r hr
  have hdist : (Fintype.card (DistinctThroughLabel a r) : ℝ) *
      (49 * ((r - 1).factorial : ℝ) / (Fintype.card α : ℝ) ^ (r - 1)) ≤ 49 := by
    rw [← mul_div_assoc, div_le_iff₀ hpow]
    nlinarith
  have hrep : (Fintype.card (RepeatedThroughLabel a r) : ℝ) *
      (C ^ 2 / (Fintype.card α : ℝ) ^ (r - 1)) ≤ 2 * C ^ 2 / Fintype.card α := by
    calc
      _ ≤ (2 * (Fintype.card α : ℝ) ^ (r - 2)) *
          (C ^ 2 / (Fintype.card α : ℝ) ^ (r - 1)) :=
        mul_le_mul_of_nonneg_right he (div_nonneg (sq_nonneg _) hpow.le)
      _ = _ := by
        have hx : r - 1 = (r - 2) + 1 := by omega
        rw [hx, pow_succ]
        field_simp
        simp only [pow_succ]
        ring
  exact add_le_add hdist hrep

/-- A fixed margin of fifteen absorbs all repeated-label words. -/
theorem sum_projectionWordWeight_sq_le_64 (a : α) (r : ℕ) (hr : 2 ≤ r) (C : ℝ)
    (hC : 2 * C ^ 2 ≤ 15 * Fintype.card α) :
    (∑ s : ThroughLabel a r, projectionWordWeight C s.val ^ 2) ≤ 64 := by
  have hn : (0 : ℝ) < Fintype.card α := by
    have : Nonempty α := ⟨a⟩
    exact_mod_cast Fintype.card_pos (α := α)
  have he : 2 * C ^ 2 / Fintype.card α ≤ 15 := (div_le_iff₀ hn).mpr hC
  exact (sum_projectionWordWeight_sq_le a r hr C).trans (by linarith)

/-- The one-letter contribution is already below the uniform budget. -/
theorem sum_projectionWordWeight_sq_one (a : α) (C : ℝ) :
    (∑ s : ThroughLabel a 1, projectionWordWeight C s.val ^ 2) = 49 := by
  have he (s : ThroughLabel a 1) : s.val = Sym.cons a Sym.nil := by
    have hz : s.val.erase a s.property = Sym.nil := Sym.eq_nil_of_card_zero _
    rw [← Sym.cons_erase s.property, hz]
  have hf (s : ThroughLabel a 1) : projectionWordWeight C s.val ^ 2 = 49 := by
    rw [he]
    norm_num [projectionWordWeight, Sym.coe_cons, Multiset.nodup_cons]
  have hc : Fintype.card (ThroughLabel a 1) = 1 := by
    simpa using card_throughLabel a 0
  simp only [hf, Finset.sum_const, Finset.card_univ, hc, one_nsmul]

/-- One matrix-size threshold works simultaneously for every word length up
to a prescribed bound. The constants for repeated words can depend on length. -/
theorem exists_uniform_projectionWordWeight_threshold (N : ℕ) (C : ℕ → ℝ) :
    ∃ D : ℕ, 0 < D ∧ ∀ d : ℕ, D ≤ d → ∀ r : ℕ, 1 ≤ r → r ≤ N →
      ∀ a : Fin d, (∑ s : ThroughLabel a r, projectionWordWeight (C r) s.val ^ 2) ≤ 64 := by
  let S := ∑ r ∈ Finset.range (N + 1), C r ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  obtain ⟨D, hD⟩ := exists_nat_ge (2 * S / 15 + 1)
  have hDpos : 0 < D := by
    have : (0 : ℝ) < D := by linarith
    exact_mod_cast this
  refine ⟨D, hDpos, ?_⟩
  intro d hd r hr hrN a
  obtain rfl | hr2 := eq_or_lt_of_le hr
  · rw [sum_projectionWordWeight_sq_one]
    norm_num
  · apply sum_projectionWordWeight_sq_le_64 a r (by omega)
    have hCr : C r ^ 2 ≤ S :=
      Finset.single_le_sum (fun _ _ => sq_nonneg _) (by simp only [Finset.mem_range]; omega)
    have hDd : (D : ℝ) ≤ d := by exact_mod_cast hd
    simp only [Fintype.card_fin]
    linarith

end

end KadisonKastler

end OAI
