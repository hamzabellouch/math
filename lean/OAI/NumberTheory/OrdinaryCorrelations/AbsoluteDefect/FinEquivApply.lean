import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical

namespace OrdinaryCorrelations.FiniteResidues

lemma finEquiv_apply (d : ℕ) [NeZero d] (i : Fin d) :
    ZMod.finEquiv d i = (i.val : ZMod d) := by
  apply ZMod.val_injective d
  rw [ZMod.val_natCast_of_lt i.isLt]
  cases d with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ d => rfl

lemma sum_full_period (d a : ℕ) [NeZero d] (f : ZMod d → ℝ) :
    (∑ i ∈ Finset.range d, f ((a + i : ℕ) : ZMod d)) = ∑ z, f z := by
  rw [← Fin.sum_univ_eq_sum_range]
  have he := ((ZMod.finEquiv d).toEquiv.trans (Equiv.addLeft (a : ZMod d))).sum_comp f
  change (∑ i : Fin d, f ((a : ZMod d) + ZMod.finEquiv d i)) = _ at he
  simpa only [finEquiv_apply, Nat.cast_add] using he

lemma sum_period_decomposition (d a N : ℕ) [NeZero d] (f : ZMod d → ℝ) :
    (∑ i ∈ Finset.range N, f ((a + i : ℕ) : ZMod d)) =
      (N / d : ℕ) * (∑ z, f z) +
        ∑ i ∈ Finset.range (N % d), f ((a + i : ℕ) : ZMod d) := by
  have hfull (q : ℕ) : (∑ i ∈ Finset.range (q * d), f ((a + i : ℕ) : ZMod d)) =
      (q : ℝ) * ∑ z, f z := by
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih]
      have hs : (∑ i ∈ Finset.range d, f ((a + (q * d + i) : ℕ) : ZMod d)) =
          ∑ z, f z := by
        simpa only [Nat.add_assoc] using sum_full_period d (a + q * d) f
      rw [hs, Nat.cast_add, Nat.cast_one]
      ring
  have hn : N = N / d * d + N % d := by simpa [Nat.mul_comm] using (Nat.div_add_mod N d).symm
  conv_lhs => rw [hn]
  rw [Finset.sum_range_add, hfull]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]

def count (d a N : ℕ) [NeZero d] (z : ZMod d) : ℝ :=
  ∑ i ∈ Finset.range N, if ((a + i : ℕ) : ZMod d) = z then 1 else 0

lemma count_small (d a r : ℕ) [NeZero d] (hr : r ≤ d) (z : ZMod d) :
    0 ≤ count d a r z ∧ count d a r z ≤ 1 := by
  constructor
  · unfold count
    exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  · have hinj : Set.InjOn (fun i : ℕ => ((a + i : ℕ) : ZMod d)) (Finset.range r) := by
      intro i hi j hj h
      have hi' : i < d := (Finset.mem_range.mp hi).trans_le hr
      have hj' : j < d := (Finset.mem_range.mp hj).trans_le hr
      simp only [Nat.cast_add] at h
      have hij := congrArg ZMod.val (add_left_cancel h)
      simpa only [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] using hij
    by_cases hex : ∃ i ∈ Finset.range r, ((a + i : ℕ) : ZMod d) = z
    · obtain ⟨i, hi, hiz⟩ := hex
      unfold count
      rw [Finset.sum_eq_single i]
      · simp [hiz]
      · intro j hj hji
        have hjz : ((a + j : ℕ) : ZMod d) ≠ z := by
          intro h
          exact hji (hinj hj hi (h.trans hiz.symm))
        exact ite_eq_right hjz
      · exact fun hn => (hn hi).elim
    · have hz : ∀ i ∈ Finset.range r, ((a + i : ℕ) : ZMod d) ≠ z := by
        intro i hi h
        exact hex ⟨i,hi,h⟩
      unfold count
      rw [Finset.sum_eq_zero (fun i hi => ite_eq_right (hz i hi))]
      norm_num

lemma count_decomposition (d a N : ℕ) [NeZero d] (z : ZMod d) :
    count d a N z = (N / d : ℕ) + count d a (N % d) z := by
  have h := sum_period_decomposition d a N (fun x => if x = z then 1 else 0)
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one, count] using h

theorem count_discrepancy (d a N : ℕ) [NeZero d] (z : ZMod d) :
    |count d a N z - (N : ℝ) / d| ≤ 1 := by
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hr := count_small d a (N % d) (Nat.mod_lt N (Nat.pos_of_ne_zero (NeZero.ne d))).le z
  have he : (N : ℝ) = (N / d : ℕ) * (d : ℝ) + (N % d : ℕ) := by
    exact_mod_cast (show N = N / d * d + N % d by
      simpa [Nat.mul_comm] using (Nat.div_add_mod N d).symm)
  have hrem : 0 ≤ ((N % d : ℕ) : ℝ) ∧ ((N % d : ℕ) : ℝ) ≤ d :=
    ⟨by positivity, by exact_mod_cast (Nat.mod_lt N (Nat.pos_of_ne_zero (NeZero.ne d))).le⟩
  rw [count_decomposition, he, add_div, mul_div_cancel_right₀ _ hd.ne']
  have hdiv : 0 ≤ ((N % d : ℕ) : ℝ) / d ∧ ((N % d : ℕ) : ℝ) / d ≤ 1 :=
    ⟨div_nonneg hrem.1 hd.le, (div_le_one hd).mpr hrem.2⟩
  apply abs_le.mpr
  constructor <;> linarith

def mass (d a N : ℕ) [NeZero d] (z : ZMod d) : ℝ := count d a N z / N

theorem mass_discrepancy (d a N : ℕ) [NeZero d] (hN : 0 < N) (z : ZMod d) :
    |mass d a N z - (d : ℝ)⁻¹| ≤ (N : ℝ)⁻¹ := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have he : mass d a N z - (d : ℝ)⁻¹ = (count d a N z - (N : ℝ) / d) / N := by
    unfold mass
    field_simp
  rw [he, abs_div, abs_of_pos hNp, ← one_div]
  exact div_le_div_of_nonneg_right (count_discrepancy d a N z) hNp.le

theorem tv_residue_le (d a N : ℕ) [NeZero d] (hN : 0 < N) :
    (∑ z : ZMod d, |mass d a N z - (d : ℝ)⁻¹|) / 2 ≤ (d : ℝ) / (2 * N) := by
  have hs := Finset.sum_le_sum (fun z (_ : z ∈ (Finset.univ : Finset (ZMod d))) =>
    mass_discrepancy d a N hN z)
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul] at hs
  apply (div_le_div_of_nonneg_right hs (by norm_num)).trans_eq
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end OrdinaryCorrelations.FiniteResidues

end

end OAI
