import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem finite_backward_rank_bound {s d₀ : ℕ}
    (R : Fin (s + 1) → ℕ) (charge : Fin s → ℕ)
    (hbase : R (Fin.last s) ≤ d₀)
    (hstep : ∀ j, R j.castSucc ≤ R j.succ + charge j) :
    R 0 ≤ d₀ + ∑ j, charge j := by
  induction s with
  | zero => simpa using hbase
  | succ s ih =>
    have htail := ih (fun j => R j.succ) (fun j => charge j.succ) hbase
      (fun j => hstep j.succ)
    have hhead := hstep 0
    rw [Fin.sum_univ_succ]
    simpa only [Fin.castSucc_zero, Fin.succ_zero_eq_one] using
      (hhead.trans (Nat.add_le_add_right htail (charge 0))).trans_eq (by omega)

theorem recursive_layer_rank_bound {s d₀ d : ℕ}
    (D : Fin s → ℕ) (R : Fin (s + 1) → ℕ)
    (hbase : R (Fin.last s) ≤ d₀)
    (hstep : ∀ j, R j.castSucc ≤ R j.succ + (j.val + 1) * D j)
    (hslots : ∑ j, D j ≤ d) :
    R 0 ≤ d₀ + ∑ j, (j.val + 1) * D j ∧
      d₀ + ∑ j, (j.val + 1) * D j ≤ d₀ + s * d := by
  refine ⟨finite_backward_rank_bound R _ hbase hstep, Nat.add_le_add_left ?_ d₀⟩
  calc
    ∑ j, (j.val + 1) * D j ≤ ∑ j, s * D j := by
      exact Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_right (D j) (by omega))
    _ = s * ∑ j, D j := (Finset.mul_sum _ _ _).symm
    _ ≤ s * d := Nat.mul_le_mul_left s hslots

theorem recursive_detector_rank_bound {s d₀ d : ℕ}
    (D detector : Fin s → ℕ) (R : Fin (s + 1) → ℕ)
    (hbase : R (Fin.last s) ≤ d₀)
    (hdetector : ∀ j, detector j ≤ (j.val + 1) * D j)
    (htransfer : ∀ j, R j.castSucc ≤ detector j + R j.succ)
    (hslots : ∑ j, D j ≤ d) :
    R 0 ≤ d₀ + ∑ j, (j.val + 1) * D j ∧ R 0 ≤ d₀ + s * d := by
  have hstep (j) : R j.castSucc ≤ R j.succ + (j.val + 1) * D j := by
    have h := (htransfer j).trans (Nat.add_le_add_right (hdetector j) (R j.succ))
    simpa only [Nat.add_comm] using h
  have h := recursive_layer_rank_bound D R hbase hstep hslots
  exact ⟨h.1, h.1.trans h.2⟩

noncomputable def originalWeightLayerCount {ι : Type*} [Fintype ι]
    (w : ι → ℕ) {s : ℕ} (j : Fin s) : ℕ :=
  (Finset.univ.filter (fun i => w i = j.val + 1)).card

theorem sum_originalWeightLayerCount {ι : Type*} [Fintype ι]
    {s : ℕ} (w : ι → ℕ) (hwpos : ∀ i, 1 ≤ w i) (hwmax : ∀ i, w i ≤ s) :
    ∑ j : Fin s, originalWeightLayerCount w j = Fintype.card ι := by
  simp only [originalWeightLayerCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hi (i : ι) : (∑ j : Fin s, if w i = j.val + 1 then 1 else 0) = (1 : ℕ) := by
    let j : Fin s := ⟨w i - 1, by have := hwpos i; have := hwmax i; omega⟩
    rw [Finset.sum_eq_single j]
    · simp only [j]
      rw [ite_eq_left (by have := hwpos i; omega)]
    · intro l _ hlj
      rw [ite_eq_right]
      intro h
      apply hlj
      apply Fin.ext
      dsimp [j]
      omega
    · simp
  simp only [hi, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

theorem recursive_original_slot_rank_bound {ι : Type*} [Fintype ι]
    {s d₀ : ℕ} (w : ι → ℕ) (hwpos : ∀ i, 1 ≤ w i) (hwmax : ∀ i, w i ≤ s)
    (detector : Fin s → ℕ) (R : Fin (s + 1) → ℕ)
    (hbase : R (Fin.last s) ≤ d₀)
    (hdetector : ∀ j, detector j ≤ (j.val + 1) * originalWeightLayerCount w j)
    (htransfer : ∀ j, R j.castSucc ≤ detector j + R j.succ) :
    R 0 ≤ d₀ + ∑ j : Fin s, (j.val + 1) * originalWeightLayerCount w j ∧
      R 0 ≤ d₀ + s * Fintype.card ι :=
  recursive_detector_rank_bound (originalWeightLayerCount w) detector R hbase hdetector htransfer
    (sum_originalWeightLayerCount w hwpos hwmax).le

theorem PolynomialPatch.recursive_layer_rank_bound {σ : Type*} {s d d₀ : ℕ}
    (B : PolynomialPatch σ s d)
    (detector : Fin s → ℕ) (R : Fin (s + 1) → ℕ)
    (hbase : R (Fin.last s) ≤ d₀)
    (hdetector : ∀ j, detector j ≤ (j.val + 1) * originalWeightLayerCount B.weight j)
    (htransfer : ∀ j, R j.castSucc ≤ detector j + R j.succ) :
    R 0 ≤ d₀ + ∑ j : Fin s, (j.val + 1) * originalWeightLayerCount B.weight j ∧
      R 0 ≤ d₀ + s * d := by
  simpa only [Fintype.card_fin] using recursive_original_slot_rank_bound
    B.weight B.weight_pos B.weight_le detector R hbase hdetector htransfer

end Erdos3

end

end OAI
