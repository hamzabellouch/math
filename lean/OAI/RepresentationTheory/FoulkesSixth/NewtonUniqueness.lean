import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.SixCycles

namespace OAI

noncomputable section

namespace Foulkes.Lookup
open MvPolynomial Finset Foulkes.Strips

lemma sortedPartition_sum {n : ℕ} (v : Fin n → ℕ) (hv : Function.Injective v) :
    (∑ j, sortedPartition v j) + ∑ j, staircase n j = ∑ j, v j := by
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ j, v (sortDesc v j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact congrFun (shifted_sortedPartition v hv) j
    _ = _ := Equiv.sum_comp (sortDesc v) v

lemma previous_partition_sum {n b : ℕ} (mu : Fin n → ℕ)
    (hmu : ∑ j, mu j = 6*b) (i : ℕ) (hi : i ≤ b)
    (d : Complete.Degree (Fin n) 6)
    (hn : ∀ j, 0 ≤ (shifted mu j : ℤ) - (i : ℤ)*d.val j)
    (hw : Function.Injective (fun j => ((shifted mu j : ℤ) - (i : ℤ)*d.val j).toNat)) :
    ∑ j, sortedPartition (fun j => ((shifted mu j : ℤ) - (i : ℤ)*d.val j).toNat) j = 6*(b-i) := by
  have hd : ∑ j, d.val j = 6 := (Finsupp.degree_eq_sum d.val).symm.trans d.property
  have hs := sortedPartition_sum _ hw
  have hh : (∑ j, (((shifted mu j : ℤ) - (i : ℤ)*d.val j).toNat : ℕ) : ℤ) =
      (6*b : ℕ) + (∑ j, staircase n j : ℕ) - (i : ℤ)*6 := by
    push_cast
    simp only [Int.toNat_of_nonneg (hn _), Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [shifted, Nat.cast_add, Finset.sum_add_distrib]
    simp only [← Nat.cast_sum, hmu, hd]
    norm_num
  have hs' := congrArg (fun z : ℕ => (z : ℤ)) hs
  rw [← Nat.cast_sum] at hh
  rw [hh] at hs'
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hs'
  omega

lemma Q_zero_of_partition {n : ℕ} (mu : Fin n → ℕ) (hmu : ∑ j, mu j = 0) :
    Q n 0 mu = 1 := by
  have hm : mu = 0 := by
    funext j
    have hj := Finset.single_le_sum (f := mu) (fun k _ => Nat.zero_le _) (Finset.mem_univ j)
    simpa [hmu] using hj
  subst mu
  unfold Q schurCoeff
  rw [Complete.pleth_zero, one_mul]
  have hstrict : StrictAnti (staircase n) := by
    intro j k hjk
    have hj := j.isLt
    have hk := k.isLt
    simp only [staircase]
    change j.val < k.val at hjk
    omega
  have he : shifted (0 : Fin n → ℕ) = staircase n := by ext j; simp [shifted]
  rw [he, coeff_alternant_strict _ _ hstrict hstrict, ite_eq_left rfl]

theorem target_table_unique (n B : ℕ) (T : ℕ → (Fin n → ℕ) → ℤ)
    (hzero : ∀ mu, Antitone mu → (∑ j, mu j = 0) → T 0 mu = 1)
    (hstep : ∀ b, 1 ≤ b → b ≤ B → ∀ mu, Antitone mu → (∑ j, mu j = 6*b) →
      (b : ℤ)*T b mu = ∑ i ∈ Finset.Icc 1 b, ∑ d : Complete.Degree (Fin n) 6,
        signedLookup (T (b-i)) (fun j => (shifted mu j : ℤ) - (i : ℤ)*d.val j)) :
    ∀ b, b ≤ B → ∀ mu, Antitone mu → (∑ j, mu j = 6*b) → T b mu = Q n b mu := by
  classical
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro hb mu hm hs
    by_cases h0 : b = 0
    · subst b
      rw [hzero mu hm (by simpa using hs), Q_zero_of_partition mu (by simpa using hs)]
    have hbpos : 1 ≤ b := by omega
    apply (mul_left_cancel₀ (show (b : ℤ) ≠ 0 by exact_mod_cast h0))
    rw [hstep b hbpos hb mu hm hs, target_newton]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro d hd
    unfold signedLookup
    dsimp only
    split_ifs with hn hw
    · congr 1
      exact ih (b-i) (by have := (Finset.mem_Icc.mp hi).1; omega)
        (by omega) _ (sortedPartition_antitone _ hw)
        (previous_partition_sum mu hs i (Finset.mem_Icc.mp hi).2 d hn hw)
    · rfl
    · rfl

end Foulkes.Lookup

end

end OAI
