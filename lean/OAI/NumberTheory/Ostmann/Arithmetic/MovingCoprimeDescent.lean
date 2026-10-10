import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Nat.Squarefree
import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotSystem
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSupport

namespace OAI

/-! # Coprimality inherited by an actual moving reversal

These are the support reductions in Section 8.1: the numerator is a unit at
all old slots, so an integral reconstructed pivot and its compensation are
already coprime to every inherited slot. Only their mutual coprimality and
the outside-prime tests remain.
-/

namespace Ostmann

/-- The compensation product and reconstructed giant inherit every old
coprimality test directly from the integer relation. -/
theorem moving_pivot_inherited_coprime (L R u p : ℕ) (s v w : ℤ)
    (hLR : L.Coprime R) (hv : IsCoprime v (L : ℤ)) (hw : IsCoprime w (R : ℤ))
    (hrel : v * R - w * L = s * ((u * p : ℕ) : ℤ)) :
    u.Coprime (L * R) ∧ p.Coprime (L * R) := by
  have hr : v * (R : ℤ) - w * L = s * (u : ℤ) * p := by
    simpa only [Nat.cast_mul, mul_assoc] using hrel
  have h := reversal_inherited_coprime v w L R s u p hLR.isCoprime hv hw hr
  constructor
  · exact Nat.isCoprime_iff_coprime.mp (by simpa only [Nat.cast_mul] using h.2)
  · exact Nat.isCoprime_iff_coprime.mp (by simpa only [Nat.cast_mul] using h.1)

private theorem pairwise_append_of_products (A B : List ℕ)
    (hA : A.Pairwise Nat.Coprime) (hB : B.Pairwise Nat.Coprime)
    (hAB : A.prod.Coprime B.prod) : (A ++ B).Pairwise Nat.Coprime := by
  apply List.pairwise_append.mpr
  refine ⟨hA, hB, ?_⟩
  intro a ha b hb
  exact (Nat.coprime_list_prod_left_iff.mp
    (Nat.coprime_list_prod_right_iff.mp hAB b hb) a ha)

private theorem coprime_products_of_pairwise_append (A B : List ℕ)
    (h : (A ++ B).Pairwise Nat.Coprime) : A.prod.Coprime B.prod := by
  have hc := (List.pairwise_append.mp h).2.2
  apply Nat.coprime_list_prod_left_iff.mpr
  intro a ha
  apply Nat.coprime_list_prod_right_iff.mpr
  intro b hb
  exact hc a ha b hb

/-- The two actual child lists have precisely one new coprimality condition:
the inserted giant must be coprime to its own compensation list. All inherited
cross-list conditions follow from the numerator equation. -/
theorem moving_children_pairwise_iff (L R U : List ℕ) (p : ℕ) (s v w : ℤ)
    (hold : (L ++ R).Pairwise Nat.Coprime)
    (hv : IsCoprime v (L.prod : ℤ)) (hw : IsCoprime w (R.prod : ℤ))
    (hrel : v * R.prod - w * L.prod = s * ((U.prod * p : ℕ) : ℤ)) :
    ((p :: (U ++ L)).Pairwise Nat.Coprime ∧ (p :: (U ++ R)).Pairwise Nat.Coprime) ↔
      U.Pairwise Nat.Coprime ∧ p.Coprime U.prod := by
  constructor
  · rintro ⟨hleft, _⟩
    obtain ⟨hpu, hUL⟩ := List.pairwise_cons.mp hleft
    refine ⟨(List.pairwise_append.mp hUL).1, Nat.coprime_list_prod_right_iff.mpr ?_⟩
    intro b hb
    exact hpu b (List.mem_append_left _ hb)
  · rintro ⟨hU, hpU⟩
    have hLR := coprime_products_of_pairwise_append L R hold
    obtain ⟨hu, hp⟩ := moving_pivot_inherited_coprime L.prod R.prod U.prod p s v w hLR hv hw hrel
    obtain ⟨hL, hR, _⟩ := List.pairwise_append.mp hold
    have child (A : List ℕ) (hA : A.Pairwise Nat.Coprime)
        (huA : U.prod.Coprime A.prod) (hpA : p.Coprime A.prod) :
        (p :: (U ++ A)).Pairwise Nat.Coprime := by
      apply List.pairwise_cons.mpr
      refine ⟨?_, pairwise_append_of_products U A hU hA huA⟩
      intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact Nat.coprime_list_prod_right_iff.mp hpU b hb
      · exact Nat.coprime_list_prod_right_iff.mp hpA b hb
    exact ⟨child L hL (Nat.coprime_mul_iff_right.mp hu).1 (Nat.coprime_mul_iff_right.mp hp).1,
      child R hR (Nat.coprime_mul_iff_right.mp hu).2 (Nat.coprime_mul_iff_right.mp hp).2⟩

private theorem compensation_product_squarefree (U : List ℕ)
    (hprime : ∀ b ∈ U, b.Prime) (hpair : U.Pairwise Nat.Coprime) : Squarefree U.prod := by
  induction U with
  | nil => simp
  | cons b U ih =>
    obtain ⟨hbU, hU⟩ := List.pairwise_cons.mp hpair
    have hcop : b.Coprime U.prod := Nat.coprime_list_prod_right_iff.mpr hbU
    rw [List.prod_cons, Nat.squarefree_mul hcop]
    exact ⟨(hprime b (by simp)).squarefree,
      ih (fun c hc => hprime c (List.mem_cons_of_mem _ hc)) hU⟩

/-- The own-compensation unit test is exactly the nonvanishing numerator
condition modulo the square of each distinct sampled compensation prime. -/
theorem moving_compensation_square_tests (U : List ℕ) (p : ℕ) (s : ℤ)
    (hprime : ∀ b ∈ U, b.Prime) (hpair : U.Pairwise Nat.Coprime)
    (hs : ∀ b ∈ U, ¬ b ∣ s.natAbs) :
    p.Coprime U.prod ↔ ∀ b ∈ U, ¬ (b : ℤ) ^ 2 ∣ s * ((U.prod * p : ℕ) : ℤ) := by
  have hsf := compensation_product_squarefree U hprime hpair
  have heq (b : ℕ) (hb : b ∈ U) :
      (¬ (b : ℤ) ^ 2 ∣ s * ((U.prod * p : ℕ) : ℤ)) ↔ ¬ b ∣ p := by
    have hd : ((b : ℤ) ^ 2 ∣ s * ((U.prod * p : ℕ) : ℤ)) ↔
        b ^ 2 ∣ s.natAbs * U.prod * p := by
      rw [← Nat.cast_pow, Int.natCast_dvd]
      simp only [Int.natAbs_mul, Int.natAbs_natCast, mul_assoc]
    rw [hd]
    apply reversal_square_test b s.natAbs U.prod p (hprime b hb) (hs b hb)
      (List.dvd_prod hb)
    have h := Nat.squarefree_iff_prime_squarefree.mp hsf b (hprime b hb)
    simpa only [pow_two] using h
  rw [Nat.coprime_list_prod_right_iff]
  constructor
  · intro h b hb
    exact (heq b hb).mpr ((hprime b hb).coprime_iff_not_dvd.mp (h b hb).symm)
  · intro h b hb
    exact ((hprime b hb).coprime_iff_not_dvd.mpr ((heq b hb).mp (h b hb))).symm

end Ostmann

end OAI
