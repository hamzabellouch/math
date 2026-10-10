import OAI.Combinatorics.ContingencyTables.Sampling.SmallEntries

namespace OAI

/-! # The literal reference-row/reference-column completion translation -/

namespace ContingencyTables.CompletionTranslation

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

def star (R : Option I → ℤ) (P : Option J → ℤ) : Option I → Option J → ℤ
  | some _,some _ => 0
  | some i,none => R (some i)
  | none,some j => P (some j)
  | none,none => R none-∑ j,P (some j)

omit [Fintype I] in
lemma star_rows (R : Option I → ℤ) (P : Option J → ℤ) (i : Option I) :
    (∑ j,star R P i j)=R i := by
  cases i <;> simp only [Fintype.sum_option,star,Finset.sum_const_zero] <;> ring

lemma star_columns (R : Option I → ℤ) (P : Option J → ℤ)
    (htotal : (∑ i,R i)=∑ j,P j) (j : Option J) : (∑ i,star R P i j)=P j := by
  cases j with
  | none =>
    simp only [Fintype.sum_option] at htotal
    simp only [Fintype.sum_option,star]
    omega
  | some j => simp only [Fintype.sum_option,star,Finset.sum_const_zero,add_zero]

omit [Fintype I] in
lemma star_neg (R : Option I → ℤ) (P : Option J → ℤ) :
    star (fun i => -R i) (fun j => -P j)=fun i j => -star R P i j := by
  funext i j
  cases i <;> cases j <;> simp only [star,Finset.sum_neg_distrib] <;> ring

def between (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ) : Option I → Option J → ℤ :=
  star (fun i => (R₁ i:ℤ)-R₀ i) (fun j => (P₁ j:ℤ)-P₀ j)

omit [Fintype I] in
lemma between_rows (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ) (i : Option I) :
    (∑ j,between R₀ R₁ P₀ P₁ i j)=(R₁ i:ℤ)-R₀ i := star_rows _ _ i

lemma between_columns (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ)
    (h₀ : (∑ i,R₀ i)=∑ j,P₀ j) (h₁ : (∑ i,R₁ i)=∑ j,P₁ j) (j : Option J) :
    (∑ i,between R₀ R₁ P₀ P₁ i j)=(P₁ j:ℤ)-P₀ j := by
  apply star_columns
  simp only [Finset.sum_sub_distrib,← Nat.cast_sum,h₀,h₁]

omit [Fintype I] in
lemma between_reverse (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ) :
    between R₁ R₀ P₁ P₀=fun i j => -between R₀ R₁ P₀ P₁ i j := by
  have hR : (fun i => (R₀ i:ℤ)-R₁ i)=fun i => -((R₁ i:ℤ)-R₀ i) := by funext i; ring
  have hP : (fun j => (P₀ j:ℤ)-P₁ j)=fun j => -((P₁ j:ℤ)-P₀ j) := by funext j; ring
  unfold between
  rw [hR,hP,star_neg]

omit [Fintype I] in
lemma star_abs_le (R : Option I → ℤ) (P : Option J → ℤ) (M : ℤ)
    (hM : 0 ≤ M) (hR : ∀ i,|R i| ≤ M) (hP : ∀ j,|P j| ≤ M)
    (i : Option I) (j : Option J) :
    |star R P i j| ≤ M*((Fintype.card J:ℤ)+1) := by
  have hsum : |∑ j : J,P (some j)| ≤ (Fintype.card J:ℤ)*M := by
    calc
      _ ≤ ∑ j : J,|P (some j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : J,M := Finset.sum_le_sum (fun j _ => hP (some j))
      _ = _ := by simp
  have hsingle : M ≤ M*((Fintype.card J:ℤ)+1) := by
    nlinarith [mul_nonneg hM (Int.natCast_nonneg (Fintype.card J))]
  cases i with
  | some i =>
    cases j with
    | some j => simpa only [star,abs_zero] using (mul_nonneg hM (by positivity : 0 ≤ (Fintype.card J:ℤ)+1))
    | none => exact (hR (some i)).trans hsingle
  | none =>
    cases j with
    | some j => exact (hP (some j)).trans hsingle
    | none =>
      calc
        _ ≤ |R none|+|∑ j : J,P (some j)| := abs_sub _ _
        _ ≤ M+(Fintype.card J:ℤ)*M := add_le_add (hR none) hsum
        _ = _ := by ring

end ContingencyTables.CompletionTranslation

end OAI
