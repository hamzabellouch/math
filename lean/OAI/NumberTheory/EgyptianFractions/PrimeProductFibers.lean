import Mathlib

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Unique factorization bounds any fixed-product family of prime lists by permutations. -/
lemma prime_list_fiber_card_le (S : Finset (List ℕ)) (s N : ℕ)
    (hlen : ∀ l ∈ S, l.length = s)
    (hprime : ∀ l ∈ S, ∀ p ∈ l, Nat.Prime p)
    (hprod : ∀ l ∈ S, l.prod = N) : S.card ≤ s.factorial := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨l, hl⟩
  · simp
  have hsub : S ⊆ l.permutations.toFinset := by
    intro a ha
    apply List.mem_toFinset.mpr
    apply List.mem_permutations.mpr
    exact (Nat.primeFactorsList_unique (hprod a ha) (hprime a ha)).trans
      (Nat.primeFactorsList_unique (hprod l hl) (hprime l hl)).symm
  calc
    S.card ≤ l.permutations.toFinset.card := Finset.card_le_card hsub
    _ ≤ l.permutations.length := List.toFinset_card_le _
    _ = s.factorial := by rw [List.length_permutations, hlen l hl]

/-- A fixed product has at most `s!` ordered prime factorizations of length `s`. -/
lemma prime_tuple_fiber_card_le {s : ℕ} (S : Finset (Fin s → ℕ)) (N : ℕ)
    (hprime : ∀ a ∈ S, ∀ i, Nat.Prime (a i))
    (hprod : ∀ a ∈ S, (∏ i, a i) = N) : S.card ≤ s.factorial := by
  have h := prime_list_fiber_card_le (S.image List.ofFn) s N
  rw [Finset.card_image_of_injective S List.ofFn_injective] at h
  apply h
  · intro l hl
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
    exact List.length_ofFn
  · intro l hl p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    exact hprime a ha i
  · intro l hl
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hl
    rw [List.prod_ofFn]
    exact hprod a ha

/-- The counting version of the prime-product atom bound, allowing repeated prime samples. -/
theorem prime_product_fiber_card (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (s N : ℕ) :
    (Finset.univ.filter (fun a : Fin s → ↥P => (∏ i, (a i : ℕ)) = N)).card ≤
      s.factorial := by
  classical
  let S := Finset.univ.filter (fun a : Fin s → ↥P => (∏ i, (a i : ℕ)) = N)
  let f : (Fin s → ↥P) → (Fin s → ℕ) := fun a i => a i
  have hf : Function.Injective f := by
    intro a b hab
    funext i
    apply Subtype.ext
    exact congrFun hab i
  have h := prime_tuple_fiber_card_le (S.image f) N
  rw [Finset.card_image_of_injective S hf] at h
  apply h
  · intro a ha i
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact hP (b i) (b i).property
  · intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hb).2

/-- Reducing products modulo a modulus larger than all products preserves the atom bound. -/
theorem prime_product_mod_fiber_card (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (s q : ℕ) (hsmall : ∀ a : Fin s → ↥P, (∏ i, (a i : ℕ)) < q) (r : ZMod q) :
    (Finset.univ.filter (fun a : Fin s → ↥P => ((∏ i, (a i : ℕ)) : ZMod q) = r)).card ≤
      s.factorial := by
  classical
  apply le_trans (Finset.card_le_card ?_) (prime_product_fiber_card P hP s r.val)
  intro a ha
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ a, ?_⟩
  have h := congrArg ZMod.val (Finset.mem_filter.mp ha).2
  rw [← Nat.cast_prod, ZMod.val_natCast, Nat.mod_eq_of_lt (hsmall a)] at h
  exact h

/-- The probability mass of one residue for independent uniform prime samples. -/
def primeProductModMass (P : Finset ℕ) (s q : ℕ) (r : ZMod q) : ℝ :=
  ((Finset.univ.filter (fun a : Fin s → ↥P =>
    ((∏ i, (a i : ℕ)) : ZMod q) = r)).card : ℝ) / (P.card : ℝ)^s

lemma primeProductModMass_nonneg (P : Finset ℕ) (s q : ℕ) (r : ZMod q) :
    0 ≤ primeProductModMass P s q r := by
  unfold primeProductModMass
  positivity

lemma primeProductModMass_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (s q : ℕ) (hsmall : ∀ a : Fin s → ↥P, (∏ i, (a i : ℕ)) < q) (r : ZMod q) :
    primeProductModMass P s q r ≤ (s.factorial : ℝ) / (P.card : ℝ)^s := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast prime_product_mod_fiber_card P hP s q hsmall r
  · positivity

lemma sum_primeProductModMass (P : Finset ℕ) (hP : P.Nonempty)
    (s q : ℕ) [NeZero q] : (∑ r : ZMod q, primeProductModMass P s q r) = 1 := by
  classical
  have hcounts : (∑ r : ZMod q,
      (Finset.univ.filter (fun a : Fin s → ↥P => ((∏ i, (a i : ℕ)) : ZMod q) = r)).card)
      = P.card^s := by
    simpa using Finset.sum_card_fiberwise_eq_card_filter
      (Finset.univ : Finset (Fin s → ↥P)) (Finset.univ : Finset (ZMod q))
      (fun a => ((∏ i, (a i : ℕ)) : ZMod q))
  unfold primeProductModMass
  rw [← Finset.sum_div]
  have hcountsR := congrArg (fun x : ℕ => (x : ℝ)) hcounts
  push_cast at hcountsR
  rw [hcountsR]
  have hp : (0 : ℝ) < P.card := by exact_mod_cast Finset.card_pos.mpr hP
  exact div_self (by positivity)

lemma sum_sq_le_atom_bound {α : Type*} [Fintype α] (p : α → ℝ) (A : ℝ)
    (hpos : ∀ x, 0 ≤ p x) (hbound : ∀ x, p x ≤ A) (hsum : ∑ x, p x = 1) :
    (∑ x, (p x)^2) ≤ A := by
  calc
    (∑ x, (p x)^2) ≤ ∑ x, A * p x := by
      apply Finset.sum_le_sum
      intro x hx
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hbound x) (hpos x)
    _ = A := by rw [← Finset.mul_sum, hsum, mul_one]

/-- The squared `L²` norm of a fresh product distribution is at most its factorial atom bound. -/
theorem prime_product_mod_sum_sq_le (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hne : P.Nonempty) (s q : ℕ) [NeZero q]
    (hsmall : ∀ a : Fin s → ↥P, (∏ i, (a i : ℕ)) < q) :
    (∑ r : ZMod q, (primeProductModMass P s q r)^2) ≤
      (s.factorial : ℝ) / (P.card : ℝ)^s := by
  exact sum_sq_le_atom_bound _ _ (primeProductModMass_nonneg P s q)
    (primeProductModMass_le P hP s q hsmall) (sum_primeProductModMass P hne s q)

/-- A convenient scale form of the factorial atom estimate. -/
lemma factorial_ratio_le_rpow (s : ℕ) (S K P : ℝ) (hS : 1 ≤ S)
    (hs : (s : ℝ) ≤ S) (hP : S^(K-1) ≤ P) :
    (s.factorial : ℝ) / P^s ≤ S^((2-K)*(s : ℝ)) := by
  have hSpos : 0 < S := by linarith
  have hbase : 0 < S^(K-1) := Real.rpow_pos_of_pos hSpos _
  have hPpos : 0 < P := hbase.trans_le hP
  have hf : (s.factorial : ℝ) ≤ S^s := by
    calc
      (s.factorial : ℝ) ≤ (s : ℝ)^s := by exact_mod_cast Nat.factorial_le_pow s
      _ ≤ S^s := pow_le_pow_left₀ (by positivity) hs s
  have hden : (S^(K-1))^s ≤ P^s := pow_le_pow_left₀ hbase.le hP s
  calc
    (s.factorial : ℝ) / P^s ≤ S^s / P^s :=
      div_le_div_of_nonneg_right hf (by positivity)
    _ ≤ S^s / (S^(K-1))^s :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = (S / S^(K-1))^s := (div_pow _ _ _).symm
    _ = (S^(2-K))^s := by
      congr 1
      rw [show 2-K = 1-(K-1) by ring]
      simpa only [Real.rpow_one] using (Real.rpow_sub hSpos 1 (K-1)).symm
    _ = S^((2-K)*(s : ℝ)) := by
      rw [Real.rpow_mul hSpos.le, Real.rpow_natCast]

/-- Scale estimate used for the fresh-product distributions in the random-residue argument. -/
theorem prime_product_mod_sum_sq_le_rpow (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (hne : P.Nonempty) (s q : ℕ) [NeZero q]
    (hsmall : ∀ a : Fin s → ↥P, (∏ i, (a i : ℕ)) < q)
    (S K : ℝ) (hS : 1 ≤ S) (hs : (s : ℝ) ≤ S) (hcard : S^(K-1) ≤ P.card) :
    (∑ r : ZMod q, (primeProductModMass P s q r)^2) ≤ S^((2-K)*(s : ℝ)) :=
  (prime_product_mod_sum_sq_le P hP hne s q hsmall).trans
    (factorial_ratio_le_rpow s S K P.card hS hs hcard)

end Problem337

end

end OAI
