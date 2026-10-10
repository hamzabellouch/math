import OAI.NumberTheory.Ostmann.QuadraticSieveSignedReindexBasic

namespace OAI

namespace Ostmann.QuadraticSieve

theorem tsum_positive_eq_odd_square_twice (f : ℕ → ℂ)
    (hf : Summable (fun n : {n : ℕ // 0 < n} => f n.val)) :
    (∑' n : {n : ℕ // 0 < n}, f n.val) =
      (∑' b : OddSquarefreeIndex, ∑' c : {c : ℕ // 0 < c}, f (c.val ^ 2 * b.val)) +
      ∑' b : OddSquarefreeIndex, ∑' c : {c : ℕ // 0 < c}, f (c.val ^ 2 * (2 * b.val)) := by
  have hp : Summable (fun p : {c : ℕ // 0 < c} × {b : ℕ // Squarefree b} =>
      f (p.1.val ^ 2 * p.2.val)) := by
    simpa only [Function.comp_def, positiveSquarefreeEquiv_apply] using
      hf.comp_injective positiveSquarefreeEquiv.injective
  have hg : Summable (fun b : {b : ℕ // Squarefree b} =>
      ∑' c : {c : ℕ // 0 < c}, f (c.val ^ 2 * b.val)) := hp.prod_symm.prod
  rw [tsum_positive_eq_tsum_squarefree f hf]
  exact tsum_squarefree_eq_odd_add_twice (fun b => ∑' c : {c : ℕ // 0 < c}, f (c.val ^ 2 * b)) hg

theorem tsum_positive_signed_eq_odd_square_twice (f : ℤ → ℂ) (z : ℤ)
    (hf : Summable (fun n : {n : ℕ // 0 < n} => f (z * (n.val : ℤ)))) :
    (∑' n : {n : ℕ // 0 < n}, f (z * (n.val : ℤ))) =
      (∑' b : OddSquarefreeIndex, ∑' c : {c : ℕ // 0 < c},
        f (z * (b.val : ℤ) * (c.val : ℤ) ^ 2)) +
      ∑' b : OddSquarefreeIndex, ∑' c : {c : ℕ // 0 < c},
        f ((2 * z) * (b.val : ℤ) * (c.val : ℤ) ^ 2) := by
  rw [tsum_positive_eq_odd_square_twice (fun n => f (z * (n : ℤ))) hf]
  congr 1
  · apply tsum_congr
    intro b
    apply tsum_congr
    intro c
    congr 1
    push_cast
    ring
  · apply tsum_congr
    intro b
    apply tsum_congr
    intro c
    congr 1
    push_cast
    ring

theorem signed_squarefree_pair_injective {a : ℤ} (ha : a ≠ 0) :
    Function.Injective (fun p : OddSquarefreeIndex × {c : ℕ // 0 < c} =>
      a * (p.1.val : ℤ) * (p.2.val : ℤ) ^ 2) := by
  intro p q he
  have hc : (p.1.val : ℤ) * (p.2.val : ℤ) ^ 2 =
      (q.1.val : ℤ) * (q.2.val : ℤ) ^ 2 :=
    mul_left_cancel₀ ha (by simpa only [mul_assoc] using he)
  have hn : p.1.val * p.2.val ^ 2 = q.1.val * q.2.val ^ 2 := by exact_mod_cast hc
  have hu := squarefree_square_decomposition_unique p.2.property q.2.property
    p.1.property.2 q.1.property.2
    ((mul_comm _ _).trans (hn.trans (mul_comm _ _)))
  exact Prod.ext (Subtype.ext hu.2) (Subtype.ext hu.1)

theorem summable_signed_squarefree_pairs (f : ℤ → ℂ) (hf : Summable f)
    {a : ℤ} (ha : a ≠ 0) :
    Summable (fun p : OddSquarefreeIndex × {c : ℕ // 0 < c} =>
      f (a * (p.1.val : ℤ) * (p.2.val : ℤ) ^ 2)) :=
  hf.comp_injective (signed_squarefree_pair_injective ha)

theorem tsum_int_eq_zero_add_signed_squarefree (f : ℤ → ℂ) (hf : Summable f) :
    (∑' h : ℤ, f h) = f 0 +
      ∑ a ∈ signedSquarefreeMultipliers, ∑' b : OddSquarefreeIndex,
        ∑' c : {c : ℕ // 0 < c}, f (a * (b.val : ℤ) * (c.val : ℤ) ^ 2) := by
  let T : ℤ → ℂ := fun a => ∑' b : OddSquarefreeIndex,
    ∑' c : {c : ℕ // 0 < c}, f (a * (b.val : ℤ) * (c.val : ℤ) ^ 2)
  have hi : Function.Injective (fun n : {n : ℕ // 0 < n} => (n.val : ℤ)) := by
    intro n t h
    exact Subtype.ext (Int.ofNat_inj.mp h)
  have hn : Function.Injective (fun n : {n : ℕ // 0 < n} => -(n.val : ℤ)) := by
    intro n t h
    exact hi (neg_injective h)
  have hp : (∑' n : ℕ+, f (n : ℤ)) = T 1 + T 2 := by
    simpa only [PNat, PNat.val, one_mul, mul_one, T] using
      tsum_positive_signed_eq_odd_square_twice f 1 (by simpa only [Function.comp_def, one_mul] using hf.comp_injective hi)
  have hm : (∑' n : ℕ+, f (-(n : ℤ))) = T (-1) + T (-2) := by
    simpa only [PNat, PNat.val, neg_one_mul, mul_neg, mul_one, T] using
      tsum_positive_signed_eq_odd_square_twice f (-1)
        (by simpa only [Function.comp_def, neg_one_mul] using hf.comp_injective hn)
  have hs : (∑ a ∈ signedSquarefreeMultipliers, T a) = T (-2) + T (-1) + T 1 + T 2 := by
    norm_num [signedSquarefreeMultipliers]
    abel
  rw [tsum_int_eq_zero_add_tsum_pnat hf, hp, hm]
  change f 0 + (T 1 + T 2) + (T (-1) + T (-2)) = f 0 + ∑ a ∈ signedSquarefreeMultipliers, T a
  rw [hs]
  abel

end Ostmann.QuadraticSieve

end OAI
