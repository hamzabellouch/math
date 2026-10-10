import OAI.NumberTheory.JointDickman.Probability.GraphResidueFactors
import OAI.NumberTheory.JointDickman.Probability.ResidueQuotientMean

namespace OAI

/-! # Exact mean of a congruence and the three-root graph majorant -/

namespace JointDickman
open Finset

theorem coprime_residue_product_mean {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d.Coprime q) (f : ZMod d → ℝ) (g : ZMod q → ℝ) :
    (∑ x : ZMod (d*q), f (x.val : ZMod d) * g (x.val : ZMod q)) /
        ((d : ℝ)*q) =
      ((∑ x : ZMod d, f x)/d) * ((∑ x : ZMod q, g x)/q) := by
  let e := ZMod.chineseRemainder hdq
  have he (x : ZMod (d*q)) : e x = ((x.val : ZMod d), (x.val : ZMod q)) := by
    have h := map_natCast e x.val
    rw [ZMod.natCast_zmod_val] at h
    exact h
  have hs := e.toEquiv.sum_comp (fun y : ZMod d × ZMod q => f y.1 * g y.2)
  change (∑ x, f (e x).1 * g (e x).2) = _ at hs
  simp only [he, Fintype.sum_prod_type, ← mul_sum, ← sum_mul] at hs
  rw [hs]
  ring

theorem prime_residue_product_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero p.val] [NeZero (∏ p ∈ P, p)]
    (f : ∀ p : P, ZMod p.val → ℝ) :
    (∑ x : ZMod (∏ p ∈ P, p), ∏ p : P, f p (x.val : ZMod p.val)) /
      (∏ p ∈ P, (p : ℝ)) = ∏ p : P, (∑ y : ZMod p.val, f p y)/(p.val : ℝ) := by
  classical
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p p.property).ne_zero⟩
  let : NeZero (∏ p ∈ P, p) := ⟨prod_ne_zero_iff.mpr (fun p hp => (hP p hp).ne_zero)⟩
  have hpq : Pairwise (fun p q : P => p.val.Coprime q.val) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have hr := residue_sum_eq_range
    (fun x : ZMod (∏ p ∈ P, p) => ((∏ p : P, f p (x.val : ZMod p.val) : ℝ) : ℂ))
  have hsum : (∑ x : ZMod (∏ p ∈ P, p), ∏ p : P, f p (x.val : ZMod p.val)) =
      ∑ n ∈ range (∏ p ∈ P, p), ∏ p : P, f p (n : ZMod p.val) := by
    have hn (n : ℕ) (hn : n ∈ range (∏ p ∈ P, p)) :
        (n : ZMod (∏ p ∈ P, p)).val = n :=
      ZMod.val_natCast_of_lt (mem_range.mp hn)
    have hr' : (∑ x : ZMod (∏ p ∈ P, p), ∏ p : P, f p (x.val : ZMod p.val)) =
      ∑ n ∈ range (∏ p ∈ P, p), ∏ p : P,
        f p ((n : ZMod (∏ p ∈ P, p)).val : ZMod p.val) := by exact_mod_cast hr
    rw [hr']
    exact sum_congr rfl (fun n hn' => by rw [hn n hn'])
  rw [hsum, ← P.prod_coe_sort (fun p : ℕ => p),
    ← P.prod_coe_sort (fun p : ℕ => (p : ℝ))]
  exact crt_product_mean (fun p : P => p.val) hpq f

open Classical in
/-- The endpoint congruence contributes its exact density; the remaining
three-root factors are independent of it by CRT. -/
theorem congruence_three_root_mean (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {d : ℕ} [NeZero d] [NeZero (∏ p ∈ P, p)] [∀ p : P, NeZero p.val]
    (hcop : d.Coprime (∏ p ∈ P, p)) (r : ZMod d)
    (a b c : ∀ p : P, ZMod p.val)
    (hab : ∀ p, a p ≠ b p) (hac : ∀ p, a p ≠ c p) (hbc : ∀ p, b p ≠ c p) :
    (∑ x : ZMod (d * ∏ p ∈ P, p),
      (if (x.val : ZMod d) = r then (1 : ℝ) else 0) *
      ∏ p : P, residueWeight (1/2) (a p) (x.val : ZMod p.val) *
        residueWeight (1/2) (b p) (x.val : ZMod p.val) *
        residueWeight (1/2) (c p) (x.val : ZMod p.val)) /
        ((d : ℝ) * ∏ p ∈ P, (p : ℝ)) =
      (1/(d : ℝ)) * ∏ p ∈ P, (1 - 3/(2*(p : ℝ))) := by
  let q := ∏ p ∈ P, p
  let : NeZero q := ⟨prod_ne_zero_iff.mpr (fun p hp => (hP p hp).ne_zero)⟩
  let : ∀ p : P, NeZero p.val := fun p => ⟨(hP p p.property).ne_zero⟩
  let f (p : P) (x : ZMod p.val) :=
    residueWeight (1/2) (a p) x * residueWeight (1/2) (b p) x *
      residueWeight (1/2) (c p) x
  have hred (x : ZMod (d*q)) (p : P) :
      (((x.val : ZMod q).val : ℕ) : ZMod p.val) = (x.val : ZMod p.val) := by
    have hd : p.val ∣ q := dvd_prod_of_mem id p.property
    rw [ZMod.val_natCast]
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
    exact Nat.mod_mod_of_dvd x.val hd
  have hprod (x : ZMod (d*q)) :
      (∏ p : P, f p (((x.val : ZMod q).val : ℕ) : ZMod p.val)) =
        ∏ p : P, f p (x.val : ZMod p.val) := by
    apply prod_congr rfl
    intro p _
    rw [hred]
  have h := coprime_residue_product_mean hcop
    (fun x : ZMod d => if x = r then (1 : ℝ) else 0)
    (fun x : ZMod q => ∏ p : P, f p (x.val : ZMod p.val))
  simp only [hprod, sum_ite_eq', mem_univ, ite_true] at h
  have hp := prime_residue_product_mean P hP f
  simp only [f, graph_three_root_mean _ _ _ (hab _) (hac _) (hbc _)] at hp
  simp only [f, q, Nat.cast_prod] at h
  rw [hp] at h
  rw [P.prod_coe_sort (fun p : ℕ => 1 - 3/(2*(p : ℝ)))] at h
  simpa only [f, q, Nat.cast_prod] using h

end JointDickman

end OAI
