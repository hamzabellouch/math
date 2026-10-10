import OAI.NumberTheory.JointDickman.Arithmetic.SieveCRT
import OAI.NumberTheory.JointDickman.Counting.PeriodicRectangle

namespace OAI

/-! # Chinese remainder counts in two variables -/

namespace JointDickman

open Finset

/-- Complete residue squares factor by two applications of the CRT. -/
theorem crt_rectangle_period_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) [∀ i, NeZero (m i)] (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (F : ∀ i, ZMod (m i) → ZMod (m i) → ℝ) :
    (∑ r ∈ range (∏ i, m i), ∑ s ∈ range (∏ i, m i),
      ∏ i, F i (r : ZMod (m i)) (s : ZMod (m i))) =
      ∏ i, ∑ r : ZMod (m i), ∑ s : ZMod (m i), F i r s := by
  calc
    _ = ∑ r ∈ range (∏ i, m i), ∏ i, ∑ s : ZMod (m i), F i (r : ZMod (m i)) s := by
      apply sum_congr rfl
      intro r _
      exact crt_period_sum m hm hcop (fun i s => F i (r : ZMod (m i)) s)
    _ = _ := crt_period_sum m hm hcop (fun i r => ∑ s : ZMod (m i), F i r s)

/-- A family of prescribed residue-pair sets has exactly the product of
its local cardinalities in a complete square. -/
theorem crt_pair_period_count {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i) × ZMod (m i))) :
    (∑ r ∈ range (∏ i, m i), ∑ s ∈ range (∏ i, m i),
      if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then (1 : ℝ) else 0) =
      ∏ i, ((A i).card : ℝ) := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hind (r s : ℕ) :
      (∏ i, if ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then (1 : ℝ) else 0) =
        if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then 1 else 0 := by
    split_ifs with h
    · exact prod_eq_one (fun i _ => ite_eq_left (h i))
    · push Not at h
      obtain ⟨i, hi⟩ := h
      exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  simp_rw [← hind]
  rw [crt_rectangle_period_sum m hm hcop (fun i r s => if (r, s) ∈ A i then (1 : ℝ) else 0)]
  apply prod_congr rfl
  intro i _
  rw [← Fintype.sum_prod_type (fun rs : ZMod (m i) × ZMod (m i) =>
    if rs ∈ A i then (1 : ℝ) else 0)]
  simp

/-- The two-dimensional CRT remainder retains the exact number of
prescribed residue pairs. -/
theorem crt_pair_rectangle_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℕ) (hm : ∀ i, 0 < m i)
    (hcop : Pairwise (fun i j => (m i).Coprime (m j)))
    (A : ∀ i, Finset (ZMod (m i) × ZMod (m i)))
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    |(∑ r ∈ Ico a b, ∑ s ∈ Ico c d,
        if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then (1 : ℝ) else 0) -
      (((b : ℝ) - a) * ((d : ℝ) - c) / (∏ i, (m i : ℝ)) ^ 2) *
        ∏ i, ((A i).card : ℝ)| ≤
      2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ i, (m i : ℝ)) + 2) *
        ∏ i, ((A i).card : ℝ) := by
  classical
  let : ∀ i, NeZero (m i) := fun i => ⟨(hm i).ne'⟩
  have hM : 0 < ∏ i, m i := prod_pos (fun i _ => hm i)
  let : NeZero (∏ i, m i) := ⟨hM.ne'⟩
  let e := ZMod.prodEquivPi m hcop
  let F := fun r s : ZMod (∏ i, m i) => if ∀ i, (e r i, e s i) ∈ A i then (1 : ℝ) else 0
  have hF (r s : ℕ) : F r s =
      if ∀ i, ((r : ZMod (m i)), (s : ZMod (m i))) ∈ A i then 1 else 0 := by
    have hr : e (r : ZMod (∏ i, m i)) = (r : ∀ i, ZMod (m i)) := map_natCast e r
    have hs : e (s : ZMod (∏ i, m i)) = (s : ∀ i, ZMod (m i)) := map_natCast e s
    simp [F, hr, hs]
  have hmass : (∑ r ∈ range (∏ i, m i), ∑ s ∈ range (∏ i, m i), F r s) =
      ∏ i, ((A i).card : ℝ) := by
    simp_rw [hF]
    exact crt_pair_period_count m hm hcop A
  have h := nonnegative_periodic_rectangle_error hM F
    (fun r s => by dsimp [F]; split_ifs <;> norm_num) hab hcd
  rw [hmass] at h
  simpa only [hF, Nat.cast_prod] using h

/-- Prime-set specialization with the local densities already factored. -/
theorem prime_pair_rectangle_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (A : ∀ p : ℕ, Finset (ZMod p × ZMod p))
    {a b c d : ℕ} (hab : a ≤ b) (hcd : c ≤ d) :
    |(∑ r ∈ Ico a b, ∑ s ∈ Ico c d,
        if ∀ p ∈ P, ((r : ZMod p), (s : ZMod p)) ∈ A p then (1 : ℝ) else 0) -
      ((b : ℝ) - a) * ((d : ℝ) - c) *
        ∏ p ∈ P, ((A p).card : ℝ) / (p : ℝ) ^ 2| ≤
      2 * ((((b : ℝ) - a) + ((d : ℝ) - c)) / (∏ p ∈ P, (p : ℝ)) + 2) *
        ∏ p ∈ P, ((A p).card : ℝ) := by
  have hcop : Pairwise (fun p q : P => (p : ℕ).Coprime (q : ℕ)) := by
    intro p q hpq
    exact (Nat.coprime_primes (hP p p.property) (hP q q.property)).mpr
      (fun h => hpq (Subtype.ext h))
  have h := crt_pair_rectangle_error (fun p : P => (p : ℕ))
    (fun p => (hP p p.property).pos) hcop (fun p => A p) hab hcd
  simp only [P.prod_coe_sort (fun p : ℕ => ((A p).card : ℝ)),
    P.prod_coe_sort (fun p : ℕ => (p : ℝ)), Subtype.forall] at h
  convert h using 1
  congr 2
  rw [prod_div_distrib, ← prod_pow]
  ring

end JointDickman

end OAI
