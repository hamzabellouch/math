import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace OAI

namespace BinPackingGap.PrimaryLoss

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {N : ℕ}

def binItems (f : ι → Fin N) (b : Fin N) : Finset ι :=
  Finset.univ.filter fun i => f i = b

abbrev fiber (f : ι → Fin N) (b : Fin N) : Finset ι := binItems f b

def itemsIn (f : ι → Fin N) (s : Finset (Fin N)) : Finset ι :=
  Finset.univ.filter fun i => f i ∈ s

def binPrimary (f : ι → Fin N) (p : ι → ℤ) (b : Fin N) : ℤ :=
  ∑ i ∈ binItems f b, p i

def fullBins (f : ι → Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun b => (fiber f b).card = 5

def nonfullBins (f : ι → Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun b => (fiber f b).card < 5

def nonfullItems (f : ι → Fin N) : Finset ι := itemsIn f (nonfullBins f)

def negativeFullBins (f : ι → Fin N) (p : ι → ℤ) : Finset (Fin N) :=
  (fullBins f).filter fun b => binPrimary f p b < 0

def outsideZeroFullItems (f : ι → Fin N) (p : ι → ℤ) : Finset ι :=
  Finset.univ.filter fun i =>
    ¬ ((fiber f (f i)).card = 5 ∧ binPrimary f p (f i) = 0)

theorem fibers_disjoint (f : ι → Fin N) {b d : Fin N} (h : b ≠ d) :
    Disjoint (fiber f b) (fiber f d) := by
  apply Finset.disjoint_left.mpr
  intro i hi hd
  simp only [fiber, binItems, Finset.mem_filter, Finset.mem_univ, true_and] at hi hd
  exact h (hi.symm.trans hd)

theorem sum_fibers (f : ι → Fin N) (s : Finset (Fin N))
    {A : Type*} [AddCommMonoid A] (w : ι → A) :
    (∑ b ∈ s, ∑ i ∈ fiber f b, w i) = ∑ i ∈ itemsIn f s, w i := by
  exact Finset.sum_fiberwise_eq_sum_filter Finset.univ s f w

theorem card_itemsIn (f : ι → Fin N) (s : Finset (Fin N)) :
    (itemsIn f s).card = ∑ b ∈ s, (fiber f b).card := by
  exact (Finset.sum_card_fiberwise_eq_card_filter Finset.univ s f).symm

theorem sum_fiber_card (f : ι → Fin N) :
    ∑ b, (fiber f b).card = Fintype.card ι := by
  simpa [itemsIn] using (card_itemsIn f Finset.univ).symm

theorem sum_binPrimary (f : ι → Fin N) (p : ι → ℤ) :
    ∑ b, binPrimary f p b = ∑ i, p i := by
  simpa [itemsIn, binPrimary] using sum_fibers f Finset.univ p

theorem card_itemsIn_le (f : ι → Fin N)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (s : Finset (Fin N)) :
    (itemsIn f s).card ≤ 5 * s.card := by
  rw [card_itemsIn]
  calc
    (∑ b ∈ s, (fiber f b).card) ≤ ∑ _ ∈ s, 5 :=
      Finset.sum_le_sum fun b _ => hcap b
    _ = 5 * s.card := by simp [Nat.mul_comm]

theorem nonfullBins_card_le (f : ι → Fin N) (B c : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c) :
    (nonfullBins f).card ≤ 5 * c := by
  have hmass : ∑ b, (fiber f b).card = 5 * B := (sum_fiber_card f).trans hcard
  have hdef : (∑ b, (5 - (fiber f b).card)) = 5 * N - 5 * B := by
    rw [Finset.sum_tsub_distrib _ (fun b _ => hcap b), hmass]
    simp [Nat.mul_comm]
  calc
    (nonfullBins f).card = ∑ _ ∈ nonfullBins f, 1 := by simp
    _ ≤ ∑ b ∈ nonfullBins f, (5 - (fiber f b).card) := by
      apply Finset.sum_le_sum
      intro b hb
      have hb' : (fiber f b).card < 5 := (Finset.mem_filter.mp hb).2
      omega
    _ ≤ ∑ b : Fin N, (5 - (fiber f b).card) :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ ≤ 5 * c := by rw [hdef]; omega

theorem nonfullItems_card_le (f : ι → Fin N) (B c : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c) :
    (nonfullItems f).card ≤ 25 * c := by
  have hi := card_itemsIn_le f hcap (nonfullBins f)
  have hb := nonfullBins_card_le f B c hcard hcap hN
  change (itemsIn f (nonfullBins f)).card ≤ 25 * c
  omega

theorem full_nonfull_disjoint (f : ι → Fin N) :
    Disjoint (nonfullBins f) (fullBins f) := by
  apply Finset.disjoint_left.mpr
  intro b hn hf
  have hn' := (Finset.mem_filter.mp hn).2
  have hf' := (Finset.mem_filter.mp hf).2
  omega

theorem full_nonfull_union (f : ι → Fin N)
    (hcap : ∀ b, (fiber f b).card ≤ 5) :
    nonfullBins f ∪ fullBins f = Finset.univ := by
  ext b
  simp only [Finset.mem_union, nonfullBins, fullBins, Finset.mem_filter,
    Finset.mem_univ, true_and, iff_true]
  have := hcap b
  omega

theorem primary_conservation (f : ι → Fin N) (p : ι → ℤ)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (htotal : ∑ i, p i = 0) :
    (∑ b ∈ nonfullBins f, binPrimary f p b) +
      (∑ b ∈ fullBins f, binPrimary f p b) = 0 := by
  rw [← Finset.sum_union (full_nonfull_disjoint f), full_nonfull_union f hcap,
    sum_binPrimary, htotal]

theorem negativeFullBins_card_le (f : ι → Fin N) (p : ι → ℤ) (B c P0 : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c)
    (hp : ∀ i, p i ≤ (P0 : ℤ)) (htotal : ∑ i, p i = 0)
    (hfull : ∀ b, (fiber f b).card = 5 → binPrimary f p b ≤ 0) :
    (negativeFullBins f p).card ≤ 25 * c * P0 := by
  have hnegative : ((negativeFullBins f p).card : ℤ) ≤
      -(∑ b ∈ fullBins f, binPrimary f p b) := by
    calc
      ((negativeFullBins f p).card : ℤ) = ∑ _ ∈ negativeFullBins f p, (1 : ℤ) := by simp
      _ = ∑ b ∈ fullBins f, if binPrimary f p b < 0 then (1 : ℤ) else 0 := by
        rw [negativeFullBins, Finset.sum_filter]
      _ ≤ ∑ b ∈ fullBins f, -binPrimary f p b := by
        apply Finset.sum_le_sum
        intro b hb
        have h := hfull b (Finset.mem_filter.mp hb).2
        split_ifs <;> omega
      _ = _ := Finset.sum_neg_distrib (fun b => binPrimary f p b)
  have hnonfull : (∑ b ∈ nonfullBins f, binPrimary f p b) ≤
      ((nonfullItems f).card : ℤ) * (P0 : ℤ) := by
    change (∑ b ∈ nonfullBins f, ∑ i ∈ fiber f b, p i) ≤ _
    rw [sum_fibers]
    calc
      (∑ i ∈ itemsIn f (nonfullBins f), p i) ≤
          ∑ _ ∈ itemsIn f (nonfullBins f), (P0 : ℤ) :=
        Finset.sum_le_sum fun i _ => hp i
      _ = _ := by simp [nonfullItems]
  have hcons := primary_conservation f p hcap htotal
  have hitems : ((nonfullItems f).card : ℤ) ≤ (25 * c : ℕ) := by
    exact_mod_cast nonfullItems_card_le f B c hcard hcap hN
  have hscaled := mul_le_mul_of_nonneg_right hitems (Int.natCast_nonneg P0)
  have hbound : ((negativeFullBins f p).card : ℤ) ≤ ((25 * c * P0 : ℕ) : ℤ) := by
    push_cast
    push_cast at hscaled
    linarith
  exact_mod_cast hbound

variable [DecidableEq ι] in
theorem outsideZeroFullItems_eq (f : ι → Fin N) (p : ι → ℤ)
    (hcap : ∀ b, (fiber f b).card ≤ 5)
    (hfull : ∀ b, (fiber f b).card = 5 → binPrimary f p b ≤ 0) :
    outsideZeroFullItems f p = nonfullItems f ∪ itemsIn f (negativeFullBins f p) := by
  ext i
  simp only [outsideZeroFullItems, nonfullItems, itemsIn, negativeFullBins,
    nonfullBins, fullBins, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  have hc := hcap (f i)
  have hs := hfull (f i)
  omega

theorem loss_items_disjoint (f : ι → Fin N) (p : ι → ℤ) :
    Disjoint (nonfullItems f) (itemsIn f (negativeFullBins f p)) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  simp only [nonfullItems, itemsIn, negativeFullBins, nonfullBins, fullBins,
    Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  omega

variable [DecidableEq ι] in
theorem primary_loss_bound (f : ι → Fin N) (p : ι → ℤ) (B c P0 : ℕ)
    (hcard : Fintype.card ι = 5 * B)
    (hcap : ∀ b, (fiber f b).card ≤ 5) (hN : N ≤ B + c)
    (hp : ∀ i, |p i| < (P0 : ℤ)) (htotal : ∑ i, p i = 0)
    (hfull : ∀ b, (fiber f b).card = 5 → binPrimary f p b ≤ 0) :
    (nonfullItems f).card ≤ 25 * c ∧
    (negativeFullBins f p).card ≤ 25 * c * P0 ∧
    (outsideZeroFullItems f p).card ≤ 25 * c * (1 + 5 * P0) ∧
    (outsideZeroFullItems f p).card < 25 * (c + 1) * (1 + 5 * P0) := by
  have hnf := nonfullItems_card_le f B c hcard hcap hN
  have hneg := negativeFullBins_card_le f p B c P0 hcard hcap hN
    (fun i => (le_abs_self (p i)).trans (hp i).le) htotal hfull
  have hni := card_itemsIn_le f hcap (negativeFullBins f p)
  have hbad : (outsideZeroFullItems f p).card ≤ 25 * c * (1 + 5 * P0) := by
    rw [outsideZeroFullItems_eq f p hcap hfull,
      Finset.card_union_of_disjoint (loss_items_disjoint f p)]
    nlinarith
  refine ⟨hnf, hneg, hbad, hbad.trans_lt ?_⟩
  nlinarith

end BinPackingGap.PrimaryLoss

end OAI
