import OAI.Combinatorics.SquareDifference.ExtendedPair

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

lemma sum_zmod_val {E : Type*} [AddCommMonoid E] (q : ℕ) [NeZero q] (f : ℕ → E) :
    (∑z : ZMod q,f z.val)=∑n∈range q,f n := by
  apply sum_bij (fun z _ => z.val)
  · intro z _; exact mem_range.mpr (ZMod.val_lt z)
  · intro x _ y _ h; exact ZMod.val_injective q h
  · intro n hn
    refine ⟨(n:ZMod q),mem_univ _,?_⟩
    simp only [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp hn)]
  · intros; rfl

lemma sum_zmod_val_support {E : Type*} [AddCommMonoid E] (q : ℕ) [NeZero q]
    (N : ℕ) (hN : N≤q) (f : ℕ → E) (hf : ∀n,N≤n → f n=0) :
    (∑z : ZMod q,f z.val)=∑n∈range N,f n := by
  rw [sum_zmod_val]
  symm
  exact sum_subset (range_mono hN) (fun n _ hn => hf n (by simpa only [mem_range,not_lt] using hn))

section Selected

variable {J : Type*} [Fintype J] [DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

noncomputable def selectedIndicator (M a L : ℕ) (A : Finset ℕ) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (n : ℕ) : ℝ :=
  if n∈A ∧ n∈Ico a (a+L) ∧ (n:ZMod M)=s ∧ ∀j∈B,(n:ZMod (p j))=z j then 1 else 0

lemma selectedIndicator_bound {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (M a L : ℕ) (A : Finset ℕ) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (n : ℕ) : |selectedIndicator p M a L A s B z n|≤1 := by
  unfold selectedIndicator
  split_ifs <;> norm_num

lemma selectedIndicator_zero {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (M a L N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (n : ℕ) (hn : N≤n) : selectedIndicator p M a L A s B z n=0 := by
  apply ite_eq_right
  intro h
  exact (Nat.not_lt.mpr hn) (mem_range.mp (hA h.1))

lemma selectedIndicator_mem {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (M a L : ℕ) (A : Finset ℕ) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (n : ℕ) (hn : selectedIndicator p M a L A s B z n≠0) :
    n∈A ∧ n∈Ico a (a+L) ∧ (n:ZMod M)=s ∧ ∀j∈B,(n:ZMod (p j))=z j := by
  by_contra h
  exact hn (ite_eq_right h)

lemma selectedIndicator_norm (M a L N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (s : ZMod M)
    (B : Finset J) (z : ResidueSpace p) (q : ℕ) [NeZero q] (hN : N≤q) :
    (∑x : ZMod q,‖(selectedIndicator p M a L A s B z x.val:ℂ)‖^2)≤N := by
  rw [sum_zmod_val_support q N hN (fun n => ‖(selectedIndicator p M a L A s B z n:ℂ)‖^2)
    (fun n hn => by rw [selectedIndicator_zero p M a L N A hA s B z n hn]; simp)]
  calc
    _ ≤ ∑n∈range N,(1:ℝ) := by
      apply sum_le_sum
      intro n _
      rw [Complex.norm_real,Real.norm_eq_abs]
      exact pow_le_one₀ (abs_nonneg _) (selectedIndicator_bound p M a L A s B z n)
    _ = _ := by simp

lemma selectedIndicator_order (M a b L N : ℕ) (hab : a+L≤b) (A : Finset ℕ) (hA : A⊆range N)
    (s t : ZMod M) (B : Finset J) (z w : ResidueSpace p)
    {q : ℕ} [NeZero q] (x y : ZMod q)
    (hxy : (selectedIndicator p M a L A s B z x.val:ℂ)*(selectedIndicator p M b L A t B w y.val:ℂ)≠0) :
    x.val<y.val ∧ y.val≤N := by
  have hx := selectedIndicator_mem p M a L A s B z x.val (by exact_mod_cast (mul_ne_zero_iff.mp hxy).1)
  have hy := selectedIndicator_mem p M b L A t B w y.val (by exact_mod_cast (mul_ne_zero_iff.mp hxy).2)
  exact ⟨(mem_Ico.mp hx.2.1).2.trans_le (hab.trans (mem_Ico.mp hy.2.1).1),le_of_lt (mem_range.mp (hA hy.1))⟩

lemma selectedIndicator_square (M a b L N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (hfree : NatSquareFree A)
    (s t : ZMod M) (B : Finset J) (z w : ResidueSpace p)
    {q : ℕ} [NeZero q] (hq : 2*N<q) (x y : ZMod q) (m : ℕ) (hm : m∈range N.sqrt)
    (he : (((m+1)^2:ℕ):ZMod q)=y-x) :
    (selectedIndicator p M a L A s B z x.val:ℂ)*(selectedIndicator p M b L A t B w y.val:ℂ)=0 := by
  by_contra hxy
  have hx := selectedIndicator_mem p M a L A s B z x.val (by exact_mod_cast (mul_ne_zero_iff.mp hxy).1)
  have hy := selectedIndicator_mem p M b L A t B w y.val (by exact_mod_cast (mul_ne_zero_iff.mp hxy).2)
  have hxN := mem_range.mp (hA hx.1)
  have hyN := mem_range.mp (hA hy.1)
  have hmN : (m+1)^2≤N := by
    have hs := Nat.sqrt_le' N
    exact (Nat.pow_le_pow_left (Nat.succ_le_of_lt (mem_range.mp hm)) 2).trans hs
  have hsum : x.val+(m+1)^2<q := by omega
  have he' : ((x.val+(m+1)^2:ℕ):ZMod q)=(y.val:ZMod q) := by
    rw [Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_zmod_val,he]
    ring
  have hv := congrArg ZMod.val he'
  simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hsum,Nat.mod_eq_of_lt (ZMod.val_lt y)] at hv
  exact hfree _ hx.1 _ hy.1 (m+1) (by omega) hv.symm

end Selected

end SquareDifference

end

end OAI
