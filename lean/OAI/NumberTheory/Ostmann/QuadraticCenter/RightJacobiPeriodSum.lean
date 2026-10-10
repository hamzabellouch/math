import OAI.NumberTheory.Ostmann.QuadraticCenter.RightJacobiBasic

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem residue_sum_zero_of_negative_unit (f : ℕ → ℤ) {P a : ℕ}
    (hP : 0 < P) (hmod : ∀ m, f m = f (m % P))
    (hmul : ∀ b c, f (b * c) = f b * f c)
    (ha : a.Coprime P) (hfa : f a = -1) :
    ∑ m ∈ Finset.range P, f m = 0 := by
  let g : Fin P → Fin P := fun x => ⟨a * x.val % P, Nat.mod_lt _ hP⟩
  have hginj : Function.Injective g := by
    intro x y he
    have hemod : Nat.ModEq P (a * x.val) (a * y.val) := congrArg Fin.val he
    have hxy := Nat.ModEq.cancel_left_of_coprime ha.symm hemod
    apply Fin.ext
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] using hxy
  let e : Fin P ≃ Fin P := Equiv.ofBijective g ⟨hginj, Finite.surjective_of_injective hginj⟩
  have hs := e.sum_comp (fun x : Fin P => f x.val)
  have hterm (x : Fin P) : f (e x).val = -f x.val := by
    change f (a * x.val % P) = -f x.val
    rw [← hmod, hmul, hfa]
    ring
  simp_rw [hterm] at hs
  rw [Finset.sum_neg_distrib] at hs
  have hz : (∑ x : Fin P, f x.val) = 0 := by omega
  simpa only [Fin.sum_univ_eq_sum_range] using hz

theorem initial_sum_abs_le_period (f : ℕ → ℤ) {P : ℕ} (hP : 0 < P)
    (hmod : ∀ m, f m = f (m % P))
    (hsum : ∑ m ∈ Finset.range P, f m = 0)
    (hbound : ∀ m, |f m| ≤ 1) (N : ℕ) :
    |∑ m ∈ Finset.range N, f m| ≤ (P : ℤ) := by
  have hshift (q i : ℕ) : f (q * P + i) = f i := by
    rw [hmod (q * P + i), Nat.mul_add_mod_self_right, ← hmod]
  have hblock (q : ℕ) : (∑ m ∈ Finset.range (q * P), f m) = 0 := by
    induction q with
    | zero => simp
    | succ q ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih]
        simp_rw [hshift]
        simpa only [zero_add] using hsum
  have hN : N = (N / P) * P + N % P := by simpa only [mul_comm] using (Nat.div_add_mod N P).symm
  have hred : (∑ m ∈ Finset.range N, f m) = ∑ m ∈ Finset.range (N % P), f m := by
    nth_rw 1 [hN]
    rw [Finset.sum_range_add, hblock]
    simp_rw [hshift]
    simp
  rw [hred]
  calc
    |∑ m ∈ Finset.range (N % P), f m| ≤ ∑ m ∈ Finset.range (N % P), |f m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ Finset.range (N % P), (1 : ℤ) := Finset.sum_le_sum (fun m hm => hbound m)
    _ = (N % P : ℤ) := by simp
    _ ≤ P := by exact_mod_cast (Nat.mod_lt N hP).le

end Ostmann.QuadraticCenter

end OAI
