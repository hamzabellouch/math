import OAI.NumberTheory.JointDickman.Counting.BilinearEnergy
import OAI.NumberTheory.JointDickman.Counting.PeriodicAverages
import OAI.NumberTheory.JointDickman.Probability.ResidueFourierParseval

namespace OAI

/-! # Complete-residue energy of the geometric kernel -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

noncomputable def cyclicGeometricKernel {q : ℕ} [NeZero q] (N : ℕ) (x : ZMod q) : ℝ :=
  ‖∑ n ∈ range N, ZMod.stdAddChar (x*(n:ZMod q))‖^2

lemma cyclicGeometricKernel_nonneg {q : ℕ} [NeZero q] (N : ℕ) (x : ZMod q) :
    0 ≤ cyclicGeometricKernel N x := sq_nonneg _

lemma cyclic_geometric_pair {q : ℕ} [NeZero q] (n m : ℕ) :
    (∑ x : ZMod q, ZMod.stdAddChar (x*(n:ZMod q)) * conj (ZMod.stdAddChar (x*(m:ZMod q)))) =
      if (n:ZMod q) = m then (q:ℂ) else 0 := by
  have he (x : ZMod q) : ZMod.stdAddChar (x*(n:ZMod q)) * conj (ZMod.stdAddChar (x*(m:ZMod q))) =
      ZMod.stdAddChar (x*((n:ZMod q)-(m:ZMod q))) := by
    rw [stdAddChar_conj,←AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [he]
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
  simp only [sub_eq_zero,ZMod.card]
  split_ifs <;> simp

lemma cyclicGeometricKernel_complete {q : ℕ} [NeZero q] {N : ℕ} (hN : N ≤ q) :
    (∑ x : ZMod q, cyclicGeometricKernel N x) = (q:ℝ)*N := by
  have he := BilinearEnergy.energy_identity (univ : Finset (ZMod q)) (range N)
    (fun _ => (1:ℂ)) (fun x n => ZMod.stdAddChar (x*(n:ZMod q)))
  simp only [one_mul,map_one,mul_one] at he
  apply Complex.ofReal_injective
  change ((∑ x : ZMod q, ‖∑ n ∈ range N, ZMod.stdAddChar (x*(n:ZMod q))‖^2 : ℝ):ℂ) = _
  rw [he]
  simp_rw [cyclic_geometric_pair]
  have hi (n : ℕ) (hn : n ∈ range N) (m : ℕ) (hm : m ∈ range N) :
      ((n:ZMod q) = m) ↔ n = m := by
    rw [ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt ((mem_range.mp hn).trans_le hN),
      Nat.mod_eq_of_lt ((mem_range.mp hm).trans_le hN)]
  have hs : (∑ n ∈ range N, ∑ m ∈ range N,
      if (n:ZMod q) = m then (q:ℂ) else 0) = (N:ℂ)*q := by
    calc
      _ = ∑ n ∈ range N, ∑ m ∈ range N, if n=m then (q:ℂ) else 0 := by
        apply sum_congr rfl
        intro n hn
        apply sum_congr rfl
        intro m hm
        simp only [hi n hn m hm]
      _ = ∑ _n ∈ range N, (q:ℂ) := by
        apply sum_congr rfl
        intro n hn
        simp [hn]
      _ = _ := by simp
  rw [hs]
  push_cast
  ring

lemma cyclicGeometricKernel_mod {q : ℕ} [NeZero q] (N : ℕ)
    (x : ZMod q) (hx : x ≠ 0) :
    cyclicGeometricKernel N x = cyclicGeometricKernel (N%q) x := by
  have hzero : (∑ n ∈ range q, ZMod.stdAddChar (x*(n:ZMod q))) = 0 := by
    rw [←residue_sum_eq_range (fun y => ZMod.stdAddChar (x*y))]
    simpa only [mul_comm x,ZMod.card,ite_eq_right hx,Nat.cast_zero] using
      AddChar.sum_mulShift x (ZMod.isPrimitive_stdAddChar q)
  have he := periodic_sum_div_mod (fun y : ZMod q => ZMod.stdAddChar (x*y)) N
  rw [hzero,mul_zero,zero_add] at he
  exact congrArg (fun z : ℂ => ‖z‖^2) he

/-- Excluding zero frequency removes the quadratic peak. The total remaining
energy is at most qN, uniformly even when N spans many periods. -/
theorem cyclicGeometricKernel_nonzero_sum {q : ℕ} [NeZero q] (N : ℕ) :
    (∑ x ∈ (univ : Finset (ZMod q)).erase 0, cyclicGeometricKernel N x) ≤ (q:ℝ)*N := by
  calc
    _ = ∑ x ∈ (univ : Finset (ZMod q)).erase 0, cyclicGeometricKernel (N%q) x := by
      apply sum_congr rfl
      intro x hx
      exact cyclicGeometricKernel_mod N x (mem_erase.mp hx).1
    _ ≤ ∑ x : ZMod q, cyclicGeometricKernel (N%q) x :=
      sum_le_sum_of_subset_of_nonneg (erase_subset _ _)
        (fun x _ _ => cyclicGeometricKernel_nonneg _ x)
    _ = (q:ℝ)*((N%q:ℕ):ℝ) := cyclicGeometricKernel_complete (Nat.mod_lt N (NeZero.pos q)).le
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.mod_le N q) (Nat.cast_nonneg q)

end JointDickman

end OAI
