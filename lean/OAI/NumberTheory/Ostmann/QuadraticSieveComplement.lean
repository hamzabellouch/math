import OAI.NumberTheory.Ostmann.QuadraticSieve
import OAI.NumberTheory.Ostmann.QuadraticSieveSquareLattice
import OAI.NumberTheory.Ostmann.QuadraticSieveSquarefreeReindex

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem tsum_squarefree_coprime_cutoff (K d : ℕ) (f : ℕ → ℂ) :
    (∑' v : {v : ℕ // Squarefree v},
      if v.val ≤ K ∧ Nat.Coprime v.val (2 * d) then f v.val else 0) =
      ∑ v ∈ oddSquarefreeUpTo K, if Nat.Coprime v d then f v else 0 := by
  classical
  change (∑' v : {v : ℕ | Squarefree v},
    if v.val ≤ K ∧ Nat.Coprime v.val (2 * d) then f v.val else 0) = _
  rw [tsum_subtype {v : ℕ | Squarefree v} (fun v =>
    if v ≤ K ∧ Nat.Coprime v (2 * d) then f v else 0)]
  rw [tsum_eq_sum (s := oddSquarefreeUpTo K)]
  · apply Finset.sum_congr rfl
    intro v hv
    have h := mem_oddSquarefreeUpTo.mp hv
    simp [h.2.2.2, h.2.1, Nat.coprime_mul_iff_right,
      Nat.coprime_two_right, h.2.2.1]
  · intro v hv
    by_cases hs : Squarefree v
    · by_cases h : v ≤ K ∧ Nat.Coprime v (2 * d)
      · have hc := Nat.coprime_mul_iff_right.mp h.2
        have hmem : v ∈ oddSquarefreeUpTo K := mem_oddSquarefreeUpTo.mpr
          ⟨Nat.pos_of_ne_zero hs.ne_zero, h.1, Nat.coprime_two_right.mp hc.1, hs⟩
        exact (hv hmem).elim
      · simp [hs, h]
    · simp [hs]

theorem schwartz_summable_positive (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : M ≠ 0) :
    Summable (fun n : {n : ℕ // 0 < n} => W ((n.val : ℝ) / M)) := by
  have hinj : Function.Injective (fun n : {n : ℕ // 0 < n} => (n.val : ℤ)) := by
    intro a b h
    apply Subtype.ext
    change (a.val : ℤ) = (b.val : ℤ) at h
    exact Int.ofNat.inj h
  exact (schwartz_summable_scaled W M hM).comp_injective hinj

theorem schwartz_complement_eq_coprime_lattices (W : 𝓢(ℝ, ℂ))
    (M : ℝ) (hM : 0 < M) (K d q : ℕ) [NeZero d] [NeZero q] :
    (∑' n : {n : ℕ // 0 < n}, if squarefreeKernel n.val ≤ K then
      (if Odd n.val then (jacobiSym (n.val : ℤ) (d ^ 2 * q) : ℂ) *
        W ((n.val : ℝ) / M) else 0) else 0) =
      (1 / 2 : ℂ) * ∑ v ∈ oddSquarefreeUpTo K, if Nat.Coprime v d then
        (jacobiSym (v : ℤ) q : ℂ) *
          ∑' m : ℤ, if Nat.Coprime m.natAbs (2 * q * d) then
            squarePullback W 1 (by norm_num) ((m : ℝ) / Real.sqrt (M / v)) else 0 else 0 := by
  have hk : 2 ≤ 2 * q * d := by
    have hq := Nat.pos_of_neZero q
    have hd := Nat.pos_of_neZero d
    nlinarith
  rw [odd_kernel_cutoff_reindex (fun n => W ((n : ℝ) / M))
    (schwartz_summable_positive W M hM.ne') K d q]
  calc
    _ = ∑' v : {v : ℕ // Squarefree v}, if v.val ≤ K ∧ Nat.Coprime v.val (2 * d) then
        (1 / 2 : ℂ) * ((jacobiSym (v.val : ℤ) q : ℂ) *
          ∑' m : ℤ, if Nat.Coprime m.natAbs (2 * q * d) then
            squarePullback W 1 (by norm_num) ((m : ℝ) / Real.sqrt (M / v.val)) else 0) else 0 := by
      apply tsum_congr
      intro v
      split_ifs with hv
      · have hlat := positive_coprime_square_lattice W M hM v.val
          (Nat.pos_of_ne_zero v.property.ne_zero) (2 * q * d) hk
        push_cast
        rw [hlat]
        ring
      · rfl
    _ = (1 / 2 : ℂ) * ∑' v : {v : ℕ // Squarefree v},
        if v.val ≤ K ∧ Nat.Coprime v.val (2 * d) then
          (jacobiSym (v.val : ℤ) q : ℂ) *
            ∑' m : ℤ, if Nat.Coprime m.natAbs (2 * q * d) then
              squarePullback W 1 (by norm_num) ((m : ℝ) / Real.sqrt (M / v.val)) else 0 else 0 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro v
      split_ifs <;> simp
    _ = _ := congrArg (fun z : ℂ => (1 / 2 : ℂ) * z)
      (tsum_squarefree_coprime_cutoff K d (fun v => (jacobiSym (v : ℤ) q : ℂ) *
        ∑' m : ℤ, if Nat.Coprime m.natAbs (2 * q * d) then
          squarePullback W 1 (by norm_num) ((m : ℝ) / Real.sqrt (M / v)) else 0))

end Ostmann.QuadraticSieve

end OAI
