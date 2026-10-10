import OAI.NumberTheory.Ostmann.ZeroDensity.RealPrimeSeries
import OAI.NumberTheory.Ostmann.QuadraticSieve.SignedKernelCharacter

namespace OAI

/-! # The Jacobi prime series differs only at the prime two -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def jacobiPrimeTerm (d : ℤ) (s : ℝ) (n : ℕ) : ℝ :=
  if n.Prime then (jacobiSym d n : ℝ) * Real.log n / (n : ℝ) ^ s else 0

private theorem two_weight_bound (a s : ℝ) (ha : |a| ≤ 1) (hs : 0 ≤ s) :
    |a * Real.log 2 / (2 : ℝ) ^ s| ≤ 1 := by
  have hp : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  have hp1 : 1 ≤ (2 : ℝ) ^ s := Real.one_le_rpow (by norm_num) hs
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  rw [abs_div, abs_mul, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)), abs_of_pos hp]
  apply (div_le_one hp).mpr
  nlinarith [abs_nonneg a]

theorem jacobiPrimeSeries_comparison (d : ℤ) (χ : PrimitiveRealCharacter) (s : ℝ)
    (hs : 0 ≤ s)
    (hvalue : ∀ p : ℕ, p.Prime → p ≠ 2 → χ.character p = (jacobiSym d p : ℝ))
    (hsum : Summable (realPrimeTerm χ.character s)) :
    Summable (jacobiPrimeTerm d s) ∧
      |(∑' n, jacobiPrimeTerm d s n) - ∑' n, realPrimeTerm χ.character s n| ≤ 2 := by
  let δ := jacobiPrimeTerm d s 2 - realPrimeTerm χ.character s 2
  let e : ℕ → ℝ := fun n => if n = 2 then δ else 0
  have he : Summable e := summable_of_ne_finset_zero (s := {2}) (by
    intro n hn
    have hne : n ≠ 2 := by simpa only [Finset.mem_singleton] using hn
    exact ite_eq_right hne)
  have heq : jacobiPrimeTerm d s = fun n => realPrimeTerm χ.character s n + e n := by
    funext n
    by_cases hn : n = 2
    · subst n
      simp only [e, ite_true, δ]
      ring
    · have hh : jacobiPrimeTerm d s n = realPrimeTerm χ.character s n := by
        by_cases hp : n.Prime
        · simp only [jacobiPrimeTerm, realPrimeTerm, ite_eq_left hp, hvalue n hp hn]
        · simp only [jacobiPrimeTerm, realPrimeTerm, ite_eq_right hp]
      simpa only [e, ite_eq_right hn, add_zero] using hh
  have ht : (∑' n, e n) = δ := by simp only [e, tsum_ite_eq]
  have hj : Summable (jacobiPrimeTerm d s) := heq ▸ hsum.add he
  refine ⟨hj, ?_⟩
  have hsumeq : (∑' n, jacobiPrimeTerm d s n) = (∑' n, realPrimeTerm χ.character s n) + δ := by
    rw [heq, hsum.tsum_add he, ht]
  rw [hsumeq, add_sub_cancel_left]
  have hJ : |(jacobiSym d 2 : ℝ)| ≤ 1 := by
    rcases jacobiSym.trichotomy d 2 with h | h | h <;> simp [h]
  have hχ : |χ.character (2 : ℕ)| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using χ.character.norm_le_one ((2 : ℕ) : ZMod χ.modulus)
  have hJw := two_weight_bound (jacobiSym d 2) s hJ hs
  have hχw := two_weight_bound (χ.character (2 : ℕ)) s hχ hs
  have hbound := abs_sub_le (jacobiPrimeTerm d s 2) 0 (realPrimeTerm χ.character s 2)
  simp only [sub_zero, zero_sub, abs_neg] at hbound
  dsimp only [δ]
  simp only [Nat.cast_ofNat] at hχw
  simp only [jacobiPrimeTerm, realPrimeTerm, Nat.prime_two, ite_true, Nat.cast_ofNat] at hbound ⊢
  exact hbound.trans (by linarith)

end Ostmann

end OAI
