import Mathlib.Data.Fintype.BigOperators
import OAI.NumberTheory.Ostmann.Dirichlet.UniformZeroCount
import OAI.NumberTheory.Ostmann.ZeroDensity.ActualZeros

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.ZeroDensity

theorem card_occurrences_eq_sum (Q : ℕ) (T : ℝ)
    (χ : NonprincipalPrimitiveFamily Q) (P : ℂ → Prop) :
    ((Finset.univ.filter (fun z : ZeroOccurrence Q T => z.1 = χ ∧ P z.point)).card) =
      ∑ ρ ∈ (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).toFinset.filter P,
        Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ := by
  classical
  let (ψ : NonprincipalPrimitiveFamily Q) :
      Fintype {ρ : ℂ // ρ ∈ Ostmann.Dirichlet.zerosUpTo ψ.1.2.1 T} :=
    (Ostmann.Dirichlet.zerosUpTo_finite ψ.1.2.1 ψ.2 T).fintype
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ z : (Σ ψ : NonprincipalPrimitiveFamily Q,
      Σ ρ : {ρ : ℂ // ρ ∈ Ostmann.Dirichlet.zerosUpTo ψ.1.2.1 T},
        Fin (Ostmann.Dirichlet.zeroMultiplicity ψ.1.2.1 ρ.1)),
      if z.1 = χ ∧ P z.2.1.1 then 1 else 0) = _
  simp only [Fintype.sum_sigma, ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
  simp only [Finset.sum_ite_eq']
  rw [Finset.sum_filter]
  symm
  convert Finset.sum_subtype
    (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).toFinset
    (fun ρ => (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).mem_toFinset)
    (fun ρ => if P ρ then Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ else 0) using 1
  simp only [Finset.mem_univ, ite_true]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hρ : P ρ.1 <;> simp [hρ]

theorem local_occurrences_le_log (Q : ℕ) (T : ℝ)
    (χ : NonprincipalPrimitiveFamily Q) (t : ℝ) :
    ((Finset.univ.filter (fun z : ZeroOccurrence Q T =>
      z.1 = χ ∧ (1 / 2 ≤ z.point.re ∧ |z.point.im - t| ≤ 1 / 2))).card : ℝ) ≤
      Real.log (4 * Erdos970.Erdos970Dependency.SiegelWalfisz.absoluteZetaTwo * (χ.1.1.val + 1) * (|t| + 6)) /
        Real.log (55 / 52) := by
  classical
  let S := (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).toFinset.filter
    (fun ρ => 1 / 2 ≤ ρ.re ∧ |ρ.im - t| ≤ 1 / 2)
  have hj := Ostmann.Dirichlet.local_zero_count_le_log χ.1.2.1 χ.2 t S (by
    intro ρ hρ
    obtain ⟨hz, hre, him⟩ := Finset.mem_filter.mp hρ
    have hz' := (Ostmann.Dirichlet.zerosUpTo_finite χ.1.2.1 χ.2 T).mem_toFinset.mp hz
    exact ⟨hre, hz'.1.2.2.le, him⟩)
  calc
    _ = ((∑ ρ ∈ S, Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ : ℕ) : ℝ) := by
      congr 1
      convert card_occurrences_eq_sum Q T χ
        (fun ρ => 1 / 2 ≤ ρ.re ∧ |ρ.im-t| ≤ 1 / 2) using 1
      all_goals congr 1
      all_goals first | rfl | (ext z; simp [S])
    _ = ∑ ρ ∈ S, (Ostmann.Dirichlet.zeroMultiplicity χ.1.2.1 ρ : ℝ) := by
      push_cast
      rfl
    _ ≤ _ := by simpa only [Nat.cast_add, Nat.cast_one] using hj

def localMultiplicityBound (Q : ℕ) (H : ℝ) : ℝ :=
  Real.log (4 * Erdos970.Erdos970Dependency.SiegelWalfisz.absoluteZetaTwo * Q * (H + 7)) /
    Real.log (55 / 52)

theorem localMultiplicityBound_nonneg {Q : ℕ} (hQ : 1 ≤ Q) {H : ℝ} (hH : 1 ≤ H) :
    0 ≤ localMultiplicityBound Q H := by
  have hB := Erdos970.Erdos970Dependency.SiegelWalfisz.one_le_absoluteZetaTwo
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hBQ : 1 ≤ Erdos970.Erdos970Dependency.SiegelWalfisz.absoluteZetaTwo * Q := by nlinarith
  apply div_nonneg (Real.log_nonneg _) (Real.log_pos (by norm_num : (1 : ℝ) < 55 / 52)).le
  nlinarith

theorem retainedZeros_local_card_le (Q : ℕ) (exception : Option (PrimitiveFamily Q))
    {σ H : ℝ} (hσ : 1 / 2 ≤ σ) (hH : 1 ≤ H)
    (χ : NonprincipalPrimitiveFamily Q) (t : ℝ) :
    (((retainedZeros Q exception σ H).filter (fun z =>
      z.1 = χ ∧ |z.point.im - t| ≤ 1 / 2)).card : ℝ) ≤ localMultiplicityBound Q H := by
  classical
  let s := (retainedZeros Q exception σ H).filter (fun z =>
    z.1 = χ ∧ |z.point.im - t| ≤ 1 / 2)
  have hQ : 1 ≤ Q := by have := χ.1.1.isLt; omega
  by_cases hs : s.Nonempty
  · obtain ⟨z, hz⟩ := hs
    have hzt := (Finset.mem_filter.mp hz).2.2
    have hzH := z.2.1.2.2
    have ht : |t| ≤ H + 1 := by
      have habs : |t| ≤ |z.point.im| + |z.point.im - t| := by
        have he : t = z.point.im - (z.point.im - t) := by ring
        calc
          |t| = |z.point.im - (z.point.im - t)| := congrArg abs he
          _ ≤ |z.point.im| + |z.point.im - t| := abs_sub _ _
      change |z.point.im| ≤ H at hzH
      linarith
    have hsub : s ⊆ Finset.univ.filter (fun z : ZeroOccurrence Q H =>
        z.1 = χ ∧ (1 / 2 ≤ z.point.re ∧ |z.point.im - t| ≤ 1 / 2)) := by
      intro z hz
      obtain ⟨hretain, heq, him⟩ := Finset.mem_filter.mp hz
      have hre := (Finset.mem_filter.mp hretain).2.2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq, hσ.trans hre, him⟩
    have hcount := (show (s.card : ℝ) ≤
        ((Finset.univ.filter (fun z : ZeroOccurrence Q H =>
          z.1 = χ ∧ (1 / 2 ≤ z.point.re ∧ |z.point.im - t| ≤ 1 / 2))).card : ℝ) by
      exact_mod_cast Finset.card_le_card hsub).trans (local_occurrences_le_log Q H χ t)
    apply hcount.trans
    apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 55 / 52)).le
    have hB := Erdos970.Erdos970Dependency.SiegelWalfisz.one_le_absoluteZetaTwo
    have hq : (χ.1.1.val + 1 : ℝ) ≤ Q := by exact_mod_cast (Nat.succ_le_of_lt χ.1.1.isLt)
    have hqpos : (0 : ℝ) < χ.1.1.val + 1 := by positivity
    apply Real.log_le_log (by positivity)
    have h1 := mul_le_mul_of_nonneg_left hq
      (show 0 ≤ 4 * Erdos970.Erdos970Dependency.SiegelWalfisz.absoluteZetaTwo by linarith)
    exact mul_le_mul h1 (by linarith) (by positivity) (by positivity)
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (s.card : ℝ) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    exact localMultiplicityBound_nonneg hQ hH

end Ostmann.ZeroDensity

end

end OAI
