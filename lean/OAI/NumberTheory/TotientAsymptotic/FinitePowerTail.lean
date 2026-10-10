import OAI.NumberTheory.TotientAsymptotic.FiniteDyadicHarmonic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace OAI

/-! The finite partial-summation bound for a logarithmic power saving. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_power_tail (K L : ℕ) (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    (∑ k ∈ Finset.Icc K L,(k:ℝ)^(-1-δ)) ≤ (1+δ⁻¹)*(K:ℝ)^(-δ) := by
  by_cases hKL : K ≤ L
  · have hK0 : (0:ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have hsum : (∑ k ∈ Finset.Icc K L,(k:ℝ)^(-1-δ)) =
        (K:ℝ)^(-1-δ)+∑ k ∈ Finset.Ico K L,((k+1:ℕ):ℝ)^(-1-δ) := by
      induction L, hKL using Nat.le_induction with
      | base => simp
      | succ L hKL ih =>
        rw [Finset.sum_Icc_succ_top (by omega),Finset.sum_Ico_succ_top hKL,ih]
        ring
    have hL0 : (0:ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have hant : AntitoneOn (fun x : ℝ => x^(-1-δ)) (Set.Icc (K:ℝ) L) := by
      intro x hx y hy hxy
      exact Real.rpow_le_rpow_of_nonpos (hK0.trans_le hx.1) hxy (by linarith)
    have hint := hant.sum_le_integral_Ico hKL
    have hzero : (0:ℝ) ∉ Set.uIcc (K:ℝ) L := by
      rw [Set.uIcc_of_le (by exact_mod_cast hKL)]
      intro h
      exact (not_le_of_gt hK0) h.1
    have he := integral_rpow (a:=(K:ℝ)) (b:=(L:ℝ))
      (r:=-1-δ) (Or.inr ⟨by linarith,hzero⟩)
    have hpow : -1-δ+1 = -δ := by ring
    rw [hpow] at he
    have htail : (∑ k ∈ Finset.Ico K L,((k+1:ℕ):ℝ)^(-1-δ)) ≤ (K:ℝ)^(-δ)/δ := by
      apply hint.trans
      rw [he]
      have hn := Real.rpow_nonneg (Nat.cast_nonneg L) (-δ)
      have hd : δ ≠ 0 := hδ.ne'
      field_simp
      nlinarith only [hn]
    have hhead : (K:ℝ)^(-1-δ) ≤ (K:ℝ)^(-δ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hK)
      linarith
    rw [hsum]
    have hh := add_le_add hhead htail
    convert hh using 1
    ring
  · rw [Finset.Icc_eq_empty (by omega),Finset.sum_empty]
    positivity

end TotientAsymptotic

end

end OAI
