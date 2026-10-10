import PrimeNumberTheoremAnd.Wiener

namespace OAI

/-! The mod-three prime progression input, from the proved Wiener--Ikehara theorem
and Mathlib's unconditional residue-class von Mangoldt continuation. -/
noncomputable section
open scoped BigOperators
open ArithmeticFunction Filter Topology MeasureTheory LSeries
namespace CubicFirstMoment

/-- The required progression PNT at the von Mangoldt level. -/
theorem modThree_mangoldt_mean (a : ZMod 3) (ha : IsUnit a) :
    Tendsto (fun N : ℕ => cumsum (vonMangoldt.residueClass a) N / N)
      atTop (𝓝 (1/2 : ℝ)) := by
  let f := vonMangoldt.residueClass a
  have hpos : 0 ≤ f := vonMangoldt.residueClass_nonneg a
  have hf (σ : ℝ) (hσ : 1 < σ) : Summable (nterm (fun n => (f n : ℂ)) σ) := by
    have hs := LSeriesSummable_of_abscissaOfAbsConv_lt_re
      (f := fun n => (f n : ℂ)) (s := (σ : ℂ))
      ((vonMangoldt.abscissaOfAbsConv_residueClass_le_one a).trans_lt
        (by exact_mod_cast hσ))
    change Summable (fun n => nterm (fun n => (f n : ℂ)) σ n)
    simp_rw [nterm_eq_norm_term]
    exact hs.norm
  have hcheby : ∃ C : ℝ, ∀ N : ℕ,
      cumsum (fun n => ‖(f n : ℂ)‖) N ≤ C * N := by
    obtain ⟨C,hC⟩ := vonMangoldt_cheby
    refine ⟨C,fun N => (Finset.sum_le_sum ?_).trans (hC N)⟩
    intro n _
    simp only [f, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (vonMangoldt.residueClass_nonneg a n),
      abs_of_nonneg vonMangoldt_nonneg]
    exact vonMangoldt.residueClass_le a n
  have hG := vonMangoldt.continuousOn_LFunctionResidueClassAux a
  have hG' : Set.EqOn (vonMangoldt.LFunctionResidueClassAux a)
      (fun s => LSeries (fun n => (f n : ℂ)) s - ((1/2 : ℝ) : ℂ) / (s - 1)) {s | 1 < s.re} := by
    intro s hs
    simpa only [show Nat.totient 3 = 2 by decide, Nat.cast_ofNat, inv_eq_one_div,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      vonMangoldt.eqOn_LFunctionResidueClassAux ha hs
  exact WienerIkeharaTheorem' hpos hf hcheby hG hG'

end CubicFirstMoment

end

end OAI
