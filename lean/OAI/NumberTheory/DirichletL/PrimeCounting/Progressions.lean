import PrimeNumberTheoremAnd.Wiener

namespace OAI

namespace SevenEighths.PNT

open Filter ArithmeticFunction LSeries
open scoped Topology

theorem residueClass_chebyshev {q : ℕ} (a : ZMod q) :
    ∃ C : ℝ, ∀ N : ℕ,
      cumsum (fun n : ℕ => ‖(vonMangoldt.residueClass a n : ℂ)‖) N ≤ C * N := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨C, fun N => le_trans ?_ (hC N)⟩
  unfold cumsum
  apply Finset.sum_le_sum
  intro n hn
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (vonMangoldt.residueClass_nonneg a n),
    abs_of_nonneg vonMangoldt_nonneg] using vonMangoldt.residueClass_le a n

theorem residueClass_summable {q : ℕ} (a : ZMod q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (vonMangoldt.residueClass a n : ℂ)) σ) := by
  have hs : LSeriesSummable (fun n => (vonMangoldt.residueClass a n : ℂ)) (σ : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      lt_of_le_of_lt (vonMangoldt.abscissaOfAbsConv_residueClass_le_one a) (by
        exact_mod_cast hσ)
  simpa only [← nterm_eq_norm_term] using hs.norm

theorem residueClass_ratio_tendsto {q : ℕ} [NeZero q]
    (a : ZMod q) (ha : IsUnit a) :
    Tendsto (fun N : ℕ => cumsum (vonMangoldt.residueClass a) N / N)
      atTop (𝓝 ((q.totient : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (vonMangoldt.residueClass_nonneg a)
    (fun σ hσ => residueClass_summable a hσ)
    (residueClass_chebyshev a)
    (vonMangoldt.continuousOn_LFunctionResidueClassAux a)
  simpa only [Complex.ofReal_inv, Complex.ofReal_natCast] using
    vonMangoldt.eqOn_LFunctionResidueClassAux ha

end SevenEighths.PNT

end OAI
