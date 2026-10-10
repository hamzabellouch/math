import Mathlib

namespace OAI

noncomputable section

namespace HeightThree.PowerSeriesDifferential
open MvPowerSeries
variable {R σ : Type*} [CommRing R]

lemma coeff_pow_zero_of_degree_lt (a : MvPowerSeries σ R) (ha : a.constantCoeff = 0)
    (d : σ →₀ ℕ) (n : ℕ) (hn : d.degree < n) : coeff d (a^n) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hn) (le_order_pow_of_constantCoeff_eq_zero n ha)

lemma coeff_subst_eq_of_coeff_le (f g : PowerSeries R) (a : MvPowerSeries σ R)
    (ha : a.constantCoeff = 0) (d : σ →₀ ℕ)
    (h : ∀ n ≤ d.degree, f.coeff n = g.coeff n) :
    coeff d (f.subst a) = coeff d (g.subst a) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero ha)]
  apply finsum_congr
  intro n
  by_cases hn : n ≤ d.degree
  · rw [h n hn]
  · rw [coeff_pow_zero_of_degree_lt a ha d n (by omega), smul_zero, smul_zero]

lemma pderiv_subst_coe (f : Polynomial R) (a : MvPowerSeries σ R)
    (ha : PowerSeries.HasSubst a) (i : σ) :
    pderiv i ((f : PowerSeries R).subst a) =
      ((PowerSeries.derivative (f : PowerSeries R)).subst a) * pderiv i a := by
  simp [PowerSeries.subst_coe ha, PowerSeries.derivative_coe,
    Derivation.comp_aeval_eq (a := a) (pderiv i) f, smul_eq_mul]

lemma pderiv_subst (f : PowerSeries R) (a : MvPowerSeries σ R)
    (ha : a.constantCoeff = 0) (i : σ) :
    pderiv i (f.subst a) = (PowerSeries.derivative f).subst a * pderiv i a := by
  classical
  ext d
  let N := d.degree + 2
  let g : Polynomial R := PowerSeries.trunc N f
  have he (e : σ →₀ ℕ) (he : e.degree < N) :
      coeff e (f.subst a) = coeff e ((g : PowerSeries R).subst a) := by
    apply coeff_subst_eq_of_coeff_le _ _ _ ha
    intro n hn
    exact (PowerSeries.coeff_coe_trunc_of_lt (by omega : n < N)).symm
  have he' (e : σ →₀ ℕ) (he : e.degree ≤ d.degree) :
      coeff e ((PowerSeries.derivative f).subst a) =
        coeff e ((PowerSeries.derivative (g : PowerSeries R)).subst a) := by
    apply coeff_subst_eq_of_coeff_le _ _ _ ha
    intro n hn
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative]
    congr 1
    exact (PowerSeries.coeff_coe_trunc_of_lt (by omega : n+1 < N)).symm
  rw [coeff_pderiv, he _ (by simp [N, map_add, Finsupp.degree_single]),
    ← coeff_pderiv, pderiv_subst_coe g a (PowerSeries.HasSubst.of_constantCoeff_zero ha),
    coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro ef hef
  rw [he' ef.1]
  have heq := Finset.HasAntidiagonal.mem_antidiagonal.mp hef
  have := congrArg Finsupp.degree heq
  rw [map_add] at this
  omega

lemma pderiv_map {S : Type*} [CommRing S] (ρ : R →+* S)
    (f : MvPowerSeries σ R) (i : σ) :
    pderiv i (f.map ρ) = (pderiv i f).map ρ := by
  ext d
  simp only [coeff_pderiv, coeff_map, map_mul, map_add, map_natCast, map_one]

end HeightThree.PowerSeriesDifferential

end

end OAI
