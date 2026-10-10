import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeSliceMoments

namespace OAI

/-! The three published sieve orientations applied to the actual common-factor quotient row. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem fullPrime_slice_three_sieve (hHuxley : HuxleyAdditiveLargeSieve)
    {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
    ∀ (W : ι → ℝ → ℂ) (X : ι → ℝ) (f e v : Eisenstein) (ℓ : ℤ) (u : ℝ)
      (Ram S T J H : Finset Eisenstein) (N U V : ℝ),
      (∏ i, X i)/norm f = N → 1 ≤ N → 1 ≤ U → 1 ≤ V →
      (∀ s ∈ S, primary s ∧ Squarefree s ∧ norm s ≤ U) →
      (∀ t ∈ T, primary t ∧ Squarefree t ∧ norm t ≤ V) →
      H ⊆ coprimeResidualSupport Ram J (coprimePairs S T) →
      (∑ h ∈ H, ‖fullPrimeSliceSum R W X f e h v ℓ u‖^2) ≤
        min ((Ram.card:ℝ)*J.card*C₁ *
          min ((T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)))
              ((S.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ))))
          ((Ram.card:ℝ)*J.card*C₂*(U*V)^ε*((U*V)^2+N)) *
            ∑ n ∈ fullPrimeSliceSupport R W X f e, ‖fullPrimeCoefficient R W X (f*n)‖^2 := by
  obtain ⟨C₁,C₂,hC₁,hC₂,hbound⟩ := dilated_noncube_three_sieve_bounds
    hHuxley (one_le_pow₀ hR : 1 ≤ R^Fintype.card ι) hε
  refine ⟨C₁,C₂,hC₁,hC₂,?_⟩
  intro W X f e v ℓ u Ram S T J H N U V hN hN1 hU hV hS hT hH
  let β := fun n => fullPrimeCoefficient R W X (f*n)*theta ℓ n*
    mellinPhase u (norm n)*cubicSymbol n v
  have hb : ∀ n ∈ fullPrimeSliceSupport R W X f e,
      primary n ∧ Squarefree n ∧ norm n ≤ R^Fintype.card ι*N := by
    intro n hn
    have hh := fullPrimeSliceSupport_bounds R W X f e hn
    refine ⟨hh.1,hh.2.1,hh.2.2.2.trans_eq ?_⟩
    rw [← hN]
    ring
  have heq (h : Eisenstein) : fullPrimeSliceSum R W X f e h v ℓ u =
      ∑ n ∈ fullPrimeSliceSupport R W X f e, β n*cubicSymbol n h := by
    unfold fullPrimeSliceSum
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [β]
    rw [cubicSymbol_mul_upper (hb n hn).1]
    ring
  simp_rw [heq]
  apply (hbound _ Ram S T J H N U V hN1 hU hV hb hS hT hH β).trans
  apply mul_le_mul_of_nonneg_left (fullPrime_slice_twisted_energy R W X f e v ℓ u)
  have hUN : 0 ≤ (U*N)^ε := Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hU) (zero_le_one.trans hN1)) _
  have hVN : 0 ≤ (V*N)^ε := Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hV) (zero_le_one.trans hN1)) _
  have hUV : 0 ≤ (U*V)^ε := Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hU) (zero_le_one.trans hV)) _
  have hleft : 0 ≤ (T.card:ℝ)*(U*N)^ε*(U+N+(U*N)^(2/3:ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hUN)
      (add_nonneg (add_nonneg (zero_le_one.trans hU) (zero_le_one.trans hN1)) (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hU) (zero_le_one.trans hN1)) _))
  have hright : 0 ≤ (S.card:ℝ)*(V*N)^ε*(V+N+(V*N)^(2/3:ℝ)) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hVN)
      (add_nonneg (add_nonneg (zero_le_one.trans hV) (zero_le_one.trans hN1)) (Real.rpow_nonneg (mul_nonneg (zero_le_one.trans hV) (zero_le_one.trans hN1)) _))
  have hpre₁ : 0 ≤ (Ram.card:ℝ)*J.card*C₁ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hC₁.le
  have hpre₂ : 0 ≤ (Ram.card:ℝ)*J.card*C₂ :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hC₂.le
  exact le_min (mul_nonneg hpre₁ (le_min hleft hright))
    (mul_nonneg (mul_nonneg hpre₂ hUV) (add_nonneg (sq_nonneg _) (zero_le_one.trans hN1)))

end CubicFirstMoment

end

end OAI
