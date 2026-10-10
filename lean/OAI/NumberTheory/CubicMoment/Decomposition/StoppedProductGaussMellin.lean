import OAI.NumberTheory.CubicMoment.Decomposition.StoppedProductMellinSplit

namespace OAI

/-! Transfer the full signed Schwartz-height estimate to the actual
product Mellin weight, with independent norm phases on both coefficients. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem gauss_mellin_complement_log_saving
    (hpnt : PrimaryPrimePNT) {C Mα Mβ M : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ) (hM : 0 ≤ M)
    (j dα dβ a : ℕ) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hpos : tsupport V ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ V) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (P B : Finset Eisenstein) (α β : Eisenstein → ℂ) (Z A X S u : ℝ),
      (65536:ℝ)^2 ≤ Z → 2*Z^(3/2:ℝ) ≤ A →
      A ≤ Z^2*(1+Real.log Z)^(3*a) → 0 < X →
      (1+Real.log Z)^Ct ≤ S →
      (∀ n ∈ P, primary n ∧ 1 ≤ norm n/A ∧ norm n/A ≤ 2) →
      (∀ n ∈ B, primary n ∧ Squarefree n ∧ Z/2 ≤ norm n ∧ norm n ≤ Z) →
      (∀ n ∈ B, ‖β n‖ ≤ M) →
      (∑ n ∈ P, ‖α n‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ n ∈ B, ‖β n‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      ‖∫ τ : ℝ, (1-(heightPartitionBump (τ/S):ℂ))*zeroLineMellinWeight V X τ*
        ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist (u-τ) (c*b)‖ ≤
        K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(S*(1+Real.log Z)^j) := by
  obtain ⟨K,Ct,hK,hbound⟩ := schwartz_gauss_complement_log_saving hpnt hMV hC hHuxley
    hMα hMβ hM j dα dβ a (reflectedZeroMellinProfile V hV hpos hsm)
  refine ⟨K,Ct,hK,?_⟩
  intro P B α β Z A X S u hZ hA hAu hX hS hP hB hβ hαE hβE
  let αu := fun c => α c*normTwist u c
  let βu := fun b => β b*normTwist u b
  have hαu : (∑ c ∈ P, ‖αu c‖^2) ≤ Mα*A*(1+Real.log Z)^dα := by
    simpa only [αu,norm_twisted_coefficient] using hαE
  have hβu : (∑ b ∈ B, ‖βu b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ := by
    simpa only [βu,norm_twisted_coefficient] using hβE
  have hu (b : Eisenstein) (hb : b ∈ B) : ‖βu b‖ ≤ M := by
    simpa only [βu,norm_twisted_coefficient] using hβ b hb
  have hh := hbound P B αu βu Z A X S hZ hA hAu hX hS hP hB hu hαu hβu
  have he : (∫ τ : ℝ, (1-(heightPartitionBump (τ/S):ℂ))*zeroLineMellinWeight V X τ*
      ∑ c ∈ P, ∑ b ∈ B, α c*β b*gauss (c*b)*normTwist (u-τ) (c*b)) =
      ∫ t : ℝ, (1-(heightPartitionBump (t/S):ℂ))*reflectedZeroMellinProfile V hV hpos hsm t*
        Complex.exp ((-Real.log X*t:ℝ)*Complex.I)*
        ∑ c ∈ P, ∑ b ∈ B, αu c*βu b*gauss (c*b)*normTwist t (c*b) := by
    rw [←integral_neg_eq_self]
    apply integral_congr_ae
    filter_upwards with t
    rw [neg_div,heightPartitionBump.neg,zeroLineMellinWeight_reflected_phase V hV hpos hsm hX,
      sub_neg_eq_add,gaussProduct_shift P B α β
        (fun c hc => (hP c hc).1) (fun b hb => (hB b hb).1)]
    dsimp only [αu,βu]
    ring
  rw [he]
  exact hh

end CubicFirstMoment

end

end OAI
