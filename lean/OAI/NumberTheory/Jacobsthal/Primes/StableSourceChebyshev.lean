import OAI.NumberTheory.Jacobsthal.Probability.StableSourceVariance

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


open _root_.Filter
namespace ErdosRandomVariance

universe u

theorem stable_source_chebyshev (delta eps : ℝ) (hdelta : 0 < delta) (heps : 0 < eps) :
    ∀ᶠ W : ℝ in atTop, 1 < W ∧ ∀ (J : ℕ), W^delta ≤ (J : ℝ) →
      ∀ (α : Type u) (C : Finset α) (w : α → ℝ) (I : ℕ → α → ℝ) (zeta eta : ℝ),
      (∀ x ∈ C, 0 ≤ w x) → 0 ≤ zeta → zeta ≤ 1 → 0 < eta →
      (∀ j ∈ Finset.range J, ∀ x ∈ C, I j x = 0 ∨ I j x = 1) →
      (∑ x ∈ C, w x) ≤ 1+zeta →
      (∀ j ∈ Finset.range J, (1-zeta)*sieveProduct (variancePrimes W) ≤ weightedMoment C w (I j)) →
      (∀ j ∈ Finset.range J, weightedMoment C w (I j) ≤ (1+zeta)*sieveProduct (variancePrimes W)) →
      (∀ i ∈ Finset.range J, ∀ j ∈ Finset.range J, i ≠ j →
        weightedMoment C w (fun x => I i x*I j x) ≤ (1+zeta)*pairKernel (variancePrimes W) i j) →
      (∑ x ∈ C with eta*((J : ℝ)*sieveProduct (variancePrimes W)) ≤
        |indicatorSum (Finset.range J) I x-(J : ℝ)*sieveProduct (variancePrimes W)|, w x) ≤
        (eps+4*zeta)/eta^2 := by
  classical
  filter_upwards [stable_source_variance delta eps hdelta heps] with W hW
  refine ⟨hW.1,?_⟩
  intro J hJ α C w I zeta eta hw hzeta hzeta1 heta hI hMass hLower hUpper hPair
  have hJpos : (0 : ℝ) < J := lt_of_lt_of_le
    (Real.rpow_pos_of_pos (show 0 < W by linarith [hW.1]) delta) hJ
  have hM := mul_pos hJpos (sieveProduct_pos _ (variancePrimes_prime W))
  exact weighted_relative_chebyshev C w (indicatorSum (Finset.range J) I)
    ((J : ℝ)*sieveProduct (variancePrimes W)) eta (eps+4*zeta) hw hM heta
    (hW.2 J hJ α C w I zeta hzeta hzeta1 hI hMass hLower hUpper hPair)

end ErdosRandomVariance


end Erdos970

end OAI
