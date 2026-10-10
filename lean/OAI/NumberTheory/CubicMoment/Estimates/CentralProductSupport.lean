import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductDetector
import OAI.NumberTheory.CubicMoment.Decomposition.DistinguishedNoStop

namespace OAI

/-! The smooth product kernel permits the exact detector support to be
replaced by its full squarefree envelope. No nonzero term is removed. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def centralProductEnvelope (X : ℝ) : Finset Eisenstein :=
  squarefreeProductEnvelope (Real.exp primeProductWeights.radius*X)

lemma centralProductEnvelope_spec {X : ℝ} {n : Eisenstein}
    (hn : n ∈ centralProductEnvelope X) :
    primary n ∧ Squarefree n ∧ norm n ≤ Real.exp primeProductWeights.radius*X := by
  obtain ⟨hn,hs⟩ := Finset.mem_filter.mp hn
  exact ⟨(mem_primaryElementBall.mp hn).1,hs,(mem_primaryElementBall.mp hn).2⟩

theorem central_product_support_sum (c : Eisenstein → ℂ) (ℓ : ℤ) (H T : ℝ)
    {X : ℝ} (hX : 0 < X) :
    (∑ n ∈ primeProductSupport X, c n*centeredHeightKernel ℓ primeProductEnvelope H T X X n) =
      ∑ n ∈ centralProductEnvelope X, c n*centeredHeightKernel ℓ primeProductEnvelope H T X X n := by
  apply Finset.sum_congr_of_eq_on_inter
  · intro n hn hout
    have hs := primeProductSupport_spec hn
    have hsize : Real.exp primeProductWeights.radius*X < norm n := lt_of_not_ge
      (fun hb => hout (Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hs.1,hb⟩,hs.2.1⟩))
    have hz := primeProductWeights.upper_support () (norm n/X) ((lt_div_iff₀ hX).mpr hsize)
    simp only [centeredHeightKernel,hz,mul_zero,zero_mul]
  · intro n hn hout
    have hs := centralProductEnvelope_spec hn
    have hz : primeProductEnvelope (norm n/X) = 0 := by
      by_cases hu : norm n ≤ 3*X
      · have hl : norm n < X/2 := lt_of_not_ge (fun hl => hout (Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨mem_primaryElementBall.mpr ⟨hs.1,hu⟩,hs.2.1⟩,hl⟩))
        exact primeProductEnvelope_zero_lower ((div_le_iff₀ hX).mpr (by linarith))
      · exact primeProductEnvelope_zero ((le_div_iff₀ hX).mpr (le_of_lt (lt_of_not_ge hu)))
    simp only [centeredHeightKernel,hz,mul_zero,zero_mul]
  · intro n _ _
    rfl

lemma centralRoughProduct_full (ℓ : ℤ) (H T : ℝ) {X : ℝ} (hX : 0 < X) :
    centralRoughProduct ℓ H T X =
      ∑ n ∈ centralProductEnvelope X,
        (roughProduct primeDetectorCutoff (X^(2/5:ℝ)) n:ℂ)*
          centeredHeightKernel ℓ primeProductEnvelope H T X X n :=
  central_product_support_sum _ ℓ H T hX

end CubicFirstMoment

end

end OAI
