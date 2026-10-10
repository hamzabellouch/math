import OAI.NumberTheory.CubicMoment.Transform.MetaplecticRetainedMean

namespace OAI

/-! Coefficient conjugation supplies the opposite height orientation.
The literal published coefficient support is preserved under conjugation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

private lemma star_real_complex (x : ℝ) : star (x:ℂ) = (x:ℂ) :=
  Complex.conj_ofReal x

lemma star_metaplecticLocalCoefficient (r : Eisenstein) (n : MetaplecticDualArgument) :
    star (metaplecticLocalCoefficient r n) = metaplecticLocalCoefficient r n := by
  simp only [metaplecticLocalCoefficient,star_prod,star_real_complex]

lemma star_complexAngular {z : ℂ} (hz : z ≠ 0) (ℓ : ℤ) :
    star (complexAngular ℓ z) = complexAngular (-ℓ) z := by
  rw [show complexAngular (-ℓ) z = (complexAngular ℓ z)⁻¹ by
    simp only [complexAngular,zpow_neg]]
  exact (Complex.inv_eq_conj (norm_complexAngular hz ℓ)).symm

def metaplecticConjugateCoefficients
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein)
    (n : MetaplecticDualArgument) : ℂ := star (a r n)

lemma MetaplecticCoefficientBounds.conjugate
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a) :
    MetaplecticCoefficientBounds (metaplecticConjugateCoefficients a) := by
  obtain ⟨C,hC,hb⟩ := ha
  refine ⟨C,hC,?_⟩
  intro r hr hsr n hn
  have he : metaplecticConjugateCoefficients a r n*metaplecticLocalCoefficient r n =
      star (a r n*metaplecticLocalCoefficient r n) := by
    rw [star_mul,star_metaplecticLocalCoefficient]
    dsimp [metaplecticConjugateCoefficients]
    ring
  have hraw : a r n*metaplecticLocalCoefficient r n ≠ 0 := by
    intro hz
    apply hn
    rw [he,hz,star_zero]
  obtain ⟨j,ζ,h,h',w,hj,hh,hh',hw,hdiv,hdiv',hwr,hsq,hfreq,hbound⟩ := hb r hr hsr n hraw
  refine ⟨j,ζ,h,h',w,hj,hh,hh',hw,hdiv,hdiv',hwr,hsq,hfreq,?_⟩
  simpa only [metaplecticConjugateCoefficients,norm_star] using hbound

lemma star_metaplecticNormalizedDualCoefficient
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (nd : MetaplecticDualArgument × PrimaryArgument) :
    star (metaplecticNormalizedDualCoefficient a r ℓ nd) =
      metaplecticNormalizedDualCoefficient (metaplecticConjugateCoefficients a) r (-ℓ) nd := by
  have hz : ((nd.2:Eisenstein)^3:ℂ)*metaplecticFrequency nd.1 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (fun h => primary_ne_zero nd.2.property (Subtype.ext h)))
      (metaplecticFrequency_ne_zero nd.1)
  unfold metaplecticNormalizedDualCoefficient
  split_ifs
  · simp only [star_mul,star_div₀,star_metaplecticLocalCoefficient,
      star_complexAngular hz,neg_neg,star_real_complex,metaplecticConjugateCoefficients]
    ring
  · simp only [star_zero]

lemma metaplectic_opposite_polynomial_norm
    (a : Eisenstein → MetaplecticDualArgument → ℂ) (r : Eisenstein) (ℓ : ℤ)
    (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (τ t : ℝ) :
    ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*mellinPhase (τ+t) (metaplecticDualNorm nd)‖ =
      ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient (metaplecticConjugateCoefficients a) r (-ℓ) nd*
        mellinPhase (-τ-t) (metaplecticDualNorm nd)‖ := by
  rw [←norm_star (∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
    mellinPhase (τ+t) (metaplecticDualNorm nd))]
  simp only [star_sum,star_mul,star_metaplecticNormalizedDualCoefficient,star_mellinPhase,
    show -(τ+t) = -τ-t by ring,mul_comm]

theorem metaplectic_actual_retained_plus_mean
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (ha : MetaplecticCoefficientBounds a)
    {ε M : ℝ} (hε : 0 < ε) (hMV : MontgomeryVaughanBound M) (hM : 0 ≤ M) :
    ∃ D : ℝ, 0 < D ∧ ∀ r : Eisenstein, primary r → Squarefree r →
      ∀ (S : Finset (MetaplecticDualArgument × PrimaryArgument)) (J T : ℝ),
      0 < J → 0 < T → (∀ nd ∈ S, metaplecticDualNorm nd ≤ J) →
      ∀ (ℓ : ℤ) (τ : ℝ),
      ((∫ t in T..2*T, ‖∑ nd ∈ S, metaplecticNormalizedDualCoefficient a r ℓ nd*
        mellinPhase (τ+t) (metaplecticDualNorm nd)‖)/T)/Real.sqrt (norm r) ≤
          ((Nat.log 2 ⌊3*J⌋₊+1:ℕ):ℝ)*D*(6*J)^(3*ε/2)*norm r^(2*ε)*
            (1+Real.sqrt (4*J/(norm r*T))) := by
  obtain ⟨D,hD,hb⟩ := metaplectic_actual_retained_mean ha.conjugate hε hMV hM
  refine ⟨D,hD,?_⟩
  intro r hr hsr S J T hJ hT hS ℓ τ
  simp_rw [metaplectic_opposite_polynomial_norm]
  exact hb r hr hsr S J T hJ hT hS (-ℓ) (-τ)

end CubicFirstMoment

end

end OAI
