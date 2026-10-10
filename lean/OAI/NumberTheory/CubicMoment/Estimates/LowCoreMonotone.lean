import OAI.NumberTheory.CubicMoment.Estimates.LowCoreMellinIntegral

namespace OAI

/-! Monotonicity permits the harmless enlargement of a zero logarithmic
core exponent without changing the actual frequency set being estimated. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma lowNoncubeSupport_mono {V₁ V₂ J₁ J₂ : ℝ} (hV : V₁ ≤ V₂) (hJ : J₁ ≤ J₂) :
    lowNoncubeSupport V₁ J₁ ⊆ lowNoncubeSupport V₂ J₂ := by
  intro h hh
  obtain ⟨hi,hn⟩ := Finset.mem_filter.mp hh
  obtain ⟨⟨v,j⟩,hvj,he⟩ := Finset.mem_image.mp hi
  have hv := mem_nonzeroNormBall.mp (Finset.mem_product.mp hvj).1
  have hj := mem_nonzeroNormBall.mp (Finset.mem_product.mp hvj).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_image.mpr ⟨(v,j),Finset.mem_product.mpr ⟨?_,?_⟩,he⟩,hn⟩
  · exact mem_nonzeroNormBall.mpr ⟨hv.1.trans hV,hv.2⟩
  · exact mem_nonzeroNormBall.mpr ⟨hj.1.trans hJ,hj.2⟩

theorem low_core_mellin_integral_all_exponents (hSW : KummerPrimeSiegelWalfisz)
    {C R c d₁ d₂ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hR : 1 ≤ R) (hc : 0 < c) (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂)
    {L : γ → ℝ} {W : γ → ι → ℝ → ℂ}
    (hW : LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2))
    (hlo : ∀ r i x, x < 1 → W r i x = 0) (hhi : ∀ r i x, R < x → W r i x = 0)
    (M : ℝ) (hM : 0 < M) (V : ℝ → ℂ) (hV : HasCompactSupport V)
    (hV' : ContDiff ℝ ∞ V) (a k U q : ℕ) :
    ∃ K T₀ : ℝ, 0 ≤ K ∧ ∀ (r : γ) (X : ι → ℝ) (J : ℝ) (H : Finset Eisenstein),
      T₀ ≤ L r → (∏ i, X i) = L r → (∀ i, (L r)^c ≤ X i) →
      0 ≤ J → J ≤ (L r)^d₂ → H ⊆ lowNoncubeSupport ((Real.log (L r))^a) J →
      ∀ (e : Eisenstein) (u ρ : ℝ), e ≠ 0 → norm e ≤ (L r)^d₁ →
      |u| ≤ (1+Real.log (L r))^U → 0 ≤ ρ →
      (1+ρ)^q*(∫ t : ℝ, ‖arithmeticMellinCoefficient M hM V hV hV' ρ t‖*
        fullStructuredHeightMass R H 1 e 0 u (W r) X t) ≤
          K*J*(L r)^2/(1+Real.log (L r))^k := by
  obtain ⟨K,T₀,hK,hb⟩ := low_core_mellin_integral_saving hSW hMV hC hR hc hd₁ hd₂
    hW hlo hhi M hM V hV hV' (a+1) k U q (by omega)
  refine ⟨K,max T₀ (Real.exp 1),hK,?_⟩
  intro r X J H hT hprod hX hJ hJL hH e u ρ he heN hu hρ
  have hL : 0 < L r := zero_lt_one.trans_le (hW.length_one (r,Classical.arbitrary ι))
  have hlog : 1 ≤ Real.log (L r) :=
    (Real.le_log_iff_exp_le hL).mpr ((le_max_right _ _).trans hT)
  have hm := lowNoncubeSupport_mono
    (pow_le_pow_right₀ hlog (Nat.le_succ a)) (le_refl J)
  exact hb r X J H ((le_max_left _ _).trans hT) hprod hX hJ hJL
    (hH.trans hm) e u ρ he heN hu hρ

end CubicFirstMoment

end

end OAI
