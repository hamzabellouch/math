import OAI.NumberTheory.CubicMoment.Estimates.ShortConvolutionTypeILow
import OAI.NumberTheory.CubicMoment.Estimates.TypeIHeightRanges

namespace OAI

/-! The short-convolution Type-I estimates for the prime
decomposition: low-height comparison and both signed high-height ranges.
All coefficient masses and divisor bounds are derived for the literal convolution. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem short_convolution_typeI_height_ranges
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    {F : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hGrowth : MetaplecticPolynomialGrowth F) (hHB : MetaplecticMeanSquare F)
    {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4) (M : ℕ) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ (w : Eisenstein → γ)
      (F₀ : ℝ) (X : ι → ℝ) (A : ι → EisensteinArithmeticFunction)
      (u : ι → Eisenstein → ℂ) (R U T : ℝ) (P : Finset Eisenstein),
      (∀ i, ShortArithmeticFactor F₀ (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (2*X i), ‖u i a‖ ≤ 1) →
      1 ≤ R → 1 ≤ U → 2 ≤ R*U → 1 ≤ Real.log (R*U) → Real.log (R*U) ≤ T →
      ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
        (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
      (∏ i, X i) ≤ R → P ⊆ orderedConvolutionSupport (fun i => primaryElementBall (2*X i)) →
      (∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      let α := orderedConvolution (fun i => primaryElementBall (2*X i))
        (fun i b => ((MvPowerSeries.coeff (idealExponentOf b) (A i):ℝ):ℂ)*u i b)
      ((∫ t in T..2*T, ∑ r ∈ P, ‖α r‖*‖metaplecticSmoothSum r (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ∑ r ∈ P, ‖α r‖*‖metaplecticSmoothSum r (W (w r)) U t‖))/T ≤
        C*(R*U)^(5/6-min (1/100) (3*κ/16))+
          E*(R*U)^(5/6:ℝ)/(Real.log (R*U))^M := by
  let K : ℝ := ((36*(1+Real.log 2))*(1+1/Real.log 2))^(Fintype.card ι)
  have hK : 0 ≤ K := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [K]
    positivity
  obtain ⟨C,E,hC,hE,hbound⟩ := typeI_selected_height_ranges hW hF hGrowth hHB
    hκ hρ (Fintype.card ι) M hK
  refine ⟨C,E,hC,hE,?_⟩
  intro w F₀ X A u R U T P hA hX hu hR hU hRU hlog hLT hrange hprod hP hlevels
  exact hbound w P _ R U T hR hU hlog hLT hrange hlevels
    (short_dyadic_mass_for_typeI F₀ X A u hA hX hu hR hU hRU hprod P hP)

theorem short_convolution_angular_typeI_height_ranges
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMV0 : 0 ≤ MV)
    {γ : Type*} {W : γ → ℝ → ℂ} (hW : UniformLogWeights W)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0) {κ ρ : ℝ} (hκ : 0 < κ) (hρ : ρ ≤ κ/4) :
    ∃ (mpos mneg : ℕ) (C : ℝ), 2 ≤ mpos ∧ 2 ≤ mneg ∧ 0 ≤ C ∧
      ∀ (w : Eisenstein → γ) (F₀ : ℝ) (X : ι → ℝ)
        (A : ι → EisensteinArithmeticFunction) (u : ι → Eisenstein → ℂ)
        (R U T : ℝ) (P : Finset Eisenstein),
      (∀ i, ShortArithmeticFactor F₀ (A i)) → (∀ i, 1 ≤ X i) →
      (∀ i, ∀ a ∈ primaryElementBall (2*X i), ‖u i a‖ ≤ 1) →
      1 ≤ R → 1 ≤ U → max 2 (Real.exp hW.radius) ≤ R*U → 1 ≤ T → T ≤ (R*U)^2 →
      ((R ≤ (R*U)^(2/5:ℝ) ∧ T ≤ (R*U)^(1/100:ℝ)) ∨
        (R ≤ (R*U)^(1/3-κ/2) ∧ T ≤ (R*U)^(1/6+ρ))) →
      (∏ i, X i) ≤ R → P ⊆ orderedConvolutionSupport (fun i => primaryElementBall (2*X i)) →
      (∀ r ∈ P, primary r ∧ R ≤ norm r ∧ norm r ≤ 2*R) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mpos:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((mneg:ℝ)-1/2)) →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((mneg:ℝ)-1/2)) →
      let α := orderedConvolution (fun i => primaryElementBall (2*X i))
        (fun i b => ((MvPowerSeries.coeff (idealExponentOf b) (A i):ℝ):ℂ)*u i b)
      ((∫ t in T..2*T, ∑ r ∈ P, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖)+
        (∫ t in -(2*T)..-T, ∑ r ∈ P, ‖α r‖*‖metaplecticAngularSmoothSum r ℓ (W (w r)) U t‖))/T ≤
        C*(R*U)^(5/6-min (1/100) (3*κ/16)) := by
  let K : ℝ := ((36*(1+Real.log 2))*(1+1/Real.log 2))^(Fintype.card ι)
  have hK : 0 ≤ K := by
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [K]
    positivity
  obtain ⟨mp,mn,C,hmp,hmn,hC,hbound⟩ := angular_typeI_selected_height_ranges
    hV hMV hMV0 hW ℓ hℓ hκ hρ (Fintype.card ι) hK
  refine ⟨mp,mn,C,hmp,hmn,hC,?_⟩
  intro w F₀ X A u R U T P hA hX hu hR hU hsize hT hTX hrange hprod hP hlevels hgmp hgpp hgmn hgpn
  exact hbound w P _ R U T hR hU hsize hT hTX hrange hlevels
    (short_dyadic_mass_for_typeI F₀ X A u hA hX hu hR hU
      ((le_max_left _ _).trans hsize) hprod P hP) hgmp hgpp hgmn hgpn

end CubicFirstMoment

end

end OAI
