import OAI.NumberTheory.CubicMoment.Estimates.DivisorNoncubeDyadic
import OAI.NumberTheory.CubicMoment.Angular.AngularDivisorNoncubeAnnulus
import OAI.NumberTheory.CubicMoment.Estimates.PoissonDyadicSum

namespace OAI

/-! Sum the actual effective-frequency annuli of a square-divisor block.
Their natural scale gives an additional reciprocal divisor norm. -/
noncomputable section
open scoped BigOperators ContDiff
open Filter
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)

variable {γ ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem angular_divisor_noncube_dyadic_saving (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C c R : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k U : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ K T₀ : ℝ, 0 < K ∧ ∀ (r : γ) (X : ι → ℝ) (A : ℝ)
      (I : Finset ℕ) (H : ℕ → Finset Eisenstein) (d e : Eisenstein) (u : ℝ),
      T₀ ≤ L r → (∏ i, X i) = L r → (∀ i, (2*L r)^c < X i) → 0 < A → d ≠ 0 →
      (∀ j ∈ I, 2*(2:ℝ)^j ≤ (L r)^(1+η)) →
      (∀ j ∈ I, ∀ h ∈ H j, d*h ∈ frequencyDyad j ∧ ¬∃ z : Eisenstein, z^3 = d*h) →
      e ≠ 0 → norm e ≤ (L r)^σ → |u| ≤ (1+Real.log (L r))^U →
      ‖∑ j ∈ I, finiteDivisorPoissonContribution d
        (fullSquarefreePrimeSupport R (W r) X e) (H j)
        (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        K*A^(2/3:ℝ)*(L r)^(5/3:ℝ)/(norm d*(1+Real.log (L r))^k) := by
  obtain ⟨η,σ,hη,hη₁,hσ,hbound⟩ := angular_divisor_noncube_annulus_saving ℓ
    (γ := γ) (ι := ι) hSW hℓ hpub hHuxley hperiod hMV hC hc hc₁ hR hGI hGQ V hV hV' k U 3
  refine ⟨η,σ,hη,hη₁,hσ,?_⟩
  intro L W hL hW hlo hhi
  obtain ⟨K,T₀,hK,hbound⟩ := hbound L W hL hW hlo hhi
  let D := SevenEighths.CubicDyadicDecay.decayConstant (1/3)
  have hD : 0 < D := SevenEighths.CubicDyadicDecay.decayConstant_pos _ (by norm_num) (by norm_num)
  refine ⟨3*K*(2:ℝ)^(1/3:ℝ)*D,T₀,by positivity,?_⟩
  intro r X A I H d e u hT hprod hX hA hd hI hH he heN hu
  have hLp : 0 < L r := zero_lt_one.trans_le (hL r)
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hz : 0 < 1+Real.log (L r) := by linarith [Real.log_nonneg (hL r)]
  let t := A/(27*(norm d)^3*(L r)^2)
  have ht : 0 < t := by dsimp [t]; positivity
  let C₀ := K*A*L r*(2:ℝ)^(1/3:ℝ)/((norm d)^2*(1+Real.log (L r))^k)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hrow (j : ℕ) (hj : j ∈ I) :
      ‖finiteDivisorPoissonContribution d (fullSquarefreePrimeSupport R (W r) X e)
        (H j) (angularHeightPrimeCoefficient ℓ R (W r) X) u V A‖ ≤
        C₀*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := by
    have hJ : 0 < (2:ℝ)^j := by positivity
    have hb := hbound r X A (2*(2:ℝ)^j) ((2:ℝ)^j) (H j) d e u
      hT hprod hX hA (by have := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j); linarith)
      (hI j hj) hJ hd
      (fun h hh => ⟨(mem_frequencyDyad.mp (hH j hj h hh).1).1,
        (frequencyDyad_norm (hH j hj h hh).1).2,(hH j hj h hh).2⟩)
      (fun h hh => frequencyDyad_norm (hH j hj h hh).1) he heN hu
    have heq : A*(2:ℝ)^j/(27*(norm d)^3*(L r)^2) = t*2^j := by dsimp [t]; ring
    rw [heq,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hJ.le] at hb
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+t*(2:ℝ)^j) 3)).mpr
    dsimp only [C₀]
    convert hb using 1 <;> ring
  have hs := finite_cubic_dyadic_sum I _ hC₀ ht hrow
  apply hs.trans_eq
  calc
    _ = (K*(2:ℝ)^(1/3:ℝ)*D/(1+Real.log (L r))^k)*
        ((A*L r/(norm d)^2)*(A/(27*(norm d)^3*(L r)^2))^(-(1/3:ℝ))) := by
      dsimp [C₀,t,D]
      ring
    _ = _ := by rw [divisor_cubic_poisson_scale hA hLp hdN]; ring

end CubicFirstMoment

end

end OAI
