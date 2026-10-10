import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedCoefficient
import OAI.NumberTheory.CubicMoment.Angular.AngularStoppedDivisorAnnulus
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorDyadic
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorAnnulus
import OAI.NumberTheory.CubicMoment.Estimates.DivisorNoncubeDyadic

namespace OAI

/-! The actual stopped effective-frequency annuli sum with a reciprocal
square-divisor norm. The principal-frequency test remains at d*h. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_stopped_divisor_noncube_dyadic
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate)
    (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {ξ κ E F J : ℝ} (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hκ : 0 < κ)
    (hF : 0 ≤ F) (hJ : 0 ≤ J)
    (Φ : ℝ → ℂ) (hΦ : HasCompactSupport Φ) (hΦ' : ContDiff ℝ ∞ Φ)
    (k H : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (δ b u V A : ℝ), 0 < δ → δ ≤ 1 → (Real.log X)^(-J) ≤ δ →
      2 ≤ b → X^κ ≤ b → b ≤ X →
      0 ≤ V → |u| ≤ (Real.log X)^H → 1+V ≤ (Real.log X)^F →
      ∀ W : ι → ℝ → ℂ, (∀ i x, ‖W i x‖ ≤ 1) → (∀ i, ContDiff ℝ ∞ (W i)) →
      (∀ i x, 0 < x → ‖deriv (W i) x‖*x ≤ V) → 0 < A →
      ∀ (I : Finset ℕ) (d : Eisenstein) (Qf : ℕ → Finset Eisenstein), d ≠ 0 →
      (∀ j ∈ I, 2*(2:ℝ)^j ≤ b^(3/5:ℝ)) →
      (∀ j ∈ I, ∀ v ∈ Qf j, d*v ∈ frequencyDyad j ∧ ¬∃ z : Eisenstein, z^3 = d*v) →
      ∀ e : Eisenstein, e ≠ 0 → norm e ≤ X^E →
      ∀ (j₀ k₀ h : ℕ) (Z Q : ℝ) (early : Bool), j₀ ≤ h →
      2 < min (X^ξ) (geometricBinLower (1+δ) X h) →
      2*(Real.log X)^(2*(4*(k+2)+k)) ≤
        min (X^ξ) (geometricBinLower (1+δ) X h) →
      ‖∑ j ∈ I, finiteDivisorPoissonContribution d
        (stoppedIntervalSupport ι X (b/2) b e) (Qf j)
        (angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
          (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
            j₀ k₀ h Z Q early)) u Φ A‖ ≤
        K*A^(2/3:ℝ)*b^(5/3:ℝ)/(norm d*(Real.log X)^k) := by
  obtain ⟨K,hK,hannulus⟩ := angular_stopped_divisor_noncube_poisson_annulus (ι := ι) (E := E)
    hpnt hEF ℓ hℓ hMV hC hHuxley hξ hξz hκ hF hJ Φ hΦ hΦ' k 3 H
  let D := SevenEighths.CubicDyadicDecay.decayConstant (1/3)
  have hD : 0 < D := SevenEighths.CubicDyadicDecay.decayConstant_pos _ (by norm_num) (by norm_num)
  refine ⟨3*K*(2:ℝ)^(1/3:ℝ)*D,by positivity,?_⟩
  filter_upwards [hannulus,eventually_ge_atTop (Real.exp 1)] with X hannulus hX
  intro δ b u V A hδ hδone hwidth hb2 hb hbX hV hu hVF W hW hWi hWd hA
    I d Qf hd hI hQf e he hNe j₀ k₀ h Z Q early hj hR hRL
  have hbp : 0 < b := by linarith
  have hdN : 0 < norm d := norm_pos_of_ne_zero hd
  have hz : 0 < Real.log X := by
    have hh := Real.log_le_log (Real.exp_pos 1) hX
    rw [Real.log_exp] at hh
    linarith
  let S := stoppedIntervalSupport ι X (b/2) b e
  let β := angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) 0 W
    (stoppedSideTest (geometricPrimeBin (1+δ) X) (geometricBinLower (1+δ) X)
      j₀ k₀ h Z Q early)
  let t := A/(27*(norm d)^3*(b/2)^2)
  let t₀ := A/(27*(norm d)^3*b^2)
  let C₀ := K*A*b*(2:ℝ)^(1/3:ℝ)/((norm d)^2*(Real.log X)^k)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht₀ : 0 < t₀ := by dsimp [t₀]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hrow (j : ℕ) (hjI : j ∈ I) :
      ‖finiteDivisorPoissonContribution d S (Qf j) β u Φ A‖ ≤
        C₀*((2:ℝ)^j)^(1/3:ℝ)/(1+t*2^j)^3 := by
    have hY : 0 < (2:ℝ)^j := by positivity
    have hh := hannulus δ b u V (2*(2:ℝ)^j) ((2:ℝ)^j) A hδ hδone hwidth
      hb2 hb hbX hV hu hVF
      (by have := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := j); linarith)
      (hI j hjI) W hW hWi hWd hY hA.le d hd (Qf j)
      (fun v hv => ⟨(mem_frequencyDyad.mp (hQf j hjI v hv).1).1,
        (frequencyDyad_norm (hQf j hjI v hv).1).2,(hQf j hjI v hv).2⟩)
      (fun v hv => frequencyDyad_norm (hQf j hjI v hv).1)
      e he hNe j₀ k₀ h Z Q early hj hR hRL
    have heq : A*(2:ℝ)^j/(27*(norm d)^3*(b/2)^2) = t*2^j := by dsimp [t]; ring
    rw [heq,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hY.le] at hh
    apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1+t*(2:ℝ)^j) 3)).mpr
    dsimp only [C₀]
    convert hh using 1 <;> ring
  have hs := finite_cubic_dyadic_sum I _ hC₀ ht hrow
  have htt : t₀ ≤ t := by
    apply div_le_div_of_nonneg_left hA.le (by positivity)
    exact mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg b] : (b/2)^2 ≤ b^2) (by positivity)
  have hp := Real.rpow_le_rpow_of_nonpos ht₀ htt (show -(1/3:ℝ) ≤ 0 by norm_num)
  apply (hs.trans (mul_le_mul_of_nonneg_left hp (mul_nonneg hC₀ hD.le))).trans_eq
  calc
    _ = (K*(2:ℝ)^(1/3:ℝ)*D/(Real.log X)^k)*
        ((A*b/(norm d)^2)*(A/(27*(norm d)^3*b^2))^(-(1/3:ℝ))) := by
      dsimp [C₀,t₀,D]
      ring
    _ = _ := by rw [divisor_cubic_poisson_scale hA hbp hdN]; ring

end CubicFirstMoment

end

end OAI
