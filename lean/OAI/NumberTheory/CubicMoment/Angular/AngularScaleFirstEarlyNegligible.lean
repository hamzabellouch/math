import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstStoppedEarly
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstEarlyNegligible
import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstStoppedAggregation
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedReduction

namespace OAI

/-! A single logarithmic boundary makes all finitely many early stopped
arities negligible. No boundary is chosen before the analytic constants. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_scaleFirstStoppedEarly_isLittleO (ℓ : ℤ) (m : ℕ)
    (hpnt : PrimaryPrimePNT) (hEF : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    {C ξ ρ ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100)
    (Ct : ℕ) :
    ∃ G : ℕ, ∀ (H : ℝ → ℝ) (h : ℝ → ℕ),
      (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (∀ᶠ X : ℝ in atTop,
        geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h X) →
      (∀ᶠ X : ℝ in atTop, 2*(Real.log X)^G ≤ min (X^ξ)
        (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X))) →
      (fun X => angular_scaleFirstStoppedSum ℓ m ρ ξ Ct (H X) X (h X) true)
        =o[atTop] firstMomentScale := by
  have hdata (i : Fin m) := angular_distinguishedStoppedDyad_early_bound ℓ i.val hpnt hEF hℓ hMV hC
    hHuxley hVor hGamma hξ hξz hρ hρ₂ hε hsmall hgap (i.val+8) Ct
  choose G K hK hb using hdata
  let G₀ := ∑ i : Fin m, G i
  refine ⟨G₀,?_⟩
  intro H h hH hh hrough
  unfold angular_scaleFirstStoppedSum
  apply Asymptotics.IsLittleO.fun_sum
  intro i hi
  let ii : Fin m := ⟨i,Finset.mem_range.mp hi⟩
  obtain ⟨D,hD,hagg⟩ := angular_distinguishedScaleStopped_bound ℓ i hρ
  have hGG : G ii ≤ G₀ := Finset.single_le_sum (fun j _ => Nat.zero_le (G j)) (Finset.mem_univ ii)
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound (D*K ii*2^(i+8))
  filter_upwards [hb ii,hH,hh,hrough,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with X hbound hH hh hrough hX hlog
  have hKi : 0 < K ii := hK ii
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hLp : 0 < Real.log X := zero_lt_one.trans_le hlog
  have hL : 0 < 1+Real.log X := by linarith
  have hroughi : 2*(Real.log X)^(G ii) ≤ min (X^ξ)
      (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) (h X)) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlog hGG) (by norm_num)).trans hrough
  have hpiece (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
      (q : ℕ × ℕ × ℕ)
      (hq : q ∈ (if true then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h X) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)))
      (j r : ℕ) :
      ‖angular_distinguishedStoppedDyad ℓ i ρ ξ Ct (H X) X (h X) true d q j r‖ ≤
        K ii*X^(5/6:ℝ)/(Real.log X)^(i+8) := by
    have hq' := Finset.mem_filter.mp hq
    have hk : 1 ≤ q.2.1 := (Finset.mem_filter.mp hq'.1).2
    exact hbound (H X) hH (h X) hh hroughi d q j r hk hq'.2
  have hsum := hagg Ct ξ (H X) X hX (h X) true
    (K ii*X^(5/6:ℝ)/(Real.log X)^(i+8)) (by positivity) hpiece
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3)]
  apply hsum.trans
  have hn := stopped_log_quotient_normalize (i+5) 3 hlog (hK ii).le
    (Real.rpow_nonneg hXp.le (5/6:ℝ))
  have hn' : (1+Real.log X)^(i+5)*(K ii*X^(5/6:ℝ)/(Real.log X)^(i+8)) ≤
      (K ii*2^(i+8))*X^(5/6:ℝ)/(1+Real.log X)^3 := by
    simpa only [show i+5+3=i+8 by omega] using hn
  calc
    _ = D*((1+Real.log X)^(i+5)*(K ii*X^(5/6:ℝ)/(Real.log X)^(i+8))) := by ring
    _ ≤ D*((K ii*2^(i+8))*X^(5/6:ℝ)/(1+Real.log X)^3) :=
      mul_le_mul_of_nonneg_left hn' hD.le
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
