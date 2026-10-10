import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionRows
import OAI.NumberTheory.CubicMoment.Estimates.UpperNoStopParameters

namespace OAI

/-! The literal ordinary-height no-stop row in the prime tail has the
published Type-I saving. Its failed first-stage prefix is preserved. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma scaleFirstTailNoStopRow_eq_window (i : ℕ) (ℓ : ℤ) (ρ ξ H U X : ℝ) (h : ℕ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    scaleFirstTailNoStopRow i ℓ ρ ξ H U X h d =
      restrictedNoStopGaussWindowValue (centralPrimaryFactors X)
        (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ) ρ
        (X^(38/100:ℝ)) (Real.exp primeProductWeights.radius) ℓ primeProductEnvelope H U X X
        (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h) := by
  unfold scaleFirstTailNoStopRow restrictedNoStopGaussWindowValue stoppingFailedPrefix
  simp only [centralProductEnvelope,centralPrimaryFactors,Finset.sum_filter,and_comm,
    scaleFirstTailKernel,productGaussHeightWindowKernel]

theorem scaleFirstTailNoStopRow_finite_bound (m : ℕ) (hpnt : PrimaryPrimePNT)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {cap : ℝ} (hcap : 1 < cap) (M : ℕ) :
    ∃ ρ C E : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ C ∧ 0 ≤ E ∧
      ∀ᶠ X : ℝ in atTop, ∀ i < m, ∀ (ξ H U : ℝ) (h : ℕ)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
        0 < H → Real.log X ≤ U → U ≤ X^(1/100:ℝ) →
        ‖scaleFirstTailNoStopRow i 0 ρ ξ H U X h d‖ ≤
          (1+Real.log X)*(C*X^(5/6-3/1600:ℝ)+E*X^(5/6:ℝ)/(Real.log X)^M) := by
  let A : ℝ := ∑ i ∈ Finset.range m, ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ)
  obtain ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,hbound⟩ := restricted_noStop_window_bound
    hpnt primeProductWeights hVor hMV hMean0
    (κ := (1/100:ℝ)) (η := 0) (ν := (1/100:ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    (A := A) (by dsimp [A]; positivity) hcap M
  refine ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,?_⟩
  filter_upwards [hbound,eventually_ordinary_noStop_window_scales primeProductWeights,
    eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with X hb hs hX hlog
  intro i hi ξ H U h d hH hLU hU
  have hAi : ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) ≤ A := by
    dsimp only [A]
    exact Finset.single_le_sum (f := fun j : ℕ => ‖(j.factorial:ℂ)⁻¹‖*(j^j:ℕ))
      (fun j _ => by positivity) (Finset.mem_range.mpr hi)
  have hXp : 0 < X := by linarith
  have hlogs : 1+Real.log (X^(39/100:ℝ)) ≤ 1+Real.log X := by
    rw [Real.log_rpow hXp]
    linarith
  rw [scaleFirstTailNoStopRow_eq_window]
  have he := hb () (centralPrimaryFactors X) (distinguishedScaleCoefficient i ξ X d)
    primeDetectorCutoff (X^ξ) (X^(38/100:ℝ)) (X^(39/100:ℝ)) H U X
    (stoppingFailedPrefix ρ (Real.exp primeProductWeights.radius*X) (X^(9/25:ℝ)) h)
    hX hlog hs.1 hLU hH hXp hs.2.1 (Or.inl ⟨hs.2.2,hU⟩)
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (fun r _ => (distinguishedScaleCoefficient_norm i ξ X d r).trans hAi)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
  convert he.trans (mul_le_mul_of_nonneg_right hlogs (by positivity)) using 1
  norm_num

end CubicFirstMoment

end

end OAI
