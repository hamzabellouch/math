import OAI.NumberTheory.CubicMoment.Estimates.ActiveRoughStopping
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailDecompositionRows
import OAI.NumberTheory.CubicMoment.Estimates.HeightNoStopBound

namespace OAI

/-! The upper-height branch uses one stopping threshold, X^(1/3-κ).
The identity retains the actual envelope and inverse binomial weights. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eventually_distinguishedScale_upper_initial (i : ℕ) (ξ : ℝ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ d : Fin i →
      Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
      distinguishedScaleLength d < X^(1/3-2*κ) → ∀ r : Eisenstein,
      distinguishedScaleCoefficient i ξ X d r ≠ 0 → norm r < X^(1/3-κ) := by
  filter_upwards [eventually_const_mul_rpow_le
    (show (1/3-2*κ:ℝ) < 1/3-κ by linarith) (2^i)] with X hX
  intro d hd r hr
  exact (distinguishedScaleCoefficient_range i ξ X d hr).2.trans_lt
    ((mul_lt_mul_of_pos_left hd (by positivity)).trans_le hX)

def upperTailNoStopRow (i : ℕ) (ℓ : ℤ) (κ ρ ξ H U X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  restrictedNoStopGaussWindowValue (centralPrimaryFactors X)
    (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ) ρ
    (X^(1/3-κ)) (Real.exp primeProductWeights.radius) ℓ primeProductEnvelope H U X X
    (fun _ _ => True)

def upperTailStoppedRow (i : ℕ) (ℓ : ℤ) (κ ρ ξ H U X : ℝ)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) : ℂ :=
  let F := Real.exp primeProductWeights.radius*X
  ∑ q ∈ stoppingLabelBox ρ F, (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
    ∑ a ∈ primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X),
      ∑ b ∈ primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X),
        stoppedAlpha (centralPrimaryFactors X) (centralPrimaryFactors X) primeDetectorCutoff
            (X^ξ) (stoppingRemainingTest (geometricPrimeBin ρ F) q.1 q.2.2) a *
          stoppedBeta (centralPrimaryFactors X) (centralPrimaryFactors X)
            (distinguishedScaleCoefficient i ξ X d) primeDetectorCutoff (X^ξ)
            (stoppedSideTest (geometricPrimeBin ρ F) (geometricBinLower ρ F)
              q.1 q.2.1 0 (X^(1/3-κ)) (X^(1/3-κ)) true) b *
          (if a*b ∈ centralProductEnvelope X then scaleFirstTailKernel ℓ H U X (a*b) else 0)

theorem scaleFirstTailScaleRow_upper_stopping (i : ℕ) (ξ : ℝ)
    {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ ρ : ℝ, 1 < ρ → ρ ≤ 2 →
      ∀ (ℓ : ℤ) (H U : ℝ)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
      distinguishedScaleLength d < X^(1/3-2*κ) →
      scaleFirstTailScaleRow i ℓ ξ H U X d =
        upperTailNoStopRow i ℓ κ ρ ξ H U X d + upperTailStoppedRow i ℓ κ ρ ξ H U X d := by
  filter_upwards [eventually_distinguishedScale_upper_initial i ξ hκ,
    eventually_ge_atTop (1:ℝ)] with X hstart hX
  intro ρ hρ hρ₂ ℓ H U d hd
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_exp primeProductWeights.radius_nonneg) hX
  have he := roughProduct_matrix_stopping_active (centralProductEnvelope X)
    (centralPrimaryFactors X) hρ hρ₂ hF (fun _ hn => centralProductEnvelope_spec hn)
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (distinguishedScaleCoefficient i ξ X d) (fun r _ hr => hstart d hd r hr)
    0 (X^(1/3-κ)) primeDetectorCutoff (X^ξ) (scaleFirstTailKernel ℓ H U X)
  unfold scaleFirstTailScaleRow
  rw [he]
  apply congrArg₂ (· + ·)
  · unfold upperTailNoStopRow restrictedNoStopGaussWindowValue
    simp only [centralProductEnvelope,centralPrimaryFactors,and_true,
      scaleFirstTailKernel,productGaussHeightWindowKernel]
  · rfl

theorem upperTailNoStopRow_finite_bound (m : ℕ) (hpnt : PrimaryPrimePNT)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    {MV : ℝ} (hMV : MontgomeryVaughanBound MV) (hMean0 : 0 ≤ MV)
    {κ η cap : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/3) (hη : η ≤ κ/4)
    (hcap : 1 < cap) (M : ℕ) :
    ∃ ρ C E : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ρ ≤ cap ∧ 0 ≤ C ∧ 0 ≤ E ∧
      ∀ᶠ X : ℝ in atTop, ∀ i < m, ∀ (ξ H U : ℝ)
        (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))),
        0 < H → Real.log X ≤ U → X^(1/100:ℝ) < U → U ≤ X^(1/6+η) →
        ‖upperTailNoStopRow i 0 κ ρ ξ H U X d‖ ≤
          (1+Real.log X)*(C*X^(5/6-min (1/100) (3*κ/16))+
            E*X^(5/6:ℝ)/(Real.log X)^M) := by
  let A : ℝ := ∑ i ∈ Finset.range m, ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ)
  obtain ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,hbound⟩ := radial_height_noStop_bound
    hpnt primeProductWeights hVor hMV hMean0 hκ hκsmall hη
    (A := A) (by dsimp [A]; positivity) hcap M
  refine ⟨ρ,C,E,hρ,hρ₂,hsmall,hC,hE,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with X hb hX
  intro i hi ξ H U d hH hLU hU hUhi
  have hAi : ‖(i.factorial:ℂ)⁻¹‖*(i^i:ℕ) ≤ A := by
    dsimp only [A]
    exact Finset.single_le_sum (f := fun j : ℕ => ‖(j.factorial:ℂ)⁻¹‖*(j^j:ℕ))
      (fun j _ => by positivity) (Finset.mem_range.mpr hi)
  have he := hb () (centralPrimaryFactors X) (distinguishedScaleCoefficient i ξ X d)
    primeDetectorCutoff (X^ξ) H U X (fun _ _ => True) hLU hUhi hH hX
    (fun _ hr => (mem_primaryElementBall.mp hr).1)
    (fun r _ => (distinguishedScaleCoefficient_norm i ξ X d r).trans hAi)
    (fun x => ⟨primeDetectorCutoff_nonneg x,primeDetectorCutoff_le_one x⟩)
  simpa only [heightNoStopThreshold,not_le.mpr hU,ite_false,upperTailNoStopRow] using he

end CubicFirstMoment

end

end OAI
