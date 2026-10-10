import OAI.NumberTheory.CubicMoment.Estimates.CentralProductSupport

namespace OAI

/-! Exact central stopping decomposition, with the whole distinguished
no-stop branch already controlled. The remaining terms are the literal
stopped matrix and the large distinguished-product rows. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def centralPrimaryFactors (X : ℝ) : Finset Eisenstein :=
  primaryElementBall (Real.exp primeProductWeights.radius*X)

def centralSmallOuter (X : ℝ) : Finset Eisenstein :=
  (centralPrimaryFactors X).filter (fun r => norm r < X^(38/100:ℝ))

def distinguishedLargeLow (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ r ∈ (centralPrimaryFactors X).filter (fun r => ¬norm r < X^(38/100:ℝ)),
    distinguishedSubsetWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) r*
      ∑ u ∈ primaryProductSlice (centralProductEnvelope X)
        (Real.exp primeProductWeights.radius*X) r,
        (roughProduct primeDetectorCutoff (X^ξ) u:ℂ)*
          centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (r*u)

def distinguishedStoppedLow (ℓ : ℤ) (ρ ξ : ℝ) (Ct : ℕ) (H X : ℝ) : ℂ :=
  ∑ q ∈ stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X),
    (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*
      ∑ a ∈ primaryPairSupport (centralPrimaryFactors X) (centralPrimaryFactors X),
        ∑ b ∈ primaryPairSupport (centralSmallOuter X) (centralPrimaryFactors X),
          stoppedAlpha (centralPrimaryFactors X) (centralPrimaryFactors X)
            primeDetectorCutoff (X^ξ)
            (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
              q.1 q.2.2) a*
          stoppedBeta (centralSmallOuter X) (centralPrimaryFactors X)
            (distinguishedSubsetWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)))
            primeDetectorCutoff (X^ξ)
            (stoppedSideTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
              (geometricBinLower ρ (Real.exp primeProductWeights.radius*X))
                q.1 q.2.1 0 (X^(38/100:ℝ)) (X^(36/100:ℝ)) true) b*
          (if a*b ∈ centralProductEnvelope X then
            centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X (a*b)
          else 0)

theorem centralRoughProduct_stopping (ℓ : ℤ) (ξ : ℝ) (Ct : ℕ) (H : ℝ)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 0 < X)
    (hF : 1 ≤ Real.exp primeProductWeights.radius*X) :
    centralRoughProduct ℓ H ((1+Real.log X)^Ct) X =
      distinguishedNoStopLow ℓ ρ ξ Ct H X X+
        distinguishedStoppedLow ℓ ρ ξ Ct H X+distinguishedLargeLow ℓ ξ Ct H X := by
  let F := Real.exp primeProductWeights.radius*X
  let v := distinguishedSubsetWeight primeDetectorCutoff (X^ξ) (X^(2/5:ℝ))
  let K := centeredHeightKernel ℓ primeProductEnvelope H ((1+Real.log X)^Ct) X X
  let f := fun r => v r*∑ u ∈ primaryProductSlice (centralProductEnvelope X) F r,
    (roughProduct primeDetectorCutoff (X^ξ) u:ℂ)*K (r*u)
  have hS : ∀ n ∈ centralProductEnvelope X, primary n ∧ Squarefree n ∧ norm n ≤ F :=
    fun n hn => centralProductEnvelope_spec hn
  have hs : (∑ r ∈ centralSmallOuter X, f r) =
      distinguishedNoStopLow ℓ ρ ξ Ct H X X+distinguishedStoppedLow ℓ ρ ξ Ct H X := by
    exact roughProduct_matrix_stopping (centralProductEnvelope X) (centralSmallOuter X)
      hρ hρ₂ hF hS
      (fun r hr => (mem_primaryElementBall.mp (Finset.mem_filter.mp hr).1).1)
      (fun r hr => (Finset.mem_filter.mp hr).2) 0 (X^(36/100:ℝ)) v primeDetectorCutoff (X^ξ) K
  rw [centralRoughProduct_full ℓ H ((1+Real.log X)^Ct) hX,
    roughProduct_distinguished_slices (centralProductEnvelope X) F hS
      primeDetectorCutoff (X^ξ) (X^(2/5:ℝ)) K]
  change (∑ r ∈ centralPrimaryFactors X, f r) = _
  rw [←Finset.sum_filter_add_sum_filter_not (centralPrimaryFactors X)
    (fun r => norm r < X^(38/100:ℝ)) f]
  change (∑ r ∈ centralSmallOuter X, f r)+distinguishedLargeLow ℓ ξ Ct H X = _
  rw [hs]

theorem centralRoughProduct_sub_stopped_large_isLittleO
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hV : MetaplecticVoronoiInput a)
    (ℓ : ℤ) (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6)) (Ct : ℕ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ρ ≤ 2 ∧ ∀ (ξ : ℝ) (H : ℝ → ℝ),
      (∀ᶠ X : ℝ in atTop, 0 < H X) →
      (fun X => centralRoughProduct ℓ (H X) ((1+Real.log X)^Ct) X-
        (distinguishedStoppedLow ℓ ρ ξ Ct (H X) X+distinguishedLargeLow ℓ ξ Ct (H X) X))
        =o[atTop] firstMomentScale := by
  obtain ⟨ρ,hρ,hρ₂,hbound⟩ := distinguishedNoStopLow_isLittleO hV ℓ hGamma Ct
  refine ⟨ρ,hρ,hρ₂,?_⟩
  intro ξ H hH
  apply (hbound ξ H id hH).congr' _ Filter.EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop (1:ℝ)] with X hX
  have hF : 1 ≤ Real.exp primeProductWeights.radius*X :=
    hX.le.trans (le_mul_of_one_le_left (by linarith : (0:ℝ) ≤ X)
      (Real.one_le_exp primeProductWeights.radius_nonneg))
  rw [centralRoughProduct_stopping ℓ ξ Ct (H X) hρ hρ₂ (zero_lt_one.trans hX) hF]
  dsimp only [id_eq]
  ring

end CubicFirstMoment

end

end OAI
