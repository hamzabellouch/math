import OAI.Combinatorics.Progressions.Fourier.FourierLawTransport
import OAI.Combinatorics.Progressions.Fourier.ResidueFourierProjection

namespace OAI

section

namespace Erdos3.IntegerFourierBudget

open scoped BigOperators Classical

def RationalMode {J : Type*} (B : IntegerFourierBudget) (K M : ℕ) (ε : ℝ) (k : J → Fin M) : Prop :=
  ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ B.denominatorBound ε ∧
    ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ B.residualBound ε) ∧
      ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / d + ξ j / K

theorem projected_approximation {X J H G : Type*}
    [Fintype X] [Fintype J] [AddCommGroup H] [Fintype H] [Fintype G]
    (B : IntegerFourierBudget) (p : FiniteProbabilityWeights X)
    (Y : (J → ℤ) → X → J → ℤ) (K M : ℕ) [NeZero M] (hKM : K ≤ M)
    (hmodel : B.Controls p Y K M) (q : FiniteProbabilityWeights G)
    (ι : H →+ (J → ZMod M)) (w : G → ℂ) (path : G → J → ℤ)
    {W ε τ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 ≤ τ)
    (hw : q.mean (fun x => ‖w x‖) ≤ W)
    (hdiscard : ∀ k, B.RationalMode K M ε k → (rectangularResidueMode M k).compAddMonoidHom ι ≠ 1 →
      ‖q.complexMean (fun x => w x * star (rectangularGridCharacter M k (path x)))‖ ≤ τ) :
    ∃ S : Finset (J → Fin M),
      (S.card : ℝ) ≤ B.countConstant / ε ^ B.countExponent ∧
      (∀ center, (∑ k, ‖integerGridCoefficient p (Y center) M k‖) ≤ B.coefficientCap) ∧
      (∀ k ∈ S, B.RationalMode K M ε k) ∧
      ∀ center, (∀ x, q.weight x ≠ 0 → centeredFundamentalBox B.radius K center (path x)) →
        ‖q.complexMean (fun x => w x *
          (((K : ℝ) ^ Fintype.card J * finiteImageMass p (Y center) (path x) : ℝ) : ℂ)) -
          q.complexMean (fun x => w x * finiteCosetAverage ι (residueGridApproximation p (Y center) K M S)
            (integerGridResidue M (path x)))‖ ≤ W * ε + B.coefficientCap * τ := by
  obtain ⟨S, hcount, hcap, hchar, happ⟩ := hmodel ε hε hε1
  refine ⟨S, hcount, hcap, hchar, ?_⟩
  intro center hpath
  apply residueGridProjection_tested_error p (Y center) K M S q ι
    (fun x => (((K : ℝ) ^ Fintype.card J * finiteImageMass p (Y center) (path x) : ℝ) : ℂ))
    w path hKM hε.le hτ hw (hcap center)
  · intro x hx
    exact happ center (path x) (hpath x hx)
  · intro k hk
    exact hdiscard k.val (hchar k.val k.property) hk

end Erdos3.IntegerFourierBudget

end

end OAI
