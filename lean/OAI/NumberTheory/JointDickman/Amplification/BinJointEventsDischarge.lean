import OAI.NumberTheory.JointDickman.Amplification.BinJointEvents
import OAI.NumberTheory.JointDickman.Analysis.CanonicalCharacterPairsDischarge

namespace OAI

/-! # Application consequences of the proved short-average estimates -/
namespace JointDickman
open Finset Filter MeasureTheory Classical PublishedInputs
open scoped Topology

theorem bin_joint_event_limit_proved
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (hνone : ∑ r, ν r = 1)
    (hνmean : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (P Q : BinCountState J → Prop) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      if P (canonicalBinVector J (N : ℝ) n) ∧ Q (canonicalBinVector J (N : ℝ) (n+1))
        then (1 : ℂ) else 0)/(N : ℂ)) atTop
      (𝓝 (((∑ r with P r, ν r : ℝ) : ℂ)*((∑ r with Q r, ν r : ℝ) : ℂ))) := by
  have hc (χ ψ : AddChar (BinCountState J) ℂ) :=
    canonical_character_pair_limit_proved hKMT hFord hSD hSW hM hMP hMC hJ ν hν hνone hνmean χ ψ
  have he := jointEvent_factorization (G := BinCountState J) (H := BinCountState J)
    (fun N => range N) (fun N => 1/(N : ℂ))
    (fun N n => canonicalBinVector J (N : ℝ) n)
    (fun N n => canonicalBinVector J (N : ℝ) (n+1))
    (fun r => (ν r : ℂ)) (fun r => (ν r : ℂ))
    (fun χ ψ => by simpa only [one_div_mul_eq_div] using hc χ ψ) P Q
  simpa only [one_div_mul_eq_div,Complex.ofReal_sum] using he

end JointDickman

end OAI
