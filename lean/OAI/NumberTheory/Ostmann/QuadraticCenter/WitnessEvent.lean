import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveSmallArrayDefs
import OAI.NumberTheory.Ostmann.QuadraticCenter.CenterCorrection
import OAI.NumberTheory.Ostmann.QuadraticCenter.PrimeProductTransform

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter

def smallQuadraticWitness (L M : ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
    (R : ℝ) (h : ℤ) (θ K : ℝ) : Prop :=
  ∃ s ∈ adaptiveSmallSupport L, ∃ d ∈ L.divisors, ∃ v ∈ L.divisors,
    Real.sqrt ((2:ℝ)^d.primeFactors.card)*Real.exp (-K) ≤
      ‖divisorQuadraticSumP d A (adaptiveInverse M d) s v 1 R h θ‖

theorem not_smallQuadraticWitness_imp_noSmallWitness
    {L M : ℕ} {A : ∀ p : ℕ, Finset (ZMod p)} {R : ℝ} {h : ℤ} {θ K : ℝ}
    (he : ¬smallQuadraticWitness L M A R h θ K) :
    adaptiveNoSmallWitness L M A R h θ K := by
  intro s hs d hd v hv
  exact (lt_of_not_ge (fun hb => he ⟨s,hs,d,hd,v,hv,hb⟩)).le

def primeProductWitness (L : ℕ) [NeZero L] (A : ∀ p : ℕ, Finset (ZMod p))
    (X K : ℝ) (t : ℕ → ℤ) (q : ℕ) : Prop :=
  smallQuadraticWitness L q A ((q:ℝ)/X)
    (centerCorrection q L (primeProductCenter q t))
    ((primeProductCenter q t:ℝ)/q) K

end Ostmann.QuadraticCenter

end

end OAI
