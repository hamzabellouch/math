import OAI.Dynamics.StandardMap.Lyapunov.Definitions

namespace OAI

section ComponentsStatement
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy

noncomputable def normalizedArea (E : Set Torus) : Measure Torus :=
  (area E)⁻¹ • area.restrict E

def IsBernoulli (f : Torus → Torus) (μ : Measure Torus) : Prop :=
  ∃ (β : Measure ℝ), IsProbabilityMeasure β ∧
    ∃ (encode : Torus → (ℤ → ℝ)) (decode : (ℤ → ℝ) → Torus),
      MeasurePreserving encode μ (MeasureTheory.Measure.infinitePi (fun _ : ℤ => β)) ∧
      MeasurePreserving decode (MeasureTheory.Measure.infinitePi (fun _ : ℤ => β)) μ ∧
      (∀ᵐ z ∂μ, decode (encode z) = z) ∧
      (∀ᵐ w ∂MeasureTheory.Measure.infinitePi (fun _ : ℤ => β), encode (decode w) = w) ∧
      (∀ᵐ z ∂μ, encode (f z) = fun i : ℤ => encode z (i+1))

def HyperbolicBernoulliComponent (k : ℝ) : Prop :=
  ∃ E : Set Torus, MeasurableSet E ∧ 0 < area E ∧
    ((standardMap k) ⁻¹' E =ᵐ[area] E) ∧
    Ergodic (standardMap k) (normalizedArea E) ∧
    (∀ᵐ z ∂normalizedArea E, ∃ l : ℝ, 0 < l ∧ LyapunovSpectrumAt k z l) ∧
    ∃ (N : ℕ) (hN : 0 < N) (P : Fin N → Set Torus),
      (∀ j, MeasurableSet (P j)) ∧
      ((⋃ j, P j) =ᵐ[area] E) ∧
      (∀ i j, i ≠ j → area (P i ∩ P j) = 0) ∧
      (∀ j : Fin N, (standardMap k '' P j) =ᵐ[area]
        P ⟨(j.val+1)%N, Nat.mod_lt _ hN⟩) ∧
      (∀ j, area (P j) = area E / (N : ℝ≥0∞) ∧ 0 < area (P j)) ∧
      (∀ j, IsBernoulli ((standardMap k)^[N]) (normalizedArea (P j)))

def MainComponentsObligation : Prop :=
  ∃ k₀ : ℝ, 0 < k₀ ∧ ∀ k : ℝ, k₀ ≤ k → HyperbolicBernoulliComponent k

end StandardMapEntropy
end ComponentsStatement

end OAI
