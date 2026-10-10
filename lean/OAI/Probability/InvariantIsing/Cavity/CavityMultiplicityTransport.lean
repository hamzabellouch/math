import OAI.Probability.InvariantIsing.Cavity.CavityOrientedFamily
import OAI.Probability.InvariantIsing.Core.MultiplicityContinuity

namespace OAI

/-! Multiplicity comparison for the physical orthogonal Haar law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_meanPressure_multiplicity_comparison {N m : ℕ} (hN : 0 < N)
    (μ : Measure (Orthogonal N)) [IsProbabilityMeasure μ] [μ.IsMulRightInvariant]
    (a b : Fin N → Fin m) (ha : Function.Surjective a) (hb : Function.Surjective b)
    (lam : Fin m → ℝ) (c : Fin N → ℝ)
    (K : ℝ) (hK : ∀ v, |lam v| ≤ K)
    (L r : ℝ) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hdiam : ∀ v w, |lam v-lam w| ≤ L)
    (herr : ∀ v, |((Finset.univ.filter fun i => a i=v).card : ℝ)-
      ((Finset.univ.filter fun i => b i=v).card : ℝ)| ≤
      r*min ((Finset.univ.filter fun i => a i=v).card : ℝ)
        ((Finset.univ.filter fun i => b i=v).card : ℝ)) :
    |(∫ V, rotatedPressure (fun i => lam (b i)) (matrixRotation V⁻¹) c ∂μ)-
      ∫ V, rotatedPressure (fun i => lam (a i)) (matrixRotation V⁻¹) c ∂μ| ≤ L*r/2 := by
  let ν := cavityOrientedBaseLaw hN μ
  let : ν.IsMulLeftInvariant := cavityOrientedBaseLaw_leftInvariant hN μ
  have hh := meanPressure_multiplicity_comparison hN ν a b ha hb lam c K hK L r hL hr hdiam herr
  rw [cavity_oriented_pressure, cavity_oriented_pressure] at hh
  exact hh

lemma cavity_meanPressure_same_proportions_tendsto {m : ℕ}
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k)
    (μ : (k : ℕ) → Measure (Orthogonal (N k))) [∀ k, IsProbabilityMeasure (μ k)]
    [∀ k, (μ k).IsMulRightInvariant]
    (a b : (k : ℕ) → Fin (N k) → Fin m)
    (ρ : Fin m → ℝ) (hρ : ∀ v, 0 < ρ v)
    (ha : Tendsto (fun k v => ((Finset.univ.filter fun i => a k i=v).card : ℝ)/N k)
      atTop (𝓝 ρ))
    (hb : Tendsto (fun k v => ((Finset.univ.filter fun i => b k i=v).card : ℝ)/N k)
      atTop (𝓝 ρ))
    (lam : Fin m → ℝ) (c : (k : ℕ) → Fin (N k) → ℝ)
    (K : ℝ) (hK : ∀ v, |lam v| ≤ K)
    (L : ℝ) (hL : 0 ≤ L) (hdiam : ∀ v w, |lam v-lam w| ≤ L) :
    Tendsto (fun k => (∫ V, rotatedPressure (fun i => lam (b k i))
      (matrixRotation V⁻¹) (c k) ∂μ k)-
      ∫ V, rotatedPressure (fun i => lam (a k i)) (matrixRotation V⁻¹) (c k) ∂μ k)
      atTop (𝓝 0) := by
  have hh := meanPressure_same_proportions_tendsto N hN
    (fun k => cavityOrientedBaseLaw (hN k) (μ k))
    (fun k => cavityOrientedBaseLaw_leftInvariant (hN k) (μ k))
    a b ρ hρ ha hb lam c K hK L hL hdiam
  simpa only [cavity_oriented_pressure] using hh

end InvariantIsing

end

end OAI
