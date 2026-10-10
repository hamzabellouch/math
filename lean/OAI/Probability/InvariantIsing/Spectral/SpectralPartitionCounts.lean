import OAI.Probability.InvariantIsing.Spectral.EmpiricalSpectralLaw
import OAI.Probability.InvariantIsing.Cavity.CavityProjectionGeometry

namespace OAI

/-! Weak empirical convergence gives the actual spectral group
proportions on finite partitions with null boundaries. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical

namespace InvariantIsing

lemma spectral_partition_counts_tendsto {m : ℕ}
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (eig : (k : ℕ) → Fin (N k) → ℝ)
    (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hN k) (eig k)) atTop (𝓝 ν))
    (S : Fin m → Set ℝ) (hS : ∀ a, MeasurableSet (S a))
    (hboundary : ∀ a, (ν : Measure ℝ) (frontier (S a))=0)
    (g : (k : ℕ) → Fin (N k) → Fin m)
    (hg : ∀ k a i, g k i=a ↔ eig k i∈S a) :
    Tendsto (fun k a => ((cavitySpectralGroup (g k) a).card : ℝ)/N k) atTop
      (𝓝 (fun a => (ν : Measure ℝ).real (S a))) := by
  apply tendsto_pi_nhds.mpr
  intro a
  have hh := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak (hboundary a)
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℝ) (S a))).comp hh
  apply hr.congr
  intro k
  change (empiricalSpectralLaw (hN k) (eig k) : Measure ℝ).real (S a)=_
  rw [empiricalSpectralLaw_mass (hN k) (eig k) (S a) (hS a)]
  congr 2
  apply congrArg Finset.card
  apply Finset.ext
  intro i
  simp only [cavitySpectralGroup,Finset.mem_filter,Finset.mem_univ,true_and,hg]

end InvariantIsing

end

end OAI
