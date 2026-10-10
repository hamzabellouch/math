import OAI.Probability.InvariantIsing.Cavity.CavityAffinePressureLimit
import OAI.Probability.InvariantIsing.Cavity.CavityResidueConvergence

namespace OAI

/-! Rational finite-spectrum pressure convergence on the full sequence
of physical dimensions, with every residue class accounted for. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_rational_all_sizes_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : Fin m → ℝ) :
    Tendsto (fun N => ∫ V, rotatedPressure
      (fun i => lam (cavityResidueLabel (by omega : 0 < m) s hsum N i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ N) atTop
      (𝓝 (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
        (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal) := by
  let P := fun N => ∫ V, rotatedPressure
    (fun i => lam (cavityResidueLabel (by omega : 0 < m) s hsum N i))
    (matrixRotation V⁻¹) (fun _ => 0) ∂μ N
  let q := m*n-n+n+3
  apply cavity_residue_tendsto hn q P
  intro t
  have hh := cavity_affine_pressure_tendsto hhaar hgauss hpub hm hn s
    (cavityResidueOffset (by omega : 0 < m) t) hs hsum μ lam
  apply hh.congr
  intro r
  dsimp only [P]
  rw [← cavityResidueSize (by omega : 0 < m) n q (t : ℕ) r]
  rw [cavityResidueLabel_progression (by omega : 0 < m) s hsum q (t : ℕ) r t.isLt]

end InvariantIsing

end

end OAI
