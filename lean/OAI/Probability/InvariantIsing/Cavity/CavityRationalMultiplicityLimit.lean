import OAI.Probability.InvariantIsing.Cavity.CavityRationalAllSizes
import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalMass
import OAI.Probability.InvariantIsing.Cavity.CavityMultiplicityTransport

namespace OAI

/-! Rational finite-spectrum pressure convergence with arbitrary
multiplicities having the prescribed positive limiting proportions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators

namespace InvariantIsing

theorem cavity_rational_multiplicity_tendsto
    (hhaar : HaarConcentrationInput) (hgauss : GaussianLipschitzVarianceInput)
    (hpub : PanchenkoTalagrandFieldPairInput)
    {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n) (s : Fin m → ℕ)
    (hs : ∀ a, 0 < s a) (hsum : ∑ a, s a=n)
    (μ : (N : ℕ) → Measure (Orthogonal N)) [∀ N, IsProbabilityMeasure (μ N)]
    [∀ N, (μ N).IsMulRightInvariant] (lam : Fin m → ℝ)
    (g : (N : ℕ) → Fin N → Fin m)
    (hρ : Tendsto (fun N a => ((cavitySpectralGroup (g N) a).card : ℝ)/N) atTop
      (𝓝 (fun a => (s a : ℝ)/n))) :
    Tendsto (fun N => ∫ V, rotatedPressure (fun i => lam (g N i))
      (matrixRotation V⁻¹) (fun _ => 0) ∂μ N) atTop
      (𝓝 (variationalFunctional (finiteR (fun j => (s j : ℝ)/n) lam
        (cavityRationalMass_positive s hs hn) (cavityRationalMass_sum s hsum hn))).toReal) := by
  let A := fun N => cavityResidueLabel (by omega : 0 < m) s hsum N
  let K := ∑ a, |lam a|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound a : |lam a| ≤ K :=
    Finset.single_le_sum (f := fun a => |lam a|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  have hdiam a b : |lam a-lam b| ≤ 2*K :=
    (abs_sub _ _).trans (by linarith [hbound a,hbound b])
  have hd := cavity_meanPressure_same_proportions_tendsto (fun k => k+1)
    (fun _ => by omega) (fun k => μ (k+1)) (fun k => A (k+1)) (fun k => g (k+1))
    (fun a => (s a : ℝ)/n) (cavityRationalMass_positive s hs hn)
    ((cavity_canonical_mass_tendsto (by omega : 0 < m) hn s hsum).comp (tendsto_add_atTop_nat 1))
    (hρ.comp (tendsto_add_atTop_nat 1)) lam (fun _ _ => 0) K hbound (2*K) (by positivity) hdiam
  have hb := (cavity_rational_all_sizes_tendsto hhaar hgauss hpub hm hn s hs hsum μ lam).comp
    (tendsto_add_atTop_nat 1)
  have hh := hd.add hb
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [A, Function.comp_def, Pi.add_apply, zero_add, sub_add_cancel] using hh

end InvariantIsing

end

end OAI
