import OAI.Geometry.NodalSets.Waves.GaussianDerivativeMoments

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory
open scoped ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma normalizedRescaling_smooth (f : Coord → ℂ) (hf : ContDiff ℝ ∞ f)
    (S : Coord → ℝ) (N s sigma : ℝ) (x : Coord) :
    ContDiff ℝ ∞ (normalizedRescaling f S N s sigma x) := by
  have hn : ContDiff ℝ ∞ (rescaledSeedNormalizer S (x,s⁻¹)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_const.mul (fderiv ℝ S x).contDiff).exp)
  exact (contDiff_const.mul hn).mul
    (hf.comp (contDiff_const.add (contDiff_id.const_smul _)))

lemma rescaledSeed_smooth (S0 T0 S : Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (N s sigma : ℝ) (x : Coord) :
    ContDiff ℝ ∞ (rescaledSeed S0 T0 S N s sigma x) := by
  rw [rescaledSeed_representation]
  apply contDiff_const.mul
  have hn : ContDiff ℝ ∞ (rescaledSeedNormalizer S (x,s⁻¹)) :=
    Complex.ofRealCLM.contDiff.comp
      ((contDiff_const.mul (fderiv ℝ S x).contDiff).exp)
  exact Complex.reCLM.contDiff.comp (hn.mul (waveExp_contDiff
    ((rescaledSeedPhase_smooth S0 T0 hS0 hT0).comp
      (contDiff_const.prodMk contDiff_id)) N))

lemma rescaledGaussianField_derivative_moment (V : ι → Coord → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (S0 T0 S : Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (N s sigma : ℝ) (x y : Coord) (k : ℕ) (v : Fin k → Coord) :
    ∫ a, (iteratedFDeriv ℝ k (rescaledGaussianField V S0 T0 S N s sigma x a) y v)^2
      ∂gaussianPairs =
      (iteratedFDeriv ℝ k (rescaledSeed S0 T0 S N s sigma x) y v)^2 +
        ∑ i, ‖iteratedFDeriv ℝ k (normalizedRescaling (V i) S N s sigma x) y v‖^2 := by
  have he (a : ι × Fin 2 → ℝ) : rescaledGaussianField V S0 T0 S N s sigma x a =
      fun z ↦ rescaledSeed S0 T0 S N s sigma x z +
        gaussianWaveField (fun i ↦ normalizedRescaling (V i) S N s sigma x) a z := by
    ext z
    exact rescaledGaussianField_decomposition _ _ _ _ _ _ _ _ _ _
  simp_rw [he]
  exact seeded_gaussian_derivative_moment _ _
    (fun i ↦ normalizedRescaling_smooth _ (hV i) _ _ _ _ _)
    (rescaledSeed_smooth _ _ _ hS0 hT0 _ _ _ _) _ _ _

lemma rescaledGaussianField_derivative_memLp (V : ι → Coord → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (S0 T0 S : Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (N s sigma : ℝ) (x y : Coord) (k : ℕ) (v : Fin k → Coord) :
    MemLp (fun a ↦ iteratedFDeriv ℝ k
      (rescaledGaussianField V S0 T0 S N s sigma x a) y v) 2 gaussianPairs := by
  have he (a : ι × Fin 2 → ℝ) : rescaledGaussianField V S0 T0 S N s sigma x a =
      fun z ↦ rescaledSeed S0 T0 S N s sigma x z +
        gaussianWaveField (fun i ↦ normalizedRescaling (V i) S N s sigma x) a z := by
    ext z
    exact rescaledGaussianField_decomposition _ _ _ _ _ _ _ _ _ _
  simp_rw [he]
  exact seeded_gaussian_derivative_memLp _ _
    (fun i ↦ normalizedRescaling_smooth _ (hV i) _ _ _ _ _)
    (rescaledSeed_smooth _ _ _ hS0 hT0 _ _ _ _) _ _ _

end
end Yau.Geometry

end OAI
