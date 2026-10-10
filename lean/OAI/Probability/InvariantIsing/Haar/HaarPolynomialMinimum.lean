import OAI.Probability.InvariantIsing.Haar.HaarPolynomialValue
import OAI.Probability.InvariantIsing.Haar.HaarPolynomialLaplacian
import OAI.Probability.InvariantIsing.Haar.CompactParabolicMinimum

namespace OAI

/-! Maximum-principle signs for the genuine rotation Laplacian. -/
noncomputable section
open Matrix MvPolynomial MeasureTheory Filter Set
open scoped BigOperators Topology
namespace InvariantIsing

lemma haarPolynomialLaplacian_nonneg_at_min {N : ℕ}
    (p : MatrixPolynomial N) (U : SpecialOrthogonal N)
    (hmin : ∀ V : SpecialOrthogonal N, haarPolynomialValue p U ≤ haarPolynomialValue p V) :
    0 ≤ haarPolynomialValue (haarPolynomialLaplacian N p) U := by
  unfold haarPolynomialValue
  rw [haarPolynomialLaplacian_apply,map_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [map_sum]
  apply Finset.sum_nonneg
  intro j _
  let q := matrixPolynomialDerivation (planeGenerator i j) p
  have hm : IsLocalMin (fun t => haarPolynomialValue p (specialPlaneRotation i j t*U)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [specialPlaneRotation_zero,one_mul] using hmin (specialPlaneRotation i j t*U)
  have hd : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt
      (fun s => haarPolynomialValue p (specialPlaneRotation i j s*U))
      (haarPolynomialValue q (specialPlaneRotation i j t*U)) t :=
    Filter.Eventually.of_forall fun t => hasDerivAt_specialPlaneRotation_polynomial p i j U t
  have hdd := hasDerivAt_specialPlaneRotation_polynomial q i j U 0
  simp only [specialPlaneRotation_zero,one_mul] at hdd
  exact second_derivative_nonneg_at_local_min hm hd hdd

/-- Compact-space parabolic comparison, with the spatial sign proved above. -/
theorem haarPolynomial_parabolic_nonneg {N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (p : ℝ → MatrixPolynomial N) (Wt : ℝ × SpecialOrthogonal N → ℝ)
    (hc : ContinuousOn (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (p z.1) z.2)
      (Icc (0 : ℝ) T ×ˢ Set.univ))
    (hi : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (p 0) U)
    (hd : ∀ t ∈ Ioc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      HasDerivAt (fun s => haarPolynomialValue (p s) U) (Wt (t,U)) t)
    (hpde : ∀ t ∈ Ioc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialLaplacian N (p t)) U-
        haarPolynomialValue (p t) U ≤ Wt (t,U)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      0 ≤ haarPolynomialValue (p t) U := by
  apply compact_parabolic_nonneg hT
    (fun t U => haarPolynomialValue (p t) U) Wt
    (fun t U => haarPolynomialValue (haarPolynomialLaplacian N (p t)) U)
    hc hi hd hpde
  intro t _ U hm
  exact haarPolynomialLaplacian_nonneg_at_min (p t) U hm

end InvariantIsing

end

end OAI
