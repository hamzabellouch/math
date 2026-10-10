import OAI.Probability.InvariantIsing.Spectral.SpectralWardPaths
import OAI.Probability.InvariantIsing.Spectral.SpectralDiagonalWardLimits

namespace OAI

/-! The two limiting spectral Ward equations imply the manuscript symbol
and root equations for synchronized overlap paths. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

lemma spectralDiagonalWardResidual_eq_synchronizedPath {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (q : Fin (m + 1) → ℝ)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = q j)
    (ρ eig : Fin m → ℝ) (a b : Fin m) (f g : ℝ → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfa : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) a.castSucc : ℝ) = f (spectralSpinArray x 0 1))
    (hga : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) b.castSucc : ℝ) = g (spectralSpinArray x 0 1)) :
    spectralDiagonalWardResidual Q ρ eig a b =
      diagonalWardResidual (ρ a) (ρ b) (eig a - eig b) (q a.castSucc) (q b.castSucc)
        (fun u => f (spectralSpinQuantilePath Q hP hn u))
        (fun u => g (spectralSpinQuantilePath Q hP hn u)) := by
  have hi : (∫ x, (x (0,1) a.castSucc : ℝ) * (x (0,1) b.castSucc : ℝ)
      ∂(Q : Measure (SpectralArray (m + 1)))) =
      ∫ s, f (spectralSpinQuantilePath Q hP hn s) * g (spectralSpinQuantilePath Q hP hn s)
        ∂pathMeasure := by
    calc
      _ = ∫ x, f (spectralSpinArray x 0 1) * g (spectralSpinArray x 0 1)
          ∂(Q : Measure (SpectralArray (m + 1))) := by
        apply integral_congr_ae
        filter_upwards [hfa, hga] with x hx hy
        rw [hx, hy]
      _ = _ := spectralSpinQuantile_integral Q hP hn _ (hf.mul hg)
  rw [spectralDiagonalWardResidual_constant_diagonal Q ρ eig a b q hd, hi]
  rfl

 theorem spectralSynchronizedWard_symbols {m : ℕ}
    (Q : ProbabilityMeasure (SpectralArray (m + 1)))
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (q : Fin (m + 1) → ℝ)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, (x (i,i) j : ℝ) = q j)
    (ρ eig : Fin m → ℝ) (a b : Fin m) (f g : ℝ → ℝ)
    (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (hfb : ∀ r, f r ∈ Icc (0 : ℝ) 1) (hgb : ∀ r, g r ∈ Icc (0 : ℝ) 1)
    (hfa : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) a.castSucc : ℝ) = f (spectralSpinArray x 0 1))
    (hga : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) b.castSucc : ℝ) = g (spectralSpinArray x 0 1))
    (hdiag : spectralDiagonalWardResidual Q ρ eig a b = 0)
    (hoff : ∀ᵐ s ∂pathMeasure, offWardPath (ρ a) (ρ b) (eig a - eig b) (q a.castSucc) (q b.castSucc)
      (fun u => f (spectralSpinQuantilePath Q hP hn u))
      (fun u => g (spectralSpinQuantilePath Q hP hn u)) s = 0) :
    let p := spectralSpinQuantilePath Q hP hn
    let A := fun u => f (p u)
    let B := fun u => g (p u)
    (∀ᵐ s ∂pathMeasure, ρ b * pathSymbol (q a.castSucc) A s -
      ρ a * pathSymbol (q b.castSucc) B s =
        (eig a - eig b) * pathSymbol (q a.castSucc) A s * pathSymbol (q b.castSucc) B s) ∧
    (ρ b * f (Function.rightLim p.val 0) - ρ a * g (Function.rightLim p.val 0) =
      (eig a - eig b) *
        ((q a.castSucc - ∫ u in 0..1, A u) * g (Function.rightLim p.val 0) +
          f (Function.rightLim p.val 0) * (q b.castSucc - ∫ u in 0..1, B u))) := by
  intro p A B
  have haf (r : ℝ) : |f r| ≤ 1 := by rw [abs_of_nonneg (hfb r).1]; exact (hfb r).2
  have hag (r : ℝ) : |g r| ≤ 1 := by rw [abs_of_nonneg (hgb r).1]; exact (hgb r).2
  have hA : Measurable A := hf.continuous.measurable.comp p.measurable
  have hB : Measurable B := hg.continuous.measurable.comp p.measurable
  have hdpath : diagonalWardResidual (ρ a) (ρ b) (eig a - eig b) (q a.castSucc) (q b.castSucc) A B = 0 := by
    rw [← spectralDiagonalWardResidual_eq_synchronizedPath Q hP hn q hd ρ eig a b f g
      hf.continuous.measurable hg.continuous.measurable hfa hga]
    exact hdiag
  refine ⟨offWardPath_symbol (ρ a) (ρ b) (eig a - eig b) (q a.castSucc) (q b.castSucc)
    A B hA hB zero_le_one (fun u => haf (p u)) (fun u => hag (p u)) hdpath hoff, ?_⟩
  have hra : Tendsto A (𝓝[>] 0) (𝓝 (f (Function.rightLim p.val 0))) :=
    hf.continuous.continuousAt.tendsto.comp (p.monotone.tendsto_rightLim 0)
  have hrb : Tendsto B (𝓝[>] 0) (𝓝 (g (Function.rightLim p.val 0))) :=
    hg.continuous.continuousAt.tendsto.comp (p.monotone.tendsto_rightLim 0)
  exact offWardPath_root (ρ a) (ρ b) (eig a - eig b) (q a.castSucc) (q b.castSucc)
    A B hA hB zero_le_one (fun u => haf (p u)) (fun u => hag (p u)) hra hrb hoff

end InvariantIsing

end

end OAI
