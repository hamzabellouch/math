import OAI.Probability.InvariantIsing.Spectral.SpectralOverlapPaths

namespace OAI

/-! Symbols of reconstructed finite spectral-group overlap paths. -/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

def pathSymbol (d : ℝ) (l : ℝ → ℝ) (s : ℝ) : ℝ :=
  d - s * l s - ∫ u in s..1, l u

/-- The total-overlap symbol is the deficit evaluated at the path. -/
theorem deficit_at_path_eq_symbol (p : OverlapPath) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    deficit p (p s) = pathSymbol 1 p s := by
  let g : ℝ → ℝ := fun u => max (p u - p s) 0
  have hg : Monotone g := by
    intro u v huv
    exact max_le_max (sub_le_sub_right (p.monotone huv) _) le_rfl
  have hlow : (∫ u in 0..s, g u) = 0 := by
    calc
      _ = ∫ _ in 0..s, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.1
        intro u hu
        exact max_eq_right (sub_nonpos.mpr (p.monotone hu.2.le))
      _ = 0 := by simp
  have hhigh : (∫ u in s..1, g u) = (∫ u in s..1, p u) - (1 - s) * p s := by
    calc
      _ = ∫ u in s..1, p u - p s := by
        apply intervalIntegral.integral_congr_Ioo_of_le hs.2
        intro u hu
        exact max_eq_left (sub_nonneg.mpr (p.monotone hu.1.le))
      _ = _ := by
        rw [intervalIntegral.integral_sub p.monotone.intervalIntegrable intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (a := 0) (b := s))
    (hg.intervalIntegrable (μ := volume) (a := s) (b := 1))
  have hdef : deficit p (p s) = 1 - p s - ∫ u in 0..1, g u := by
    unfold deficit pathMeasure
    dsimp [g]
    rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  rw [hlow, hhigh] at hsum
  unfold pathSymbol
  linarith

theorem spectralGroupSymbol_nonneg (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : ι) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ pathSymbol (spectralGroupDiagonal ρ eig hρ hρsum p a)
      (spectralGroupPath ρ eig hρ hρsum p a) s := by
  have hi := intervalIntegral.integral_mono (μ := volume) hs.2
    (spectralGroupPath_monotone ρ eig hρ hρsum p a).intervalIntegrable
    intervalIntegrable_const
    (spectralGroupPath_le_diagonal ρ eig hρ hρsum p a)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  have hm := mul_le_mul_of_nonneg_left
    (spectralGroupPath_le_diagonal ρ eig hρ hρsum p a s) hs.1
  unfold pathSymbol
  nlinarith

theorem sum_spectralGroupSymbol (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    (∑ a, pathSymbol (spectralGroupDiagonal ρ eig hρ hρsum p a)
      (spectralGroupPath ρ eig hρ hρsum p a) s) = deficit p (p s) := by
  simp only [pathSymbol, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_spectralGroupDiagonal, sum_spectralGroupPath,
    ← intervalIntegral.integral_finsetSum
      (fun a _ => (spectralGroupPath_monotone ρ eig hρ hρsum p a).intervalIntegrable)]
  simp only [sum_spectralGroupPath]
  exact (deficit_at_path_eq_symbol p hs).symm

end InvariantIsing

end

end OAI
