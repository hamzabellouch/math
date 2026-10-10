import OAI.Probability.InvariantIsing.Spectral.SpectralFubini
import OAI.Probability.InvariantIsing.Spectral.SpectralGroupRoots
import OAI.Probability.InvariantIsing.Arrays.PathSymbolAEUniqueness

namespace OAI

/-! A canonical group quantile and its diagonal are identified by the
spectral symbols and roots derived from the actual Ward equations. -/

noncomputable section

open MeasureTheory Set Filter Function
open scoped BigOperators Topology

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- Equality with the reconstructed spectral group follows from its
proved symbol and root formulas and the AE path uniqueness theorem. -/
theorem spectralGroup_identification_of_symbol_root (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p q : OverlapPath) (d : ℝ) (a : ι)
    (hsymbol : ∀ᵐ s ∂pathMeasure, pathSymbol d q.val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
    (hroot : Function.rightLim q.val 0 = Function.rightLim p.val 0 *
      projectedResolventDerivative ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0))) :
    d = spectralGroupDiagonal ρ eig hρ hρsum p a ∧
      q.val =ᵐ[pathMeasure] spectralGroupPath ρ eig hρ hρsum p a := by
  have hqB (s : ℝ) : |q s| ≤ 1 := by
    rw [abs_of_nonneg (q.nonneg s)]
    exact q.le_one s
  have hGB (s : ℝ) : |spectralGroupPath ρ eig hρ hρsum p a s| ≤ 1 := by
    rw [abs_of_nonneg (spectralGroupPath_nonneg ρ eig hρ hρsum p a s)]
    exact (spectralGroupPath_le_diagonal ρ eig hρ hρsum p a s).trans
      (spectralGroupDiagonal_le_one ρ eig hρ hρsum p a)
  have heq : ∀ᵐ s ∂pathMeasure, pathSymbol d q.val s =
      pathSymbol (spectralGroupDiagonal ρ eig hρ hρsum p a)
        (spectralGroupPath ρ eig hρ hρsum p a) s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo, hsymbol] with s hs hsym
    exact hsym.trans (spectralGroupSymbol_eq_projectedResolvent ρ eig hρ hρsum p a
      ⟨hs.1.le, hs.2.le⟩).symm
  have hqr : Tendsto q.val (𝓝[>] (0 : ℝ))
      (𝓝 (Function.rightLim p.val 0 * projectedResolventDerivative ρ eig hρ hρsum a
        (deficit p (Function.rightLim p.val 0)))) := by
    rw [← hroot]
    exact q.monotone.tendsto_rightLim 0
  exact ae_equal_pathSymbols_equal_roots q.val (spectralGroupPath ρ eig hρ hρsum p a)
    q.measurable (spectralGroupPath_monotone ρ eig hρ hρsum p a).measurable hqB hGB
    d (spectralGroupDiagonal ρ eig hρ hρsum p a) _ heq hqr
    (spectralGroupPath_root_tendsto ρ eig hρ hρsum p a)

/-- The finite family form keeps all group quantiles on one common full
measure set, as needed for the actual limiting spectral-array law. -/
theorem spectralGroups_identification_of_symbols_roots (ρ eig : ι → ℝ)
    (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1) (p : OverlapPath)
    (q : ι → OverlapPath) (d : ι → ℝ)
    (hsymbol : ∀ a, ∀ᵐ s ∂pathMeasure, pathSymbol (d a) (q a).val s =
      projectedResolvent ρ eig hρ hρsum a (deficit p (p s)))
    (hroot : ∀ a, Function.rightLim (q a).val 0 = Function.rightLim p.val 0 *
      projectedResolventDerivative ρ eig hρ hρsum a (deficit p (Function.rightLim p.val 0))) :
    (∀ a, d a = spectralGroupDiagonal ρ eig hρ hρsum p a) ∧
      ∀ᵐ s ∂pathMeasure, ∀ a, q a s = spectralGroupPath ρ eig hρ hρsum p a s := by
  have he (a : ι) := spectralGroup_identification_of_symbol_root ρ eig hρ hρsum p (q a) (d a) a
    (hsymbol a) (hroot a)
  exact ⟨fun a => (he a).1, ae_all_iff.mpr fun a => (he a).2⟩

end InvariantIsing

end

end OAI
