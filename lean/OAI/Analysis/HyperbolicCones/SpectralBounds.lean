import OAI.Analysis.HyperbolicCones.PositiveMaps
import OAI.Analysis.HyperbolicCones.PencilConjugation

namespace OAI

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

def minimumEigenvalue (X : Sym 4) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (sym_isHermitian X).eigenvalues

theorem minimumEigenvalue_pos (X : Sym 4) (hX : (X : Mat 4 ℝ).PosDef) :
    0 < minimumEigenvalue X := by
  apply (Finset.lt_inf'_iff _).mpr
  intro i _
  exact hX.eigenvalues_pos i

theorem minimumEigenvalue_smul_le (X : Sym 4) :
    minimumEigenvalue X • (1 : Mat 4 ℝ) ≤ (X : Mat 4 ℝ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  apply (algebraMap_le_iff_le_spectrum (R := ℝ) (p := IsSelfAdjoint) X.property).mpr
  intro x hx
  rw [(sym_isHermitian X).spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact Finset.inf'_le _ (Finset.mem_univ i)

theorem positive_unital_map_minimumEigenvalue_bound {n : ℕ}
    (D : Sym 4 →ₗ[ℝ] Sym n)
    (hD : ∀ X : Sym 4, (X : Mat 4 ℝ).PosSemidef → (D X : Mat n ℝ).PosSemidef)
    (hI : D 1 = 1) (X : Sym 4) :
    minimumEigenvalue X • (1 : Mat n ℝ) ≤ (D X : Mat n ℝ) := by
  have h := positiveLinearMap_monotone D hD (minimumEigenvalue X • 1) X
    (minimumEigenvalue_smul_le X)
  simpa [hI] using h

end Paper256

end

end OAI
