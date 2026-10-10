import OAI.Analysis.MutuallyUnbiased.Moments.AuxiliaryGram
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Basic

namespace OAI

/-!
# Interpreting the certificate's expanded auxiliary functions

The integer tagged terms are ordinary finite linear combinations of the
manuscript's two auxiliary functions. Their real Gram products expand into
the exact mixed-moment expressions used by the certificate. Positive
semidefiniteness of a coefficient matrix proves nonnegativity independently
of how its entries or its finite lists of terms were obtained.
-/

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramFunctions

def LinearForm.auxiliaryEval (P : LinearForm) (B : Fin 7 → Basis) : AuxiliarySample → ℂ :=
  fun ω => P.eval (fun t a => auxiliaryF B t a ω)

/-- Explicit mixed-moment expansion of a pair of integer linear forms. -/
def LinearForm.mixedGram (P Q : LinearForm) (B : Fin 7 → Basis) : ℝ :=
  ∑ i, ∑ j, ((P.terms i).coefficient : ℝ) * ((Q.terms j).coefficient : ℝ) *
    auxiliaryMixedEntry B (P.terms i).tag (Q.terms j).tag
      (P.terms i).charge (Q.terms j).charge

theorem LinearForm.auxiliaryEval_gram (P Q : LinearForm) (B : Fin 7 → Basis)
    (hB : IsMUBFamily B) :
    realGram (P.auxiliaryEval B) (Q.auxiliaryEval B) = P.mixedGram Q B := by
  unfold LinearForm.auxiliaryEval LinearForm.eval LinearForm.mixedGram
  have hcast (z : ℤ) : (z : ℂ) = ((z : ℝ) : ℂ) := by norm_cast
  simp_rw [hcast]
  rw [realGram_weighted_sum]
  simp_rw [auxiliaryGram_eq B hB]

/-- A positive semidefinite matrix proves nonnegativity of the fully
expanded mixed expression for any finite family of integer linear forms. -/
theorem LinearForm.mixedGram_psd_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ι → LinearForm) (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (Z : Matrix ι ι ℝ) (hZ : Z.PosSemidef) :
    0 ≤ ∑ i, ∑ j, Z i j * (P i).mixedGram (P j) B := by
  have h := realGram_psd_nonneg Z hZ (fun i => (P i).auxiliaryEval B)
  simpa only [LinearForm.auxiliaryEval_gram _ _ B hB] using h

end MUB6.Certificate.GramFunctions

end

end OAI
