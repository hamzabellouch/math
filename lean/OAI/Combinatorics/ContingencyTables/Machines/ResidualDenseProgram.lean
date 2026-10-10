import OAI.Combinatorics.ContingencyTables.Rooted.LargeMarginProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseCanonicalProgram

namespace OAI

/-! # A computed dense completion call from a retained small profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

abbrev ResidualParameters := (ProfileCheckData×ℕ)×(ℕ×ℕ)
abbrev ResidualDrawData := ResidualParameters×List Bool

def residualParameters (z : ResidualParameters) : DensePrograms.CanonicalParameters :=
  ((profilePaddedMargins true z.1,profilePaddedMargins false z.1),z.2)

def residualParametersRealizer : Realizer residualParameters := by
  let rows : Realizer (fun z : ResidualParameters => profilePaddedMargins true z.1) :=
    composition (f := fun z : ResidualParameters => z.1) (g := profilePaddedMargins true)
      first (profilePaddedMarginsRealizer true)
  let columns : Realizer (fun z : ResidualParameters => profilePaddedMargins false z.1) :=
    composition (f := fun z : ResidualParameters => z.1) (g := profilePaddedMargins false)
      first (profilePaddedMarginsRealizer false)
  exact pair (pair rows columns) second

theorem polynomial_residualParameters : PolynomialTime residualParametersRealizer := by
  unfold residualParametersRealizer
  exact polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_profilePaddedMargins true))
    (polynomial_composition polynomial_first (polynomial_profilePaddedMargins false)))
    polynomial_second

def residualDenseDraw (z : ResidualDrawData) : DensePrograms.MatrixCode :=
  DensePrograms.canonicalDenseDraw (residualParameters z.1,z.2)

def residualDenseDrawRealizer : Realizer residualDenseDraw :=
  composition (pair (composition first residualParametersRealizer) second)
    DensePrograms.canonicalDenseDrawRealizer

/-- The actual completion call computes the residual margins, selects
their large rectangle, initializes it, and draws a dense matrix. -/
theorem polynomial_residualDenseDraw : PolynomialTime residualDenseDrawRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_residualParameters) polynomial_second)
    DensePrograms.polynomial_canonicalDenseDraw

end ContingencyTables.ProfilePrograms

end OAI
