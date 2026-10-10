import Mathlib
import OAI.NumberTheory.CubicGauss.Eisenstein
import OAI.NumberTheory.CubicGram.GaussCharacters

namespace OAI

/-! Prime cutoffs and literal cubic residue characters with normalized Gauss sums. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

open UniqueFactorizationMonoid
end CubicFirstMoment
end

end OAI
