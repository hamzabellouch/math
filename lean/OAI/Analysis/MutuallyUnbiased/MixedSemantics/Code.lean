import OAI.Analysis.MutuallyUnbiased.Matrix.Definitions
import OAI.Analysis.MutuallyUnbiased.Certificate.Algebra

namespace OAI

namespace MUB6.Certificate.MixedSemantics

/-- A finite integer mixed-moment descriptor, retaining every index size. -/
structure Code where
  rows : ℕ
  factors : ℕ
  labels : ℕ
  matrix : Matrix (Fin rows) (Fin factors) ℤ
  label : Fin factors → Fin labels

instance : Inhabited Code := ⟨⟨0, 0, 0, 0, Fin.elim0⟩⟩

/-- Pair coordinates and all elementary mixed nodes share one ambient space.
The numerical certificate is reindexed into this space separately. -/
abbrev Master := Fin 909 ⊕ Fin 5502

end MUB6.Certificate.MixedSemantics

end OAI
