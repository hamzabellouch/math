import OAI.Analysis.MutuallyUnbiased.Matrix.Definitions

namespace OAI

namespace MUB6.Certificate.GramFunctions

open scoped BigOperators

structure TaggedTerm where
  tag : Fin 2
  charge : Charge
  coefficient : ℤ
  deriving Inhabited

structure LinearForm where
  size : ℕ
  terms : Fin size → TaggedTerm
  deriving Inhabited

noncomputable def LinearForm.eval (P : LinearForm) (F : Fin 2 → Charge → ℂ) : ℂ :=
  ∑ i, ((P.terms i).coefficient : ℂ) * F (P.terms i).tag (P.terms i).charge

end MUB6.Certificate.GramFunctions

end OAI
