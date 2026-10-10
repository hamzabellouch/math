import OAI.Analysis.SeparableQuotients.NegativeComplex

namespace OAI

namespace SeparableQuotient

universe u

theorem negative_main (hCH : CH) : ¬ SQ.{u} ℝ ∧ ¬ SQ.{u} ℂ :=
  ⟨negative_real hCH, negative_complex hCH⟩

end SeparableQuotient

end OAI
