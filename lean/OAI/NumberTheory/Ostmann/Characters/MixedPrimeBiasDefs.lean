import OAI.NumberTheory.Ostmann.Preliminaries.ResidueSupports
import OAI.NumberTheory.Ostmann.Supply.Fourier
import OAI.NumberTheory.Ostmann.Tree.Fourier

namespace OAI

noncomputable section
namespace Ostmann.Characters
attribute [local instance] Classical.propDecidable

def mixedPrimeBias (d : Decomposition) (p : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    (FiniteField.correlationBound (Supply.additiveTransform (d.residueSupport p)):ℝ)
  else 0

@[simp] theorem mixedPrimeBias_prime (d : Decomposition) (p : ℕ) [Fact p.Prime] :
    mixedPrimeBias d p =
      (FiniteField.correlationBound (Supply.additiveTransform (d.residueSupport p)):ℝ) := by
  simp [mixedPrimeBias,Fact.out]

theorem mixedPrimeBias_nonneg (d : Decomposition) (p : ℕ) : 0 ≤ mixedPrimeBias d p := by
  unfold mixedPrimeBias
  split_ifs <;> positivity

end Ostmann.Characters

end

end OAI
