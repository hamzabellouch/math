import OAI.Analysis.MutuallyUnbiased.TaoCertificate.Merged
import OAI.Analysis.MutuallyUnbiased.TaoCertificate.TargetMerge13

namespace OAI

namespace MUB6.TaoCertificate
open TaoArithmetic

theorem source_eq_target : combined478 = targetCombined13 := by rfl

/-- The exact source-derived Tao exclusion certificate contradicts cubic positivity. -/
theorem tao_exclusion (f : Charge → ℂ)
    (hcross : ∀ a c, Balanced a → Balanced c →
      offDiagSum (fun i j => f (a + difference i j) *
        star (g tao (c + difference i j))) = 0)
    (horder : OrderTwoValues f)
    (hpositive : 0 ≤ 6 + offDiagSum (fun i j => (f ((3 : ℤ) • difference i j)).re)) : False := by
  have hz := combined478_zero f hcross
  rw [source_eq_target, targetCombined13_value f horder] at hz
  linarith

end MUB6.TaoCertificate

end OAI
