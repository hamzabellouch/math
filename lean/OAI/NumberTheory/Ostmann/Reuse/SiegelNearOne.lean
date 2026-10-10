import OAI.NumberTheory.Jacobsthal.Siegel.NormLogDerivLFunctionNegLogDerivZeta
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.LocallyUniformLimit

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Complex DirichletCharacter

namespace Ostmann.Dirichlet

theorem exists_near_one_zero_unique_real_simple :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) (hq : 3 ≤ q),
      let _ : NeZero q := ⟨by omega⟩
      ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive → χ ≠ 1 →
      (∀ a : ZMod q, (χ a).im = 0) → ∀ z : ℂ,
      ‖z - 1‖ ≤ c / Real.log q → LFunction χ z = 0 →
      z.im = 0 ∧ analyticOrderAt (LFunction χ) z = 1 ∧
        ∀ w : ℂ, ‖w - 1‖ ≤ c / Real.log q → LFunction χ w = 0 → w = z :=
  Erdos970.WeightedTorusJets.exists_classical_near_one_zero_unique_real_simple

end Ostmann.Dirichlet

end OAI
