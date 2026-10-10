import OAI.Analysis.KadisonKastler.TwoRatioParameters
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Sum

namespace OAI

/-! # Reindexing the extra family of lambda sites

Even and odd lambda sites absorb a second countable family. Mu sites
are unchanged. This is the explicit state-preserving bijection used in
the pointed infinite tensor-product absorption argument.
-/

namespace KadisonKastler

noncomputable section

abbrev TwoRatioSite := ℕ ⊕ ℕ

def twoRatioSiteParameter : TwoRatioSite → ℝ :=
  Sum.elim (fun _ => fixedProductLambda) (fun _ => fixedProductMu)

/-- Interleave the original and extra lambda families, leaving mu sites
in their original order. -/
def lambdaAbsorptionSiteEquiv : (TwoRatioSite ⊕ ℕ) ≃ TwoRatioSite :=
  (Equiv.sumAssoc ℕ ℕ ℕ).trans
    ((Equiv.sumCongr (Equiv.refl ℕ) (Equiv.sumComm ℕ ℕ)).trans
      ((Equiv.sumAssoc ℕ ℕ ℕ).symm.trans
        (Equiv.sumCongr Equiv.natSumNatEquivNat (Equiv.refl ℕ))))

@[simp] theorem lambdaAbsorptionSiteEquiv_old_lambda (n : ℕ) :
    lambdaAbsorptionSiteEquiv (Sum.inl (Sum.inl n)) = Sum.inl (2 * n) := rfl

@[simp] theorem lambdaAbsorptionSiteEquiv_new_lambda (n : ℕ) :
    lambdaAbsorptionSiteEquiv (Sum.inr n) = Sum.inl (2 * n + 1) := rfl

@[simp] theorem lambdaAbsorptionSiteEquiv_mu (n : ℕ) :
    lambdaAbsorptionSiteEquiv (Sum.inl (Sum.inr n)) = Sum.inr n := rfl

/-- Each site retains its density matrix parameter under the bijection. -/
theorem lambdaAbsorptionSiteEquiv_preserves_parameter (i : TwoRatioSite ⊕ ℕ) :
    twoRatioSiteParameter (lambdaAbsorptionSiteEquiv i) =
      Sum.elim twoRatioSiteParameter (fun _ => fixedProductLambda) i := by
  rcases i with ((n | n) | n) <;> rfl

/-- The individual diagonal weights of the two-dimensional state. -/
def twoSiteWeight (ν : ℝ) (i : Fin 2) : ℝ :=
  if i = 0 then (1 + ν)⁻¹ else ν / (1 + ν)

theorem lambdaAbsorptionSiteEquiv_preserves_weight (i : TwoRatioSite ⊕ ℕ) (j : Fin 2) :
    twoSiteWeight (twoRatioSiteParameter (lambdaAbsorptionSiteEquiv i)) j =
      twoSiteWeight (Sum.elim twoRatioSiteParameter (fun _ => fixedProductLambda) i) j := by
  rw [lambdaAbsorptionSiteEquiv_preserves_parameter]

end

end KadisonKastler

end OAI
