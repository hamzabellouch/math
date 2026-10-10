import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

namespace OAI

/-! The tangent and its quarter-turn form an invertible real planar frame. -/
open Function
noncomputable section
namespace CircleDomainRigidity

def complexTangentFrame (k : ℂ) : (ℝ × ℝ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight k +
  (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (Complex.I * k)

lemma complexTangentFrame_apply (k : ℂ) (v : ℝ × ℝ) :
    complexTangentFrame k v = v.1 • k + v.2 • (Complex.I * k) := rfl

lemma complexTangentFrame_eq_mul (k : ℂ) (v : ℝ × ℝ) :
    complexTangentFrame k v = Complex.equivRealProdCLM.symm v * k := by
  rw [complexTangentFrame_apply,Complex.equivRealProdCLM_symm_apply]
  simp only [Complex.real_smul]
  ring

lemma complexTangentFrame_bijective {k : ℂ} (hk : k ≠ 0) :
    Bijective (complexTangentFrame k) := by
  constructor
  · intro v w he
    rw [complexTangentFrame_eq_mul,complexTangentFrame_eq_mul] at he
    exact Complex.equivRealProdCLM.symm.injective (mul_right_cancel₀ hk he)
  · intro w
    refine ⟨Complex.equivRealProdCLM (w/k),?_⟩
    rw [complexTangentFrame_eq_mul,ContinuousLinearEquiv.symm_apply_apply,div_mul_cancel₀ _ hk]

end CircleDomainRigidity

end

end OAI
