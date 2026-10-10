import OAI.NumberTheory.Ostmann.Tree.PairCoordinates
import OAI.NumberTheory.Ostmann.Tree.PairMobius

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
variable {F : Type*} [Field F]

def affinePairParameter (σ lam : Fˣ) (d : F) : F :=
  pairMobiusValue (lam/σ) (1-(lam:F)*d)

theorem affinePairParameter_formula (σ lam : Fˣ) (d : F) :
    affinePairParameter σ lam d = ((lam:F)*d-1)/((σ:F)*d) := by
  by_cases hd : d=0
  · simp [affinePairParameter,pairMobiusValue,hd]
  · dsimp [affinePairParameter,pairMobiusValue]
    rw [Units.val_div_eq_div_val]
    field_simp
    ring

theorem affinePairParameter_inv (σ lam : Fˣ) (d : F) :
    (affinePairParameter σ lam d)⁻¹=pairSecond σ d ((lam:F)*d) := by
  rw [affinePairParameter_formula, inv_div]
  rfl

theorem affinePairParameter_transformed (σ lam : Fˣ) (d : F) :
    affinePairParameter σ lam d-(affinePairParameter σ lam d)^2*((σ:F)/(lam:F)) =
      ((lam:F)*d-1)/((σ:F)*(lam:F)*d^2) := by
  rw [affinePairParameter_formula]
  by_cases hd : d=0
  · simp [hd]
  · field_simp
    ring

theorem affinePairParameter_transformed_inv (σ lam : Fˣ) (d : F) :
    (affinePairParameter σ lam d-(affinePairParameter σ lam d)^2*((σ:F)/(lam:F)))⁻¹ =
      pairFirst σ d ((lam:F)*d) := by
  rw [affinePairParameter_transformed, inv_div]
  dsimp [pairFirst]
  ring

end
end Ostmann.FiniteField

end OAI
