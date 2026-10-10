import OAI.Analysis.KadisonKastler.HilbertConjugation
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

namespace OAI

/-! # Bounded logarithmic approximations to the modular group

The logarithmic generator of the graph resolvent is regularized at both
endpoints. Each approximation is an actual norm-continuous unitary group.
The strong limit and its modular properties are subsequent constructions.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real scaling written through the complex scalar action. -/
def scaleSelfAdjoint (a : selfAdjoint (H →L[ℂ] H)) (t : ℝ) : selfAdjoint (H →L[ℂ] H) :=
  ⟨(t : ℂ) • a.val, by
    change star ((t : ℂ) • a.val) = (t : ℂ) • a.val
    rw [star_smul, a.property.star_eq]
    simp⟩

private theorem scaleSelfAdjoint_add (a : selfAdjoint (H →L[ℂ] H)) (s t : ℝ) :
    scaleSelfAdjoint a (s + t) = scaleSelfAdjoint a s + scaleSelfAdjoint a t := by
  apply Subtype.ext
  change ((s + t : ℝ) : ℂ) • a.val = (s : ℂ) • a.val + (t : ℂ) • a.val
  rw [Complex.ofReal_add, add_smul]

/-- Exponentiation of a bounded self-adjoint generator. -/
def boundedSelfAdjointGroup (a : selfAdjoint (H →L[ℂ] H)) :
    Multiplicative ℝ →* unitary (H →L[ℂ] H) where
  toFun t := selfAdjoint.expUnitary (scaleSelfAdjoint a (Multiplicative.toAdd t))
  map_one' := by
    change selfAdjoint.expUnitary (scaleSelfAdjoint a 0) = 1
    have hzero : scaleSelfAdjoint a 0 = 0 := by apply Subtype.ext; simp [scaleSelfAdjoint]
    rw [hzero, selfAdjoint.expUnitary_zero]
  map_mul' s t := by
    change selfAdjoint.expUnitary (scaleSelfAdjoint a
      (Multiplicative.toAdd s + Multiplicative.toAdd t)) = _
    rw [scaleSelfAdjoint_add]
    apply Commute.expUnitary_add
    exact ((Commute.refl a.val).smul_left ((Multiplicative.toAdd s : ℝ) : ℂ)).smul_right
      ((Multiplicative.toAdd t : ℝ) : ℂ)

theorem boundedSelfAdjointGroup_continuous (a : selfAdjoint (H →L[ℂ] H)) :
    Continuous (fun t : ℝ => boundedSelfAdjointGroup a (Multiplicative.ofAdd t)) := by
  have hscale : Continuous (scaleSelfAdjoint a) :=
    (Complex.continuous_ofReal.smul continuous_const).subtype_mk _
  exact selfAdjoint.continuous_expUnitary.comp hscale

theorem boundedSelfAdjointGroup_stronglyContinuous (a : selfAdjoint (H →L[ℂ] H)) (x : H) :
    Continuous (fun t : ℝ =>
      (boundedSelfAdjointGroup a (Multiplicative.ofAdd t) : H →L[ℂ] H) x) :=
  (continuous_subtype_val.comp (boundedSelfAdjointGroup_continuous a)).clm_apply continuous_const

/-- The bounded approximation to `log ((1-R)/R)`. -/
def regularizedModularLog (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (ε : ℝ) : selfAdjoint (H →L[ℂ] H) :=
  ⟨CFC.log (1 - graphResolvent M J Ω 1 + algebraMap ℝ (H →L[ℂ] H) ε) -
      CFC.log (graphResolvent M J Ω 1 + algebraMap ℝ (H →L[ℂ] H) ε),
    IsSelfAdjoint.log.sub IsSelfAdjoint.log⟩

/-- The regularized unitary groups used to approach the modular group. -/
def regularizedModularGroup (M : VonNeumannAlgebra H) (J : H ≃ₗᵢ⋆[ℂ] H)
    (Ω : H) (ε : ℝ) : Multiplicative ℝ →* unitary (H →L[ℂ] H) :=
  boundedSelfAdjointGroup (regularizedModularLog M J Ω ε)

theorem regularizedModularGroup_stronglyContinuous (M : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (ε : ℝ) (x : H) :
    Continuous (fun t : ℝ =>
      (regularizedModularGroup M J Ω ε (Multiplicative.ofAdd t) : H →L[ℂ] H) x) :=
  boundedSelfAdjointGroup_stronglyContinuous _ x

end

end KadisonKastler

end OAI
