import OAI.Algebra.Finitistic.Ordinary.OrdinaryResolutionModels
import OAI.Algebra.Finitistic.Ordinary.OrdinaryXAugmentation
import OAI.Algebra.Finitistic.Ordinary.OrdinaryShiftDerivedTensor

namespace OAI
noncomputable section
open CategoryTheory Limits
open scoped TensorProduct
namespace LittleFinitistic.OrdinarySimulation
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]

namespace TensorResolution

theorem finiteDegrees_range (l : ℕ) (n : ℤ) : n ∈ Set.range (finiteDegrees l) ↔ -(l:ℤ) ≤ n ∧ n ≤ 0 := by
  constructor
  · rintro ⟨i,rfl⟩
    dsimp [finiteDegrees]
    have hi := i.isLt
    omega
  · rintro ⟨hlo,hhi⟩
    let j := (n+(l:ℤ)).toNat
    have hj : (j:ℤ) = n+(l:ℤ) := Int.toNat_of_nonneg (by omega)
    refine ⟨⟨j,by omega⟩,?_⟩
    dsimp [finiteDegrees]
    omega

/-- The actual Q_T augmentation with all source resolution obligations proved. -/
def resolutionModel (k B : Type u) [Field k] [Ring B] [Algebra k B] (l : ℕ) :
    BoundedBimoduleResolution k B (B ⊗[k] ChainAlgebra k l) (bimoduleTerminalObject k B l) where
  complex := integerBimoduleComplex k B l
  size := l+1
  degrees := finiteDegrees l
  strictMono := finiteDegrees_strictMono l
  support n hn := by
    have h : n < -(l:ℤ) ∨ 0 < n := by
      have := (finiteDegrees_range l n).not.mp hn
      omega
    exact h.elim (integerBimodule_lower k B l n) (integerBimodule_upper k B l n)
  rightProjective n := integerBimoduleRight_projective k B l n
  augmentation := integerBimoduleAugmentation k B l
  augmentation_quasiIso := integerBimoduleAugmentation_quasiIso k B l
end TensorResolution

variable (P : CochainComplex (ModuleCat.{u} (Enveloping k B)) ℤ) (a : ℤ) (l : ℕ)
variable [∀ n, Module.Projective Bᵐᵒᵖ ((underlyingRightComplex P).X n)]

/-- The actual Q_X resolution with no assumed augmentation, projectivity, or support theorem. -/
def XResolution.resolutionModel :
    BoundedBimoduleResolution k (AlgebraD k l B) (AlgebraD k l B) (XResolution.ordinaryXObject P a l) where
  complex := XResolution.complex P a l
  size := l+1
  degrees := TensorResolution.finiteDegrees l
  strictMono := TensorResolution.finiteDegrees_strictMono l
  support n hn := by
    apply XResolution.vanishes P a l n
    have := (TensorResolution.finiteDegrees_range l n).not.mp hn
    omega
  rightProjective n := XResolution.right_projective P a l n
  augmentation := XResolution.augmentationToX P a l
  augmentation_quasiIso := XResolution.augmentationToX_quasiIso P a l

/-- The actual P[b] itself is a finite right-projective tensor model with exactly the source support. -/
def shiftedResolutionModel (b : ℤ) (hb : a+(l:ℤ)=b)
    (hP : ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) : FiniteProjectiveBimoduleComplex k B B where
  complex := P⟦b⟧
  size := l+1
  degrees := TensorResolution.finiteDegrees l
  strictMono := TensorResolution.finiteDegrees_strictMono l
  support n hn := by
    change IsZero (P.X (n+b))
    apply hP
    have := (TensorResolution.finiteDegrees_range l n).not.mp hn
    omega
  rightProjective n := shifted_right_projective P b n
end LittleFinitistic.OrdinarySimulation

end

end OAI
