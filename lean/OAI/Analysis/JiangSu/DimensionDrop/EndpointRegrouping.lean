import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.SpectralFamilies

namespace OAI

section

noncomputable section
namespace JiangSuConstruction
open scoped ComplexOrder CStarAlgebra

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable {p q P Q : ℕ} {ρ : Type*} [Fintype ρ] [DecidableEq ρ]

lemma connectingAmbient_injective (ξ : ρ → C(Interval,Interval))
    (e : ((Fin p×Fin q)×ρ)≃(Fin P×Fin Q))
    (u₀ u₁ : unitary (TensorMat P Q)) (k : ρ) (hk : Function.Surjective (ξ k)) :
    Function.Injective (connectingAmbient ξ e u₀ u₁) :=
  (continuousUnitaryConjugation_injective _).comp
    ((continuousReindex_injective e).comp (diagonalContinuousHom_injective ξ k hk))

lemma connectingMap_injective (ξ : ρ → C(Interval,Interval))
    (e : ((Fin p×Fin q)×ρ)≃(Fin P×Fin Q)) (u₀ u₁ : unitary (TensorMat P Q))
    (h₀ h₁) (k : ρ) (hk : Function.Surjective (ξ k)) :
    Function.Injective (connectingMap ξ e u₀ u₁ h₀ h₁) := by
  intro f g h
  apply Subtype.ext
  apply connectingAmbient_injective ξ e u₀ u₁ k hk
  exact congrArg (fun x : DimensionDrop P Q => (x : C(Interval,TensorMat P Q))) h

end JiangSuConstruction

end
end

end OAI
