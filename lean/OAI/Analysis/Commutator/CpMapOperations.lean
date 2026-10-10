import Mathlib
import OAI.Analysis.Commutator.CpCompression
import OAI.Analysis.Commutator.OperatorSystem
import OAI.Analysis.Commutator.StinespringDilation

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder CStarAlgebra

namespace Kadison.CpOperations

variable {A B C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

def comp (g : B →CP C) (f : A →CP B) : A →CP C where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_cstarMatrix_nonneg' n X hX := by
    have h := g.map_cstarMatrix_nonneg _ (f.map_cstarMatrix_nonneg X hX)
    convert h using 1
    ext i j
    rfl

@[simp] lemma comp_apply (g : B →CP C) (f : A →CP B) (a : A) : comp g f a=g (f a) := rfl

lemma isCompletelyPositive_comp (S : Submodule ℂ A) (f : S →ₗ[ℂ] B)
    (hf : OperatorSystem.IsCompletelyPositive S f) (g : B →CP C) :
    OperatorSystem.IsCompletelyPositive S (g.toLinearMap.comp f) := by
  intro ι _ X hX
  have h := g.map_cstarMatrix_nonneg _ (hf ι X hX)
  convert h using 1
  ext i j
  rfl

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def compression (V : K →L[ℂ] H) : (H →L[ℂ] H) →CP (K →L[ℂ] K) :=
  CpCompression.compression (StarAlgHom.id ℂ (H →L[ℂ] H)) V

@[simp] lemma compression_apply (V : K →L[ℂ] H) (T : H →L[ℂ] H) :
    compression V T=V.adjoint.comp (T.comp V) := rfl

lemma norm_apply_le (φ : A →CP (H →L[ℂ] H)) (a : A) : ‖φ a‖≤‖φ 1‖*‖a‖ := by
  rw [Stinespring.factorization φ a]
  have hρ : ‖Stinespring.representation φ a‖≤‖a‖ := NonUnitalStarAlgHom.norm_apply_le (Stinespring.representation φ) a
  calc
    _ ≤ ‖(Stinespring.embedding φ).adjoint‖ * (‖Stinespring.representation φ a‖ * ‖Stinespring.embedding φ‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ ‖Stinespring.embedding φ‖ * (‖a‖ * ‖Stinespring.embedding φ‖) := by
      simp only [LinearIsometryEquiv.norm_map]
      gcongr
    _ = ‖φ 1‖*‖a‖ := by rw [←Stinespring.embedding_norm_sq]; ring

end Kadison.CpOperations

end

end
end

end OAI
