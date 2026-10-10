import OAI.Algebra.Finitistic.Ordinary.OrdinaryBimoduleTotalMaps
import OAI.Algebra.Finitistic.Ordinary.OrdinaryRestrictionHomology
import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorTotalQuasiIso

namespace OAI
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace LittleFinitistic.BimoduleComplexTensor
universe u
variable (k S A : Type u) [Field k] [Ring S] [Ring A] [Algebra k S] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} (S ⊗[k] Aᵐᵒᵖ)) ℤ)
variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

/-- The actual tensor total is a functor retaining its outside action on every complex. -/
def totalFunctor : CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} S) ℤ where
  obj Z := total k S A Q Z p hp
  map f := totalMap k S A Q f p hp
  map_id Z := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    change termInputMap k S A Q (𝟙 Z) (p i) (n + -(p i)) (z i) = z i
    rw [termInputMap_id]
    rfl
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    funext i
    change termInputMap k S A Q (f ≫ g) (p i) (n + -(p i)) (z i) =
      termInputMap k S A Q g (p i) (n + -(p i)) (termInputMap k S A Q f (p i) (n + -(p i)) (z i))
    rw [termInputMap_comp]
    rfl

/-- The forgetful chain comparison is natural in all input complexes. -/
def forgetTotalFunctorIso :
    totalFunctor k S A Q p hp ⋙ (ModuleCat.restrictScalars (algebraMap k S)).mapHomologicalComplex (.up ℤ) ≅
    ComplexTensor.finiteTotalFunctor k A (rightComplex k S A Q) p hp :=
  NatIso.ofComponents (fun Z => forgetTotalIso k S A Q Z p hp)
    (fun f => forgetTotalIso_natural k S A Q f p hp)

/-- The genuine outside-action tensor preserves arbitrary quasi-isomorphisms when its right terms
are projective. There are no restrictions on either input complex. -/
theorem totalFunctor_quasiIso
    [∀ i, Module.Projective Aᵐᵒᵖ (ComplexTensor.rightTerm k A (rightComplex k S A Q) (p i))]
    {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z') [QuasiIso f] :
    QuasiIso ((totalFunctor k S A Q p hp).map f) := by
  apply (RestrictionHomology.quasiIso_iff (algebraMap k S) _).mp
  let g := ((ModuleCat.restrictScalars (algebraMap k S)).mapHomologicalComplex (.up ℤ)).map
    (totalMap k S A Q f p hp)
  have := ComplexTensor.finiteTotalMap_quasiIso k A (rightComplex k S A Q) f p hp
  have hg : QuasiIso (g ≫ (forgetTotalIso k S A Q Z' p hp).hom) := by
    dsimp only [g]
    rw [forgetTotalIso_natural]
    infer_instance
  exact (quasiIso_iff_comp_right g (forgetTotalIso k S A Q Z' p hp).hom).mp hg
end LittleFinitistic.BimoduleComplexTensor

end

end OAI
