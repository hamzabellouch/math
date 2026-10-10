import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalFunctor

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

abbrev forget := (ModuleCat.restrictScalars (algebraMap k B)).mapHomologicalComplex (.up ℤ)

variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

def underlyingTerm (n : ℤ) :
    ((forget k B).obj (total k B P p hp Z)).X n ≃ₗ[k]
      (vectorTotal k B P p hp Z).X n where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    funext i
    exact BimoduleBalancedTensor.algebraMap_smul k B (P.X (p i))
      (ComplexTensor.leftTerm k B Z (n + -(p i))) c (x i)

/-- Forgetting the full left action recovers the frozen signed tensor total with its actual differential. -/
def underlyingIso : (forget k B).obj (total k B P p hp Z) ≅ vectorTotal k B P p hp Z :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (underlyingTerm k B P p hp Z n).toModuleIso)
    (by intros n m h; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl)

/-- The comparison preserves the original maps in the arbitrary input complex. -/
def underlyingComparison :
    functor k B P p hp ⋙ forget k B ≅ ComplexTensor.finiteTotalFunctor k B (right k B P) p hp :=
  NatIso.ofComponents (underlyingIso k B P p hp) (by
    intros Z Z' f
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

instance restrictPreservesHomology :
    (ModuleCat.restrictScalars (algebraMap k B)).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (fun S hS => by
    rw [ShortComplex.moduleCat_exact_iff] at hS ⊢
    exact hS)

/-- The frozen K-flatness proof applies to the total with its complete B action. -/
theorem totalMap_quasiIso
    [∀ i, Module.Projective Bᵐᵒᵖ (ComplexTensor.rightTerm k B (right k B P) (p i))]
    {Z Z' : CochainComplex (ModuleCat.{u} B) ℤ} (f : Z ⟶ Z') [QuasiIso f] :
    QuasiIso (totalMap k B P p hp f) := by
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    (totalMap k B P p hp f) (ModuleCat.restrictScalars (algebraMap k B))).mp
  let e : Arrow.mk ((forget k B).map (totalMap k B P p hp f)) ≅
      Arrow.mk (ComplexTensor.finiteTotalMap k B (right k B P) p hp f) := Arrow.isoMk (underlyingIso k B P p hp Z) (underlyingIso k B P p hp Z')
    ((underlyingComparison k B P p hp).hom.naturality f).symm
  apply (quasiIso_iff_of_arrow_mk_iso _ _ e).mpr
  exact ComplexTensor.finiteTotalMap_quasiIso k B (right k B P) f p hp
end LittleFinitistic.BimoduleTotal

end

end OAI
