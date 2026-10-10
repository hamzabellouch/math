import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalTerms

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable {k B : Type u} [Field k] [Ring B] [Algebra k B]
variable {P : BiComplex k B} {Z Z' Z'' : CochainComplex (ModuleCat.{u} B) ℤ}
variable {p p' p'' q q' q'' : ℤ}

def termMap (f : P.X p ⟶ P.X p') (g : Z.X q ⟶ Z'.X q') :
    Term k B P Z p q →ₗ[B] Term k B P Z' p' q' where
  __ := (@BalancedTensor.bimap k B
    (ComplexTensor.rightTerm k B (right k B P) p)
    (ComplexTensor.rightTerm k B (right k B P) p')
    (ComplexTensor.leftTerm k B Z q) (ComplexTensor.leftTerm k B Z' q') _ _ _
    _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p))
    _ _ _ (BalancedTensor.scalarLeftTower k Bᵐᵒᵖ ((right k B P).X p'))
    _ _ _ (BalancedTensor.scalarLeftTower k B (Z.X q))
    _ _ _ (BalancedTensor.scalarLeftTower k B (Z'.X q'))
    ((forgetRight k B).map f).hom g.hom).toAddMonoidHom
  map_smul' := bimap_smul f g

@[simp] theorem termMap_comp
    (f : P.X p ⟶ P.X p') (f' : P.X p' ⟶ P.X p'')
    (g : Z.X q ⟶ Z'.X q') (g' : Z'.X q' ⟶ Z''.X q'') :
    (termMap f' g').comp (termMap f g) = termMap (f ≫ f') (g ≫ g') := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)


@[simp] theorem termMap_id : termMap (𝟙 (P.X p)) (𝟙 (Z.X q)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using BalancedTensor.induction_on with
  | hz => simp
  | ht m n => rfl
  | ha x y hx hy =>
    exact (map_add _ _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)

/-- Right-degree transport keeps the actual balanced tensor and the full left action. -/
def rightDegreeIso (P : BiComplex k B) (Z : CochainComplex (ModuleCat.{u} B) ℤ)
    (p q q' : ℤ) (h : q=q') :
    ModuleCat.of B (Term k B P Z p q) ≅ ModuleCat.of B (Term k B P Z p q') :=
  eqToIso (congrArg (fun q => ModuleCat.of B (Term k B P Z p q)) h)
end LittleFinitistic.BimoduleTotal

end

end OAI
