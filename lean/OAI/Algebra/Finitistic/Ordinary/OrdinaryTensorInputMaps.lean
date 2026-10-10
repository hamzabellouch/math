import OAI.Algebra.Finitistic.Ordinary.OrdinaryTensorFiniteMatrix
import OAI.Algebra.Finitistic.Ordinary.OrdinaryFiniteTotalMaps

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.ComplexTensor
open BalancedTensor
universe u
variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
variable (Q : CochainComplex (ModuleCat.{u} Aᵐᵒᵖ) ℤ)
variable {Z Z' : CochainComplex (ModuleCat.{u} A) ℤ} (f : Z ⟶ Z')

/-- The actual map induced by an input chain map in a single balanced tensor term. -/
def inputMap (p q : ℤ) : term k A Q Z p q →ₗ[k] term k A Q Z' p q :=
  bimap (k := k) (M := rightTerm k A Q p) (M' := rightTerm k A Q p)
    (N := leftTerm k A Z q) (N' := leftTerm k A Z' q) LinearMap.id (f.f q).hom

/-- Input chain maps act on the signed columns by the actual shifted tensor functor. -/
def columnMap (p : ℤ) : column k A Q Z p ⟶ column k A Q Z' p :=
  (shiftFunctor _ (-p)).map
    (((fixedTensorFunctor k A (rightTerm k A Q p)).mapHomologicalComplex (.up ℤ)).map f)

@[simp] theorem columnMap_f (p n : ℤ) :
    ((columnMap k A Q f p).f n).hom = inputMap k A Q f p (n + -p) := by
  apply BalancedTensor.ext
  intro x y
  rfl

theorem inputMap_transport {q q' : ℤ} (h : q=q') :
    eqToHom (congrArg Z.X h) ≫ f.f q' = f.f q ≫ eqToHom (congrArg Z'.X h) := by
  subst q'
  simp only [eqToHom_refl,Category.id_comp,Category.comp_id]

/-- The horizontal tensor differential is natural in the arbitrary input complex. -/
theorem horizontal_inputMap (n p p' : ℤ) (h : p+1=p') :
    (horizontal k A Q Z' n p p' h).comp (inputMap k A Q f p (n + -p)) =
      (inputMap k A Q f p' ((n+1) + -p')).comp (horizontal k A Q Z n p p' h) := by
  unfold horizontal inputMap map
  erw [bimap_comp,bimap_comp,LinearMap.comp_id]
  congr 1
  have hn := inputMap_transport A f (show n + -p = (n+1) + -p' by omega)
  exact congrArg ModuleCat.Hom.hom hn.symm

variable {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)

theorem entry_inputMap (n : ℤ) (i j : Fin l) :
    (entry k A Q Z' p n i j).comp (inputMap k A Q f (p i) (n + -(p i))) =
      (inputMap k A Q f (p j) ((n+1) + -(p j))).comp (entry k A Q Z p n i j) := by
  unfold entry
  split_ifs with h
  · exact horizontal_inputMap k A Q f n (p i) (p j) h
  · simp only [LinearMap.zero_comp,LinearMap.comp_zero]

/-- The full horizontal matrix commutes with the actual input map. -/
theorem matrix_inputMap (n : ℤ) :
    (matrix k A Q Z' p n).comp
      (FiniteColumnComplex.componentMap (columns k A Q Z p) (columns k A Q Z' p)
        (fun i => columnMap k A Q f (p i)) n) =
    (FiniteColumnComplex.componentMap (columns k A Q Z p) (columns k A Q Z' p)
      (fun i => columnMap k A Q f (p i)) (n+1)).comp (matrix k A Q Z p n) := by
  apply LinearMap.ext
  intro z
  funext j
  change matrix k A Q Z' p n
    (FiniteColumnComplex.componentMap (columns k A Q Z p) (columns k A Q Z' p)
      (fun i => columnMap k A Q f (p i)) n z) j =
      ((columnMap k A Q f (p j)).f (n+1)).hom (matrix k A Q Z p n z j)
  simp only [matrix_apply,FiniteColumnComplex.componentMap_apply,columnMap_f]
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun g => g (z i)) (entry_inputMap k A Q f p n i j)
end LittleFinitistic.ComplexTensor

end

end OAI
