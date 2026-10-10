import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.PointFiberEvaluation

namespace OAI

section
open CategoryTheory Classical Set MonoidalCategory
namespace SimpleAmenable.PolygonObject.Labelled.PointFiber

variable {a n : ℕ}
noncomputable def muEval (U V : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) :
    FiniteSetGroupoid.sum (E.obj U b) (E.obj V b) ⟶ E.obj (sum U V) b := mu U V b
@[simp] lemma muEval_inl (U V : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) (x : Fiber U b) :
    muEval U V b (FiniteSetGroupoid.sumEquiv _ _ (.inl (enumerate U b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inl x)) := mu_inl U V b x
@[simp] lemma muEval_inr (U V : Labelled a n) (b : GenericSquare a × (Fin n → CutRing × CutRing)) (x : Fiber V b) :
    muEval U V b (FiniteSetGroupoid.sumEquiv _ _ (.inr (enumerate V b x)))=
      enumerate (sum U V) b (fiberSum U V b (.inr x)) := mu_inr U V b x
noncomputable def epsEval (b : GenericSquare a × (Fin n → CutRing × CutRing)) :
    FiniteSetGroupoid.empty ⟶ E.obj (empty (a:=a) (n:=n)) b := eps b
lemma mu_assoc (U V W : Labelled a n) :
    mu U V ▷ E.obj W ≫ mu (U⊗V) W ≫ E.map (α_ U V W).hom =
      (α_ (E.obj U) (E.obj V) (E.obj W)).hom ≫ E.obj U ◁ mu V W ≫ mu U (V⊗W) := by
  funext b
  apply Equiv.ext
  intro x
  change E.map (assocHom U V W) b (muEval (sum U V) W b
      (FiniteSetGroupoid.sumHom (muEval U V b) (𝟙 (E.obj W b)) x)) =
    muEval U (sum V W) b (FiniteSetGroupoid.sumHom (𝟙 (E.obj U b)) (muEval V W b)
      (FiniteSetGroupoid.assoc (E.obj U b) (E.obj V b) (E.obj W b) x))
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (FiniteSetGroupoid.sum (E.obj U b) (E.obj V b)) (E.obj W b)).surjective x
  cases x with
  | inl x =>
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      rw [FiniteSetGroupoid.sumHom_inl (muEval U V b) (𝟙 (E.obj W b)),muEval_inl,muEval_inl,E_map_enum,fiber_assoc_left,
        FiniteSetGroupoid.assoc_left,FiniteSetGroupoid.sumHom_inl,FiniteSetGroupoid.id_apply,muEval_inl]
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      rw [FiniteSetGroupoid.sumHom_inl (muEval U V b) (𝟙 (E.obj W b)),muEval_inr,muEval_inl,E_map_enum,fiber_assoc_mid,
        FiniteSetGroupoid.assoc_mid,FiniteSetGroupoid.sumHom_inr,muEval_inl,muEval_inr]
  | inr x =>
    obtain ⟨x,rfl⟩ := (enumerate W b).surjective x
    rw [FiniteSetGroupoid.sumHom_inr (muEval U V b) (𝟙 (E.obj W b)),FiniteSetGroupoid.id_apply,muEval_inr,E_map_enum,fiber_assoc_right,
      FiniteSetGroupoid.assoc_right,FiniteSetGroupoid.sumHom_inr,muEval_inr,muEval_inr]
lemma eps_left (U : Labelled a n) :
    (λ_ (E.obj U)).hom = eps ▷ E.obj U ≫ mu (𝟙_ _) U ≫ E.map (λ_ U).hom := by
  funext b
  apply Equiv.ext
  intro x
  change FiniteSetGroupoid.left (E.obj U b) x = E.map (leftHom U) b
    (muEval empty U b (FiniteSetGroupoid.sumHom (epsEval b) (𝟙 (E.obj U b)) x))
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv FiniteSetGroupoid.empty (E.obj U b)).surjective x
  cases x with
  | inl x => exact Fin.elim0 x
  | inr x =>
    obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
    rw [FiniteSetGroupoid.left_apply,FiniteSetGroupoid.sumHom_inr (epsEval b) (𝟙 (E.obj U b)),
      FiniteSetGroupoid.id_apply,muEval_inr,E_map_enum,fiber_left]
lemma eps_right (U : Labelled a n) :
    (ρ_ (E.obj U)).hom = E.obj U ◁ eps ≫ mu U (𝟙_ _) ≫ E.map (ρ_ U).hom := by
  funext b
  apply Equiv.ext
  intro x
  change FiniteSetGroupoid.right (E.obj U b) x = E.map (rightHom U) b
    (muEval U empty b (FiniteSetGroupoid.sumHom (𝟙 (E.obj U b)) (epsEval b) x))
  obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) FiniteSetGroupoid.empty).surjective x
  cases x with
  | inl x =>
    obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
    rw [FiniteSetGroupoid.right_apply,FiniteSetGroupoid.sumHom_inl (𝟙 (E.obj U b)) (epsEval b),
      FiniteSetGroupoid.id_apply,muEval_inl,E_map_enum,fiber_right]
  | inr x => exact Fin.elim0 x
noncomputable instance evaluationMonoidal : (evaluation (a:=a) (n:=n)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := asIso eps
    μIso U V := asIso (mu U V)
    μIso_hom_natural_left := by intro U V f W; simpa using mu_natural f (𝟙 W)
    μIso_hom_natural_right := by intro U V W f; simpa using mu_natural (𝟙 W) f
    associativity := mu_assoc
    left_unitality := eps_left
    right_unitality := eps_right }
noncomputable instance evaluationBraided : (evaluation (a:=a) (n:=n)).Braided where
  braided U V := by
    change mu U V ≫ E.map (swapHom U V) = (β_ (E.obj U) (E.obj V)).hom ≫ mu V U
    funext b
    apply Equiv.ext
    intro x
    change E.map (swapHom U V) b (muEval U V b x) =
      muEval V U b (FiniteSetGroupoid.swap (E.obj U b) (E.obj V b) x)
    obtain ⟨x,rfl⟩ := (FiniteSetGroupoid.sumEquiv (E.obj U b) (E.obj V b)).surjective x
    cases x with
    | inl x =>
      obtain ⟨x,rfl⟩ := (enumerate U b).surjective x
      rw [muEval_inl,E_map_enum,fiber_swap_left,FiniteSetGroupoid.swap_left,muEval_inr]
    | inr x =>
      obtain ⟨x,rfl⟩ := (enumerate V b).surjective x
      rw [muEval_inr,E_map_enum,fiber_swap_right,FiniteSetGroupoid.swap_right,muEval_inl]
end SimpleAmenable.PolygonObject.Labelled.PointFiber

end

end OAI
