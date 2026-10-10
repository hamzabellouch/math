import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ProductNatural
import OAI.GroupTheory.SimpleAmenable.Simplicial.StageCoordinateMaps

namespace OAI

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory Limits MonoidalCategory HomologicalComplex Simplicial Opposite
namespace BarFinitePower
open FreeChains ProductChains

lemma finite_tensor (X Y:SSet) (n:ℕ)
    (hX:∀i,i≤n → Module.Finite ℤ (X.homology Z i : A))
    (hY:∀i,i≤n → Module.Finite ℤ (Y.homology Z i : A)) :
    Module.Finite ℤ ((X⊗Y).homology Z n : A) := by
  have hXF : ∀i,i≤n → Module.Finite ℤ ((complex X).homology i) := by
    intro i hi
    have := hX i hi
    exact homology_finite_complex X i
  have hYF : ∀i,i≤n → Module.Finite ℤ ((complex Y).homology i) := by
    intro i hi
    have := hY i hi
    exact homology_finite_complex Y i
  have : Module.Finite ℤ ((complex X⊗complex Y).homology n) :=
    TensorProductHomology.finite _ _ n hXF hYF
  exact Module.Finite.equiv (homologyIsoN X Y n).symm.toLinearEquiv
lemma finite_of_iso {X Y:SSet} (e:X≅Y) (n:ℕ)
    [Module.Finite ℤ (Y.homology Z n : A)] : Module.Finite ℤ (X.homology Z n : A) := by
  let e' : (X.homology Z n : A) ≅ Y.homology Z n := (SSet.homologyFunctor Z n).mapIso e
  exact Module.Finite.equiv e'.symm.toLinearEquiv
lemma finite_fin (X:SSet) (s n:ℕ)
    (hX:∀i,i≤n → Module.Finite ℤ (X.homology Z i : A)) :
    Module.Finite ℤ (((power (Fin s)).obj X).homology Z n : A) := by
  induction s generalizing n with
  | zero =>
    have : Module.Finite ℤ (ConnectedProduct.one.homology Z n : A) := by
      by_cases hn:n=0
      · subst n; exact homology_zero_finite _
      · have := ModuleCat.isZero_iff_subsingleton.mp (ConnectedProduct.one_homology_zero n hn)
        infer_instance
    exact finite_of_iso (finZeroIso X) n
  | succ s ih =>
    have := finite_tensor X ((power (Fin s)).obj X) n hX (by
      intro i hi
      exact ih i (by intro j hj; exact hX j (hj.trans hi)))
    exact finite_of_iso (finSuccIso X s) n
lemma finite_power (X:SSet) (κ:Type) [Finite κ] (n:ℕ)
    (hX:∀i,i≤n → Module.Finite ℤ (X.homology Z i : A)) :
    Module.Finite ℤ (((power κ).obj X).homology Z n : A) := by
  let := Fintype.ofFinite κ
  have := finite_fin X (Fintype.card κ) n hX
  exact finite_of_iso (reindexIso X (Fintype.equivFin κ)) n
end BarFinitePower

end

section
open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace BarFinitePower
open IntervalBar IntervalBar.Diagram StageProductColimit SimplicialDiagonal

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C] (κ:Type)
noncomputable def singleProject (n:ℕ) :
    Diagram (κ→C) (Fin (n+1)) ⥤ (κ→Diagram C (Fin (n+1))) :=
  Functor.pi' (fun k => map (I:=Fin (n+1)) (project κ k))
lemma singleProject_eval (n:ℕ) :
    singleProject (C:=C) κ n ⋙ powerMap κ (eval n) = eval n ⋙ swap (Fin n) κ := rfl
noncomputable instance (n:ℕ) : (singleProject (C:=C) κ n).IsEquivalence := by
  have : (singleProject (C:=C) κ n ⋙ powerMap κ (eval n)).IsEquivalence := by
    rw [singleProject_eval]
    infer_instance
  exact Functor.isEquivalence_of_comp_right _ (powerMap κ (eval n))
noncomputable def doubleProject (m n:ℕ) :
    Diagram (Diagram (κ→C) (Fin (n+1))) (Fin (m+1)) ⥤
    (κ→Diagram (Diagram C (Fin (n+1))) (Fin (m+1))) :=
  Functor.pi' (fun k => map (I:=Fin (m+1)) (map (I:=Fin (n+1)) (project κ k)))
lemma doubleProject_eval (m n:ℕ) :
    doubleProject (C:=C) κ m n ⋙ powerMap κ (eval₂ m n) = eval₂ m n ⋙ swap (Fin m × Fin n) κ := rfl
noncomputable instance (m n:ℕ) : (doubleProject (C:=C) κ m n).IsEquivalence := by
  have : (doubleProject (C:=C) κ m n ⋙ powerMap κ (eval₂ m n)).IsEquivalence := by
    rw [doubleProject_eval]
    infer_instance
  exact Functor.isEquivalence_of_comp_right _ (powerMap κ (eval₂ m n))
noncomputable def singlePowerComparison : bar (C:=κ→C) ⟶ (power κ).obj (bar (C:=C)) :=
  lift κ (fun k => barMap (project κ k))
noncomputable def doublePowerComparison : bar₂ (C:=κ→C) ⟶ (power κ).obj (bar₂ (C:=C)) :=
  lift κ (fun k => bar₂Map (project κ k))
lemma singleDegree_homology_isIso (p q:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k=>nerveMap (map (I:=Fin (p+1)) (project (C:=C) κ k)))) DiagonalResolution.Z q) := by
  have : (Functor.pi' (fun k=>map (I:=Fin (p+1)) (project (C:=C) κ k))).IsEquivalence :=
    inferInstanceAs (singleProject (C:=C) κ p).IsEquivalence
  exact lift_nerve_homology_isIso κ (fun k=>map (I:=Fin (p+1)) (project (C:=C) κ k)) q
lemma singleRow_homology_isIso (p:SimplexCategoryᵒᵖ) (q:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k =>
      (Functor.whiskerRight (simplicialMap (project (C:=C) κ k)) nerveFunctor).app p)) DiagonalResolution.Z q) := by
  exact singleDegree_homology_isIso κ p.unop.len q
lemma single_power_diagonal_eq : singlePowerComparison (C:=C) κ =
    lift κ (fun k => diagonal.map (Functor.whiskerRight (simplicialMap (project (C:=C) κ k)) nerveFunctor)) := rfl
lemma singlePowerComparison_homology_isIso (n:ℕ) :
    IsIso (SSet.homologyMap (singlePowerComparison (C:=C) κ) DiagonalResolution.Z n) := by
  rw [single_power_diagonal_eq]
  apply homologyLiftDiagonal_isIso
  intro p q
  exact singleRow_homology_isIso (C:=C) κ p q
lemma doubleDegree_homology_isIso (l p r:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k=>nerveMap (map (I:=Fin (l+1))
      (map (I:=Fin (p+1)) (project (C:=C) κ k))))) DiagonalResolution.Z r) := by
  have : (Functor.pi' (fun k=>map (I:=Fin (l+1))
      (map (I:=Fin (p+1)) (project (C:=C) κ k)))).IsEquivalence :=
    inferInstanceAs (doubleProject (C:=C) κ l p).IsEquivalence
  exact lift_nerve_homology_isIso κ (fun k=>map (I:=Fin (l+1))
    (map (I:=Fin (p+1)) (project (C:=C) κ k))) r
lemma doubleFirst_homology_isIso (p q:ℕ) :
    IsIso (SSet.homologyMap (lift κ (fun k=>barMap (map (I:=Fin (p+1)) (project (C:=C) κ k)))) DiagonalResolution.Z q) := by
  apply homologyLiftDiagonal_isIso κ (fun k => Functor.whiskerRight
    (simplicialMap (map (I:=Fin (p+1)) (project (C:=C) κ k))) nerveFunctor)
  intro l r
  exact doubleDegree_homology_isIso κ l.unop.len p r
lemma doublePowerComparison_homology_isIso (n:ℕ) :
    IsIso (SSet.homologyMap (doublePowerComparison (C:=C) κ) DiagonalResolution.Z n) := by
  apply homologyLiftDiagonal_isIso κ (fun k => rows₂Map (project (C:=C) κ k))
  intro p q
  exact doubleFirst_homology_isIso κ p.unop.len q
end BarFinitePower

end

open _root_.CategoryTheory _root_.OAI.CategoryTheory MonoidalCategory Simplicial Opposite
namespace IntervalBar.Diagram

variable {C:Type} [Groupoid.{0} C] [MonoidalCategory C] [SymmetricCategory C]
def outerOrder (i:Fin 2) : Fin 2 →o Fin 3 :=
  if i=0 then (SimplexCategory.δ (0:Fin 3)).toOrderHom else (SimplexCategory.δ (2:Fin 3)).toOrderHom
noncomputable def outerFunctor : Diagram C (Fin 3) ⥤ (Fin 2 → Diagram C (Fin 2)) :=
  Functor.pi' (fun i => reindex (outerOrder i))
noncomputable instance : (outerFunctor (C:=C)).Braided :=
  inferInstanceAs ((Functor.pi' (fun i : Fin 2 => reindex (C:=C) (outerOrder i))).Braided)
noncomputable instance : (outerFunctor (C:=C)).Faithful where
  map_injective {X Y} f g h := by
    apply (eval (C:=C) 2).map_injective
    funext i
    fin_cases i
    · exact congrArg (fun h => ((eval (C:=C) 1).map (h (1:Fin 2))) 0) h
    · exact congrArg (fun h => ((eval (C:=C) 1).map (h (0:Fin 2))) 0) h
noncomputable instance : (outerFunctor (C:=C)).Full where
  map_surjective {X Y} f := by
    let g : (eval 2).obj X ⟶ (eval 2).obj Y := fun i =>
      if h:i=0 then by subst i; exact ((eval 1).map (f 1)) 0
      else by
        have hi:i=1 := by omega
        subst i
        exact ((eval 1).map (f 0)) 0
    refine ⟨(eval 2).preimage g,?_⟩
    funext i
    apply (eval (C:=C) 1).map_injective
    funext j
    have hj:j=0 := Subsingleton.elim _ _
    subst j
    fin_cases i
    · change ((eval 2).map ((eval 2).preimage g)) 1 = ((eval 1).map (f 0)) 0
      rw [Functor.map_preimage]
      simp only [g,dite_eq_right (show (1:Fin 2)≠0 by decide)]
      rfl
    · have h := congrArg (fun h=>h (0:Fin 2)) ((eval 2).map_preimage g)
      exact h
noncomputable instance : (outerFunctor (C:=C)).EssSurj where
  mem_essImage Y := by
    let U : Fin 2 → C := fun i => if i=0 then ((eval 1).obj (Y 1)) 0 else ((eval 1).obj (Y 0)) 0
    let X := (eval (C:=C) 2).objPreimage U
    let e := (eval (C:=C) 2).objObjPreimageIso U
    refine ⟨X,⟨?_⟩⟩
    refine { hom := fun i=> ?_,inv := fun i=>?_,hom_inv_id := ?_,inv_hom_id := ?_ }
    · apply (eval 1).preimage
      intro j
      have hj:j=0 := Subsingleton.elim _ _
      subst j
      cases i using Fin.cases with
      | zero => exact e.hom 1
      | succ i =>
        have hi:i=0 := Subsingleton.elim _ _
        subst i
        exact e.hom 0
    · apply (eval 1).preimage
      intro j
      have hj:j=0 := Subsingleton.elim _ _
      subst j
      cases i using Fin.cases with
      | zero => exact e.inv 1
      | succ i =>
        have hi:i=0 := Subsingleton.elim _ _
        subst i
        exact e.inv 0
    · funext i
      apply (eval (C:=C) 1).map_injective
      change (eval 1).map (_ ≫ _) = (eval 1).map (𝟙 _)
      simp only [Functor.map_comp,Functor.map_preimage]
      funext j
      have hj:j=0 := Subsingleton.elim _ _
      subst j
      fin_cases i
      · change e.hom 1 ≫ e.inv 1 = 𝟙 _
        exact congrArg (fun f=>f (1:Fin 2)) e.hom_inv_id
      · change e.hom 0 ≫ e.inv 0 = 𝟙 _
        exact congrArg (fun f=>f (0:Fin 2)) e.hom_inv_id
    · funext i
      apply (eval (C:=C) 1).map_injective
      change (eval 1).map (_ ≫ _) = (eval 1).map (𝟙 _)
      simp only [Functor.map_comp,Functor.map_preimage]
      funext j
      have hj:j=0 := Subsingleton.elim _ _
      subst j
      fin_cases i
      · change e.inv 1 ≫ e.hom 1 = 𝟙 _
        exact congrArg (fun f=>f (1:Fin 2)) e.inv_hom_id
      · change e.inv 0 ≫ e.hom 0 = 𝟙 _
        exact congrArg (fun f=>f (0:Fin 2)) e.inv_hom_id
noncomputable instance : (outerFunctor (C:=C)).IsEquivalence where
end IntervalBar.Diagram

end OAI
