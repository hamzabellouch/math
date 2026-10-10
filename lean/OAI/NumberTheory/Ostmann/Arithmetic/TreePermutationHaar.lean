import OAI.NumberTheory.Ostmann.Arithmetic.PermutationHaar
import OAI.NumberTheory.Ostmann.Tree.Diagram

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.TreePermutationHaar
open IncidenceHaar

def leafIndex (depth : ℕ) : Tree.Leaves depth ≃ Fin (2^depth) :=
  Fintype.equivFinOfCardEq (by simp [Tree.Leaves])

variable {depth m : ℕ}

abbrev blocks (σ : Equiv.Perm (Fin (2^depth) × Fin m)) :=
  Fintype.card (Conclusion.OverlapComponent σ)

def componentIndex (σ : Equiv.Perm (Fin (2^depth) × Fin m)) :
    Conclusion.OverlapComponent σ ≃ Fin (blocks σ) := Fintype.equivFin _

def leftPartition (σ : Equiv.Perm (Fin (2^depth) × Fin m)) :
    Tree.LeafPartition depth (blocks σ) where
  label path := componentIndex σ (Conclusion.leftComponent σ (leafIndex depth path))
  onto := (componentIndex σ).surjective.comp
    ((Conclusion.leftComponent_surjective σ).comp (leafIndex depth).surjective)

theorem rightComponent_surjective (σ : Equiv.Perm (Fin (2^depth) × Fin m)) (hm : 0 < m) :
    Function.Surjective (Conclusion.rightComponent σ hm) := by
  intro c
  have hpos : 0 < Fintype.card {b // Conclusion.rightComponent σ hm b = c} := by
    rw [← Conclusion.component_card_balance σ hm c]
    exact Conclusion.component_card_pos σ c
  obtain ⟨b⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨b.val,b.property⟩

def rightPartition (σ : Equiv.Perm (Fin (2^depth) × Fin m)) (hm : 0 < m) :
    Tree.LeafPartition depth (blocks σ) where
  label path := componentIndex σ (Conclusion.rightComponent σ hm (leafIndex depth path))
  onto := (componentIndex σ).surjective.comp
    ((rightComponent_surjective σ hm).comp (leafIndex depth).surjective)

variable {F : Type*} [Field F]

def leafPairEquiv : ((Fin (2^depth) → Fˣ) × (Fin (2^depth) → Fˣ)) ≃
    ((Tree.Leaves depth → Fˣ) × (Tree.Leaves depth → Fˣ)) where
  toFun x := (x.1 ∘ leafIndex depth,x.2 ∘ leafIndex depth)
  invFun x := (x.1 ∘ (leafIndex depth).symm,x.2 ∘ (leafIndex depth).symm)
  left_inv x := by ext i <;> simp
  right_inv x := by ext i <;> simp

private theorem fiberProduct_equiv {A B C G : Type*} [Fintype A] [Fintype B]
    [DecidableEq C] [CommMonoid G] (e : A ≃ B) (label : B → C) (c : C) (f : B → G) :
    (∏ a ∈ Finset.univ.filter (fun a => label (e a) = c), f (e a)) =
      ∏ b ∈ Finset.univ.filter (fun b => label b = c), f b := by
  simp only [Finset.prod_filter]
  exact e.prod_comp (fun b => if label b=c then f b else 1)

theorem left_componentProduct (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (x : (Fin (2^depth) → Fˣ) × (Fin (2^depth) → Fˣ)) (b : Fin (blocks σ)) :
    (leftPartition σ).componentProduct (leafPairEquiv x).1 b =
      fiberProduct (Conclusion.leftComponent σ) ((componentIndex σ).symm b) x.1 := by
  change (∏ path ∈ Finset.univ.filter (fun path =>
      componentIndex σ (Conclusion.leftComponent σ (leafIndex depth path)) = b),
        x.1 (leafIndex depth path)) = _
  simp only [← Equiv.eq_symm_apply]
  exact fiberProduct_equiv (leafIndex depth) (Conclusion.leftComponent σ) _ x.1

theorem right_componentProduct (σ : Equiv.Perm (Fin (2^depth) × Fin m)) (hm : 0 < m)
    (x : (Fin (2^depth) → Fˣ) × (Fin (2^depth) → Fˣ)) (b : Fin (blocks σ)) :
    (rightPartition σ hm).componentProduct (leafPairEquiv x).2 b =
      fiberProduct (Conclusion.rightComponent σ hm) ((componentIndex σ).symm b) x.2 := by
  change (∏ path ∈ Finset.univ.filter (fun path =>
      componentIndex σ (Conclusion.rightComponent σ hm (leafIndex depth path)) = b),
        x.2 (leafIndex depth path)) = _
  simp only [← Equiv.eq_symm_apply]
  exact fiberProduct_equiv (leafIndex depth) (Conclusion.rightComponent σ hm) _ x.2

theorem coupled_iff (σ : Equiv.Perm (Fin (2^depth) × Fin m)) (hm : 0 < m)
    (x : (Fin (2^depth) → Fˣ) × (Fin (2^depth) → Fˣ)) :
    x ∈ PermutationHaar.coupled σ hm ↔
      (leftPartition σ).coupled (rightPartition σ hm) (leafPairEquiv x) := by
  change (∀ c, fiberProduct (Conclusion.leftComponent σ) c x.1 =
      fiberProduct (Conclusion.rightComponent σ hm) c x.2) ↔
    ∀ b, (leftPartition σ).componentProduct (leafPairEquiv x).1 b =
      (rightPartition σ hm).componentProduct (leafPairEquiv x).2 b
  simp only [left_componentProduct,right_componentProduct]
  exact (componentIndex σ).symm.surjective.forall

def coupledEquiv (σ : Equiv.Perm (Fin (2^depth) × Fin m)) (hm : 0 < m) :
    PermutationHaar.coupled (G:=Fˣ) σ hm ≃
      {x : (Tree.Leaves depth → Fˣ) × (Tree.Leaves depth → Fˣ) //
        (leftPartition σ).coupled (rightPartition σ hm) x} :=
  leafPairEquiv.subtypeEquiv (fun x => coupled_iff σ hm x)

instance coupledTreeFintype [Fintype F] (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (hm : 0 < m) : Fintype {x : (Tree.Leaves depth → Fˣ) × (Tree.Leaves depth → Fˣ) //
      (leftPartition σ).coupled (rightPartition σ hm) x} := Fintype.ofFinite _

theorem tree_products_uniform [Fintype F] [DecidableEq F] (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (hm : 0 < m) (test : {x : (Tree.Leaves depth → Fˣ) × (Tree.Leaves depth → Fˣ) //
      (leftPartition σ).coupled (rightPartition σ hm) x} → ℂ) :
    ResidueHaar.average (fun samples => test (coupledEquiv σ hm
      (PermutationHaar.toCoupled σ hm samples))) = ResidueHaar.average test := by
  exact (PermutationHaar.products_uniform σ hm (fun x => test (coupledEquiv σ hm x))).trans
    (ResidueHaar.average_equiv (coupledEquiv σ hm) test)

end Ostmann.Arithmetic.TreePermutationHaar

end

end OAI
