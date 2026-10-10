import OAI.MathematicalPhysics.Heisenberg.PhysicalClock

namespace OAI

section
attribute [instance] instDecidableEqFin instDecidableEqProd
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg
open SlotTensor

lemma directed_sum {X E : Type*} [Fintype X] [AddCommMonoid E]
    (R r : X → X → Prop) (hR : ∀ x y,R x y → R y x) (hne : ∀ x y,R x y → x≠y)
    (hr : ∀ x y,x≠y → r x y ∨ r y x) (ha : ∀ x y,r x y → ¬r y x)
    (f : X → X → E) (hf : ∀ x y,R x y → f x y=f y x) :
    (∑ e : X×X,if R e.1 e.2 then f e.1 e.2 else 0)=
      2 • (∑ e : X×X,if R e.1 e.2 ∧ r e.1 e.2 then f e.1 e.2 else 0) := by
  let g : X×X → E:=fun e=>if R e.1 e.2 ∧ r e.1 e.2 then f e.1 e.2 else 0
  have h (e : X×X) : (if R e.1 e.2 then f e.1 e.2 else 0)=g e+g e.swap := by
    dsimp only [g]
    by_cases hh : R e.1 e.2
    · rw [ite_eq_left hh]
      by_cases he : r e.1 e.2
      · rw [ite_eq_left ⟨hh,he⟩,ite_eq_right (fun h=>ha _ _ he h.2),add_zero]
      · have he' : r e.2 e.1:=(hr _ _ (hne _ _ hh)).resolve_left he
        rw [ite_eq_right (fun h=>he h.2),ite_eq_left ⟨hR _ _ hh,he'⟩,zero_add,hf _ _ hh]
        rfl
    · have hh' : ¬R e.2 e.1:=fun h=>hh (hR _ _ h)
      rw [ite_eq_right hh,ite_eq_right (fun h=>hh h.1),ite_eq_right (fun h=>hh' h.1),add_zero]
  simp_rw [h]
  rw [Finset.sum_add_distrib]
  change (∑ e,g e)+(∑ e,g ((Equiv.prodComm X X) e))=2 • ∑ e,g e
  rw [(Equiv.prodComm X X).sum_comp,two_smul]

lemma bond_symm {d ℓ : ℕ} {x y : Site d} (hxy : x≠y) : bond d ℓ x y=bond d ℓ y x := by
  have hX:=singleton_local_commute hxy (spinX_mem_localAlgebra d ℓ {x} (Set.mem_singleton x))
    (spinX_mem_localAlgebra d ℓ {y} (Set.mem_singleton y))
  have hY:=singleton_local_commute hxy (spinY_mem_localAlgebra d ℓ {x} (Set.mem_singleton x))
    (spinY_mem_localAlgebra d ℓ {y} (Set.mem_singleton y))
  have hZ:=singleton_local_commute hxy (spinZ_mem_localAlgebra d ℓ {x} (Set.mem_singleton x))
    (spinZ_mem_localAlgebra d ℓ {y} (Set.mem_singleton y))
  simp only [bond,hX.eq,hY.eq,hZ.eq]

lemma sum_siteEdges {X : Type} {E : Type*} [Fintype X] [AddCommMonoid E]
    (R : X → X → Prop) (f : X → X → E) :
    (∑ e : SiteEdges R,f e.val.1 e.val.2)=∑ e : X×X,if R e.1 e.2 then f e.1 e.2 else 0 := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun e : X×X=>R e.1 e.2)) (by simp) (fun e=>f e.1 e.2)]
  simp only [Finset.sum_filter]

lemma sum_volumeEdges {d ℓ : ℕ} (Λ : Finset (Site d)) :
    (∑ e : Λ×Λ,if NearestNeighbor e.1.val e.2.val ∧ WellOrderingRel e.1.val e.2.val
      then bond d ℓ e.1.val e.2.val else 0)= -hamiltonian d ℓ Λ := by
  rw [hamiltonian,neg_neg,volumeEdges,Finset.sum_filter,Finset.sum_product,Fintype.sum_prod_type]
  rw [←Finset.sum_coe_sort Λ]
  apply Finset.sum_congr rfl
  intro x _
  exact Finset.sum_coe_sort Λ (fun y=>if NearestNeighbor x.val y ∧ WellOrderingRel x.val y then bond d ℓ x.val y else 0)

lemma directed_bond_sum {d ℓ : ℕ} (Λ : Finset (Site d)) :
    (∑ e : SiteEdges (fun x y : Λ=>NearestNeighbor x.val y.val),bond d ℓ e.val.1.val e.val.2.val)=
      2 • (-hamiltonian d ℓ Λ) := by
  rw [sum_siteEdges (fun x y : Λ=>NearestNeighbor x.val y.val) (fun x y : Λ=>bond d ℓ x.val y.val)]
  have hh:=directed_sum (fun x y : Λ=>NearestNeighbor x.val y.val) (fun x y : Λ=>WellOrderingRel x.val y.val)
    (fun _ _ h=>nearestNeighbor_symm h)
    (fun x y h he=>nearestNeighbor_ne h (congrArg Subtype.val he))
    (fun x y h=>by
      rcases trichotomous_of WellOrderingRel x.val y.val with hxy | hxy | hxy
      · exact Or.inl hxy
      · exact False.elim (h (Subtype.ext hxy))
      · exact Or.inr hxy)
    (fun x y h=>asymm h)
    (fun x y : Λ=>bond d ℓ x.val y.val) (fun x y h=>bond_symm (nearestNeighbor_ne h))
  rw [sum_volumeEdges] at hh
  exact hh

lemma finiteRepresentation_generator {d ℓ : ℕ} (Λ : Finset (Site d)) :
    finiteRepresentation (ℓ:=ℓ) (fun x : Λ=>x.val) Subtype.val_injective
      (spinGenerator (fun x y : Λ=>NearestNeighbor x.val y.val) ℓ)=
      (-2:ℝ) • hamiltonian d ℓ Λ-
        ((Fintype.card (SiteEdges (fun x y : Λ=>NearestNeighbor x.val y.val)):ℝ)*(ℓ:ℝ)^2/4) • 1 := by
  simp only [spinGenerator,map_sum,map_sub,finiteRepresentation_bond,
    Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,directed_bond_sum]
  rw [←Nat.cast_smul_eq_nsmul ℝ,←Nat.cast_smul_eq_nsmul ℝ,smul_smul]
  rw [map_smul, map_one]
  norm_num
  module

end Heisenberg
end
end

end OAI
