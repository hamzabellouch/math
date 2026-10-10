import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Group.Subgroup.Finite
import OAI.NumberTheory.Ostmann.Construction.ArrangementBoundary

namespace OAI

/-! # Every compatible pair of leaf-product vectors is realized by bulk slots -/

namespace Ostmann
open scoped Classical BigOperators

theorem arrangementBoundary_range_of_balanced {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) (f : L ⊕ L → G)
    (hf : ∀ c : (arrangementGraph m e).ConnectedComponent,
      (∏ v : {v : L ⊕ L // (arrangementGraph m e).connectedComponentMk v = c}, f v.val) = 1) :
    f ∈ (arrangementBoundary e).range := by
  let component := (arrangementGraph m e).connectedComponentMk
  choose root hroot using arrangementLeft_surjective hm e
  let vertex : (arrangementGraph m e).ConnectedComponent → L ⊕ L := fun c => Sum.inl (root c)
  have hv (c) : component (vertex c) = c := hroot c
  have hmem (v : L ⊕ L) : Pi.mulSingle (M := fun _ : L ⊕ L => G) v (f v) / Pi.mulSingle (M := fun _ : L ⊕ L => G) (vertex (component v)) (f v) ∈
      (arrangementBoundary e).range := by
    apply arrangementBoundary_transfer_reachable
    exact SimpleGraph.ConnectedComponent.exact (hv (component v)).symm
  have hden : (∏ v : L ⊕ L, Pi.mulSingle (M := fun _ : L ⊕ L => G) (vertex (component v)) (f v)) = 1 := by
    rw [← Fintype.prod_fiberwise component (fun v => Pi.mulSingle (M := fun _ : L ⊕ L => G) (vertex (component v)) (f v))]
    apply Finset.prod_eq_one
    intro c _
    calc
      _ = (MonoidHom.mulSingle (fun _ : L ⊕ L => G) (vertex c))
          (∏ v : {v : L ⊕ L // component v = c}, f v.val) := by
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro v _
        simp only [MonoidHom.mulSingle_apply, v.property]
      _ = 1 := by rw [hf c]; exact map_one _
  have hnum : (∏ v : L ⊕ L, Pi.mulSingle v (f v)) = f := by
    ext v
    change (Pi.evalMonoidHom (fun _ : L ⊕ L => G) v) (∏ w, Pi.mulSingle w (f w)) = _
    rw [map_prod]
    exact Fintype.prod_pi_mulSingle v f
  have hall := (arrangementBoundary (G := G) e).range.prod_mem (fun v (_ : v ∈ Finset.univ) => hmem v)
  simpa only [Finset.prod_div_distrib, hnum, hden, div_one] using hall

noncomputable def arrangementComponentVertexEquiv {L : Type*} {m : ℕ}
    (e : Equiv.Perm (L × Fin m)) (c : (arrangementGraph m e).ConnectedComponent) :
    {v : L ⊕ L // (arrangementGraph m e).connectedComponentMk v = c} ≃
      ({l : L // arrangementLeft e l = c} ⊕ {l : L // arrangementRight e l = c}) where
  toFun v := match v with
    | ⟨.inl l, h⟩ => .inl ⟨l, h⟩
    | ⟨.inr l, h⟩ => .inr ⟨l, h⟩
  invFun v := match v with
    | .inl ⟨l, h⟩ => ⟨.inl l, h⟩
    | .inr ⟨l, h⟩ => ⟨.inr l, h⟩
  left_inv v := by rcases v with ⟨v, h⟩; cases v <;> rfl
  right_inv v := by cases v <;> rfl

theorem arrangement_component_signed_product {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (a b : L → G)
    (c : (arrangementGraph m e).ConnectedComponent) :
    (∏ v : {v : L ⊕ L // (arrangementGraph m e).connectedComponentMk v = c},
      Sum.elim a (fun l => (b l)⁻¹) v.val) =
      partitionProduct (arrangementLeft e) a c / partitionProduct (arrangementRight e) b c := by
  rw [← (arrangementComponentVertexEquiv e c).symm.prod_comp]
  rw [Fintype.prod_sum_type]
  simp only [arrangementComponentVertexEquiv, Equiv.coe_fn_symm_mk, Sum.elim_inl, Sum.elim_inr,
    div_eq_mul_inv, ← Finset.prod_inv_distrib, partitionProduct]

theorem arrangement_leaf_products_surjective {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (hm : 0 < m) (e : Equiv.Perm (L × Fin m)) (a b : L → G)
    (hab : partitionProduct (arrangementLeft e) a = partitionProduct (arrangementRight e) b) :
    ∃ x : L × Fin m → G, bulkBlockProduct x = a ∧ bulkBlockProduct (x ∘ e.symm) = b := by
  have hf := arrangementBoundary_range_of_balanced hm e (Sum.elim a (fun l => (b l)⁻¹))
    (fun c => by rw [arrangement_component_signed_product, congrFun hab c]; exact div_self' _)
  obtain ⟨x, hx⟩ := hf
  refine ⟨x, ?_, ?_⟩
  · funext l
    exact congrFun hx (.inl l)
  · funext l
    have h := congrFun hx (.inr l)
    exact inv_injective h

end Ostmann

end OAI
