import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Subgroup.Ker
import OAI.NumberTheory.Ostmann.Construction.ArrangementProducts

namespace OAI

/-! # Transfers along the actual overlap graph

The signed vertex products form a group homomorphism. A slot transfers an
arbitrary unit between its two endpoints; connected paths compose transfers.
-/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def arrangementBoundary {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) : (L × Fin m → G) →* (L ⊕ L → G) where
  toFun x := Sum.elim (bulkBlockProduct x) (fun l => (bulkBlockProduct (x ∘ e.symm) l)⁻¹)
  map_one' := by ext v; cases v <;> simp [bulkBlockProduct]
  map_mul' x y := by
    ext v
    cases v <;> simp [bulkBlockProduct, Pi.mul_apply, Function.comp_apply, Finset.prod_mul_distrib, mul_comm]

theorem bulkBlockProduct_mulSingle {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (s : L × Fin m) (g : G) (l : L) :
    bulkBlockProduct (Pi.mulSingle s g) l = if l = s.1 then g else 1 := by
  rcases s with ⟨a, i⟩
  by_cases h : l = a
  · subst l
    simp [bulkBlockProduct, Pi.mulSingle_apply, Prod.mk.injEq]
  · simp [bulkBlockProduct, Prod.mk.injEq, h]

theorem arrangementBoundary_mulSingle {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (s : L × Fin m) (g : G) :
    arrangementBoundary e (Pi.mulSingle s g) =
      Pi.mulSingle (Sum.inl s.1) g / Pi.mulSingle (Sum.inr (e s).1) g := by
  have he : (Pi.mulSingle s g) ∘ e.symm = Pi.mulSingle (e s) g := by
    funext t
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.symm_apply_eq]
  ext v
  cases v with
  | inl l =>
    simp [arrangementBoundary, bulkBlockProduct_mulSingle, Pi.mulSingle_apply]
  | inr l =>
    simp [arrangementBoundary, he, bulkBlockProduct_mulSingle, Pi.mulSingle_apply]

theorem arrangementBoundary_transfer_adj {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (u v : L ⊕ L)
    (h : (arrangementGraph m e).Adj u v) (g : G) :
    Pi.mulSingle u g / Pi.mulSingle v g ∈ (arrangementBoundary (G := G) e).range := by
  cases u with
  | inl a =>
    cases v with
    | inl b => exact False.elim h
    | inr b =>
      obtain ⟨i, j, hij⟩ := h
      refine ⟨Pi.mulSingle (a, i) g, ?_⟩
      simp only [arrangementBoundary_mulSingle, hij]
  | inr b =>
    cases v with
    | inr a => exact False.elim h
    | inl a =>
      obtain ⟨i, j, hij⟩ := h
      have hf : Pi.mulSingle (Sum.inl a) g / Pi.mulSingle (Sum.inr b) g ∈
          (arrangementBoundary (G := G) e).range := by
        refine ⟨Pi.mulSingle (a, i) g, ?_⟩
        simp only [arrangementBoundary_mulSingle, hij]
      simpa only [inv_div] using (arrangementBoundary (G := G) e).range.inv_mem hf

theorem arrangementBoundary_transfer_reachable {L G : Type*} [Fintype L] [CommGroup G]
    {m : ℕ} (e : Equiv.Perm (L × Fin m)) (u v : L ⊕ L)
    (h : (arrangementGraph m e).Reachable u v) (g : G) :
    Pi.mulSingle u g / Pi.mulSingle v g ∈ (arrangementBoundary (G := G) e).range := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have ha := arrangementBoundary_transfer_adj (G := G) e a b hab g
    have hm := (arrangementBoundary (G := G) e).range.mul_mem ha ih
    simpa only [div_mul_div_cancel] using hm

end Ostmann

end OAI
