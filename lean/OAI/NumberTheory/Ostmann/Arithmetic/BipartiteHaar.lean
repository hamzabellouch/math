import OAI.NumberTheory.Ostmann.Arithmetic.IncidenceComponents

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.BipartiteHaar
open IncidenceHaar

variable {L R E G : Type*} [Fintype L] [Fintype R] [Fintype E]
  [DecidableEq L] [DecidableEq R] [CommGroup G]

def signedEquiv : ((L → G) × (R → G)) ≃* (L ⊕ R → G) where
  toFun x := Sum.elim x.1 (fun r => (x.2 r)⁻¹)
  invFun x := (fun l => x (.inl l),fun r => (x (.inr r))⁻¹)
  left_inv x := by ext z <;> simp
  right_inv x := by funext z; cases z <;> simp
  map_mul' x y := by funext z; cases z <;> simp [mul_comm]

def slotProducts (left : E → L) (right : E → R) :
    (E → G) →* ((L → G) × (R → G)) where
  toFun x := (fun l => fiberProduct left l x,fun r => fiberProduct right r x)
  map_one' := by ext z <;> simp
  map_mul' x y := by ext z <;> simp

omit [Fintype L] [Fintype R] in
theorem signed_slotProducts (left : E → L) (right : E → R) (x : E → G) :
    signedEquiv (slotProducts left right x) =
      boundary (fun e => Sum.inl (left e)) (fun e => Sum.inr (right e)) x := by
  funext v
  cases v with
  | inl l =>
      change (∏ e ∈ Finset.univ.filter (fun e => left e=l),x e) =
        (∏ e, flow (Sum.inl (left e)) (Sum.inr (right e)) (x e)) (Sum.inl l)
      simp [flow, Finset.prod_apply, Pi.mulSingle_apply, Finset.prod_filter,eq_comm]
  | inr r =>
      change (∏ e ∈ Finset.univ.filter (fun e => right e=r),x e)⁻¹ =
        (∏ e, flow (Sum.inl (left e)) (Sum.inr (right e)) (x e)) (Sum.inr r)
      simp [flow, Finset.prod_apply, Pi.mulSingle_apply, Finset.prod_filter,eq_comm]

abbrev Components (left : E → L) (right : E → R) :=
  Component (fun e => Sum.inl (left e)) (fun e => Sum.inr (right e))

def leftComponent (left : E → L) (right : E → R) (l : L) : Components left right :=
  componentLabel _ _ (Sum.inl l)
def rightComponent (left : E → L) (right : E → R) (r : R) : Components left right :=
  componentLabel _ _ (Sum.inr r)

omit [DecidableEq L] [DecidableEq R] in
theorem fiberProduct_signed {C : Type*} [DecidableEq C]
    (pl : L → C) (pr : R → C) (c : C) (x : (L → G) × (R → G)) :
    fiberProduct (Sum.elim pl pr) c (signedEquiv x) =
      fiberProduct pl c x.1 / fiberProduct pr c x.2 := by
  simp only [fiberProduct,Finset.prod_filter,Fintype.prod_sum_type]
  simp only [signedEquiv,MulEquiv.coe_mk,Equiv.coe_fn_mk,Sum.elim_inl,Sum.elim_inr]
  change (∏ l, if pl l = c then x.1 l else 1) *
    (∏ r, if pr r = c then (x.2 r)⁻¹ else 1) =
      (∏ l, if pl l = c then x.1 l else 1) /
        (∏ r, if pr r = c then x.2 r else 1)
  rw [div_eq_mul_inv,← Finset.prod_inv_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro r hr
  split_ifs <;> simp

omit [Fintype E] [DecidableEq L] [DecidableEq R] in
theorem componentProduct_signed (left : E → L) (right : E → R)
    (c : Components left right) (x : (L → G) × (R → G)) :
    fiberProduct (componentLabel (fun e => Sum.inl (left e))
      (fun e => Sum.inr (right e))) c (signedEquiv x) =
      fiberProduct (leftComponent left right) c x.1 /
        fiberProduct (rightComponent left right) c x.2 := by
  have hlabel : componentLabel (fun e => Sum.inl (left e)) (fun e => Sum.inr (right e)) =
      Sum.elim (leftComponent left right) (rightComponent left right) := by
    funext v; cases v <;> rfl
  rw [hlabel]
  exact fiberProduct_signed _ _ c x

def coupled (left : E → L) (right : E → R) : Subgroup ((L → G) × (R → G)) :=
  (balanced (fun e => Sum.inl (left e)) (fun e => Sum.inr (right e))).comap
    signedEquiv.toMonoidHom

omit [Fintype E] [DecidableEq L] [DecidableEq R] in
theorem mem_coupled_iff (left : E → L) (right : E → R) (x : (L → G) × (R → G)) :
    x ∈ coupled left right ↔ ∀ c : Components left right,
      fiberProduct (leftComponent left right) c x.1 =
        fiberProduct (rightComponent left right) c x.2 := by
  change (∀ c, fiberProduct _ c (signedEquiv x) = 1) ↔ _
  simp only [componentProduct_signed,div_eq_one]

theorem slotProducts_range (left : E → L) (right : E → R) :
    (slotProducts (G:=G) left right).range = coupled left right := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change signedEquiv (slotProducts left right y) ∈ balanced _ _
    rw [signed_slotProducts,← boundary_range_eq_balanced]
    exact ⟨y,rfl⟩
  · intro hx
    have hx' : signedEquiv x ∈ (boundary
        (fun e => Sum.inl (left e)) (fun e => Sum.inr (right e))).range := by
      rw [boundary_range_eq_balanced]
      exact hx
    obtain ⟨y,hy⟩ := hx'
    refine ⟨y, signedEquiv.injective ?_⟩
    rw [signed_slotProducts]
    exact hy

end Ostmann.Arithmetic.BipartiteHaar

end

end OAI
