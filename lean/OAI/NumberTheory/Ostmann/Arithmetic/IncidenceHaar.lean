import OAI.NumberTheory.Ostmann.Arithmetic.GroupHaarImage

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.IncidenceHaar

variable {V E G : Type*} [DecidableEq V] [CommGroup G]

def flow (v w : V) (a : G) : V → G := Pi.mulSingle v a / Pi.mulSingle w a

@[simp] theorem flow_one (v w : V) : flow v w (1:G) = 1 := by simp [flow]
@[simp] theorem flow_self (v : V) (a : G) : flow v v a = 1 := by simp [flow]
theorem flow_mul (v w : V) (a b : G) : flow v w (a*b) = flow v w a * flow v w b := by
  ext u
  simp only [flow, Pi.div_apply, Pi.mul_apply, Pi.mulSingle_mul]
  exact mul_div_mul_comm _ _ _ _
theorem flow_trans (v w z : V) (a : G) : flow v w a * flow w z a = flow v z a := by
  simp [flow]
theorem flow_symm (v w : V) (a : G) : flow w v a = (flow v w a)⁻¹ := by
  simp [flow]

variable [Fintype E]

def boundary (source target : E → V) : (E → G) →* (V → G) where
  toFun x := ∏ e, flow (source e) (target e) (x e)
  map_one' := by simp
  map_mul' x y := by simp only [Pi.mul_apply,flow_mul,Finset.prod_mul_distrib]

def edgeRelation (source target : E → V) (v w : V) : Prop :=
  ∃ e, source e = v ∧ target e = w

@[simp] theorem boundary_single [DecidableEq E] (source target : E → V) (e : E) (a : G) :
    boundary source target (Pi.mulSingle e a) = flow (source e) (target e) a := by
  change (∏ j, flow (source j) (target j) (Pi.mulSingle e a j)) = _
  rw [Finset.prod_eq_single e]
  · simp
  · intro j hj hje
    simp [Pi.mulSingle_eq_of_ne hje]
  · simp

theorem flow_mem_range (source target : E → V) {v w : V}
    (h : Relation.EqvGen (edgeRelation source target) v w) (a : G) :
    flow v w a ∈ (boundary source target).range := by
  classical
  induction h with
  | rel v w h =>
      obtain ⟨e,rfl,rfl⟩ := h
      exact ⟨Pi.mulSingle e a, boundary_single source target e a⟩
  | refl v => simp
  | symm v w h ih =>
      rw [flow_symm v w a]
      exact (boundary (G:=G) source target).range.inv_mem ih
  | trans v w z h₁ h₂ ih₁ ih₂ =>
      rw [← flow_trans v w z a]
      exact (boundary (G:=G) source target).range.mul_mem ih₁ ih₂

variable [Fintype V]

def fiberProduct {C : Type*} [DecidableEq C] (label : V → C) (c : C) : (V → G) →* G where
  toFun x := ∏ v ∈ Finset.univ.filter (fun v => label v = c), x v
  map_one' := by simp
  map_mul' x y := by simp [Finset.prod_mul_distrib]

@[simp] theorem fiberProduct_single {C : Type*} [DecidableEq C]
    (label : V → C) (c : C) (v : V) (a : G) :
    fiberProduct label c (Pi.mulSingle v a) = if label v = c then a else 1 := by
  simp [fiberProduct, Pi.mulSingle_apply]

theorem fiberProduct_boundary {C : Type*} [DecidableEq C]
    (source target : E → V) (label : V → C)
    (hlabel : ∀ e, label (source e) = label (target e)) (c : C) (x : E → G) :
    fiberProduct label c (boundary source target x) = 1 := by
  change fiberProduct label c (∏ e, flow (source e) (target e) (x e)) = 1
  rw [map_prod]
  apply Finset.prod_eq_one
  intro e he
  simp [flow,map_div,fiberProduct_single,hlabel e]

theorem mem_range_of_component_products {C : Type*} [Fintype C] [DecidableEq C]
    (source target : E → V) (label : V → C) (root : C → V)
    (_hroot : ∀ c, label (root c) = c)
    (hpath : ∀ v, Relation.EqvGen (edgeRelation source target) v (root (label v)))
    (x : V → G) (hx : ∀ c, fiberProduct label c x = 1) :
    x ∈ (boundary source target).range := by
  classical
  have hflow : (∏ v, flow v (root (label v)) (x v)) ∈ (boundary source target).range :=
    Subgroup.prod_mem _ fun v hv => flow_mem_range source target (hpath v) (x v)
  have hden : (∏ v, Pi.mulSingle (M := fun _ : V => G) (root (label v)) (x v)) = (1 : V → G) := by
    rw [← Finset.prod_fiberwise Finset.univ label]
    apply Finset.prod_eq_one
    intro c hc
    calc
      (∏ v ∈ Finset.univ.filter (fun v => label v = c), Pi.mulSingle (M := fun _ : V => G) (root (label v)) (x v)) =
          ∏ v ∈ Finset.univ.filter (fun v => label v = c), Pi.mulSingle (M := fun _ : V => G) (root c) (x v) :=
        Finset.prod_congr rfl fun v hv => by rw [(Finset.mem_filter.mp hv).2]
      _ = Pi.mulSingle (M := fun _ : V => G) (root c) (fiberProduct (G:=G) label c x) := by
        ext w
        simp only [Finset.prod_apply,fiberProduct]
        by_cases hw : w = root c
        · subst w; simp
        · simp [Pi.mulSingle_eq_of_ne hw]
      _ = 1 := by rw [hx]; simp
  simpa only [flow,Finset.prod_div_distrib,Finset.univ_prod_mulSingle,hden,div_one] using hflow

end Ostmann.Arithmetic.IncidenceHaar

end

end OAI
