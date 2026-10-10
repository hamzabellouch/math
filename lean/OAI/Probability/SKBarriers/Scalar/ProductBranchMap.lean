import Mathlib
import OAI.Probability.SKBarriers.Replicas.ProductMerge

namespace OAI

section

noncomputable section
open scoped BigOperators
namespace SK.Analytic
section Map
variable {E F E' F' : Type}

def mapProductIncrement (f : E → E') (g : F → F') :
    ProductIncrement (E:=E) (F:=F) → ProductIncrement (E:=E') (F:=F') :=
  Sum.map (fun p => (p.1,f p.2)) (fun p => (p.1,g p.2))

@[simp] theorem productMass_map (f : E → E') (g : F → F') (p : ProductIncrement (E:=E) (F:=F)) :
    productMass (mapProductIncrement f g p)=productMass p := by cases p <;> rfl

theorem productLeft_map (f : E → E') (g : F → F') (l : List (ProductIncrement (E:=E) (F:=F))) :
    productLeft (l.map (mapProductIncrement f g))=(productLeft l).map (fun p => (p.1,f p.2)) := by
  induction l with
  | nil => rfl
  | cons p l ih => cases p <;> simp only [List.map_cons,mapProductIncrement,Sum.map_inl,Sum.map_inr,
      productLeft,List.filterMap_cons] at ih ⊢ <;> rw [ih]

theorem productRight_map (f : E → E') (g : F → F') (l : List (ProductIncrement (E:=E) (F:=F))) :
    productRight (l.map (mapProductIncrement f g))=(productRight l).map (fun p => (p.1,g p.2)) := by
  induction l with
  | nil => rfl
  | cons p l ih => cases p <;> simp only [List.map_cons,mapProductIncrement,Sum.map_inl,Sum.map_inr,
      productRight,List.filterMap_cons] at ih ⊢ <;> rw [ih]

theorem mergedProductBranches_map (f : E → E') (g : F → F') (l : List (ℝ × E)) (r : List (ℝ × F)) :
    (mergedProductBranches l r).map (mapProductIncrement f g)=
      mergedProductBranches (l.map (fun p => (p.1,f p.2))) (r.map (fun p => (p.1,g p.2))) := by
  unfold mergedProductBranches
  rw [List.map_merge (s:=fun p q => decide (productMass p≤productMass q))
    (by intro a ha b hb; simp only [productMass_map])]
  simp only [List.map_map,Function.comp_def,mapProductIncrement,Sum.map_inl,Sum.map_inr]
end Map

end SK.Analytic

end
end

end OAI
