import Mathlib
import OAI.GroupTheory.SimpleOvergroups.PolynomialNames

namespace OAI


namespace SimpleFInftyOvergroups.EffectiveNames.Polynomial
open BoundedEncoding
noncomputable section
open scoped Classical
variable {A k : Type*} [CommSemiring k]

omit [CommSemiring k] in
@[simp] theorem cost_nil (grade : List A → ℕ) : cost grade ([] : Name k A) = 0 := rfl

omit [CommSemiring k] in
 theorem cost_append (grade : List A → ℕ) (p q : Name k A) :
    cost grade (p++q) = max (cost grade p) (cost grade q) := by
  apply Nat.le_antisymm
  · rw [cost_le_iff]
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (term_cost_le grade ha).trans (Nat.le_max_left _ _)
    · exact (term_cost_le grade ha).trans (Nat.le_max_right _ _)
  · rw [max_le_iff, cost_le_iff, cost_le_iff]
    exact ⟨fun a ha => term_cost_le grade (List.mem_append_left _ ha),
      fun a ha => term_cost_le grade (List.mem_append_right _ ha)⟩

 theorem value_flatten (ps : List (Name k A)) : value ps.flatten = (ps.map value).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

omit [CommSemiring k] in
 theorem cost_flatten_le (grade : List A → ℕ) {ps : List (Name k A)} {b : ℕ}
    (h : ∀ p ∈ ps, cost grade p ≤ b) : cost grade ps.flatten ≤ b := by
  rw [cost_le_iff]
  intro a ha
  obtain ⟨p,hp,ha⟩ := List.mem_flatten.mp ha
  exact (term_cost_le grade ha).trans (h p hp)

 theorem cost_product_le (grade : List A → ℕ)
    (ha : ∀ u v, grade (u++v) = grade u + grade v) (p q : Name k A) :
    cost grade (product p q) ≤ cost grade p + cost grade q := by
  rw [cost_le_iff]
  intro x hx
  obtain ⟨a,ha',hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
  rw [ha]
  exact Nat.add_le_add (term_cost_le grade ha') (term_cost_le grade hb)

 theorem cost_oneName (grade : List A → ℕ) (h0 : grade [] = 0) :
    cost grade (oneName : Name k A) = 0 := by simp [oneName,cost,h0]

variable {R : Type*} [CommRing R]
def negate (p : Name R A) : Name R A := p.map (fun a => (-a.1,a.2))

@[simp] theorem value_negate (p : Name R A) : value (negate p) = -value p := by
  induction p with
  | nil => simp [negate]
  | cons a p ih =>
    change MonoidAlgebra.single (FreeMonoid.ofList a.2) (-a.1) + value (negate p) =
      -(MonoidAlgebra.single (FreeMonoid.ofList a.2) a.1 + value p)
    rw [MonoidAlgebra.single_neg,ih]
    abel

@[simp] theorem cost_negate (grade : List A → ℕ) (p : Name R A) :
    cost grade (negate p) = cost grade p := by
  simp only [negate,cost,List.map_map,Function.comp_def]

 theorem primrec_negate [Primcodable A] [Primcodable R] [Finite R] :
    Primrec (negate (R:=R) (A:=A)) := by
  exact Primrec.list_map Primrec.id
    (((Primrec.dom_finite (Neg.neg : R → R)).comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)).to₂
end
end SimpleFInftyOvergroups.EffectiveNames.Polynomial

end OAI
