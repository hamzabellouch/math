import Mathlib
import OAI.GroupTheory.SimpleOvergroups.PrefixLists

namespace OAI


namespace BinaryPrefixOperators.Arithmetic
variable (K : Type*) [CommRing K]

def cancel (w u : Word) : Option Pair :=
  if u.take w.length = w then some (u.drop w.length, []) else
    if w.take u.length = u then some ([], w.drop u.length) else none

noncomputable section

theorem deletion_insertion (w u : Word) :
    deletion K w * insertion K u =
      if u.take w.length = w then insertion K (u.drop w.length) else
        if w.take u.length = u then deletion K (w.drop u.length) else 0 := by
  induction w generalizing u with
  | nil => simp
  | cons i w ih =>
    cases u with
    | nil => simp
    | cons j u =>
      have hh : (deletion K w * r K i) * (l K j * insertion K u) =
          deletion K w * (r K i * l K j) * insertion K u := by simp [mul_assoc]
      rw [deletion_cons, prefix_cons, hh, r_l]
      by_cases hij : i=j
      · subst j
        simp only [List.length_cons, List.take_succ_cons,
          List.drop_succ_cons, List.cons.injEq, true_and]
        exact ih u
      · simp [hij, Ne.symm hij]

theorem deletion_insertion_cancel (w u : Word) :
    deletion K w * insertion K u = (cancel w u).elim 0 (replacement K) := by
  rw [deletion_insertion]
  unfold cancel
  split
  · simp [replacement]
  · split <;> simp [replacement]

end

def multiplyPair (p q : Pair) : Option Pair :=
  (cancel p.2 q.1).map (fun r => (p.1++r.1,q.2++r.2))

noncomputable section
 theorem replacement_mul (p q : Pair) :
    replacement K p * replacement K q = (multiplyPair p q).elim 0 (replacement K) := by
  have hh : replacement K p * replacement K q =
      insertion K p.1 * (deletion K p.2 * insertion K q.1) * deletion K q.2 := by
    simp [replacement, mul_assoc]
  rw [hh, deletion_insertion_cancel]
  cases h : cancel p.2 q.1 with
  | none => simp [multiplyPair, h]
  | some r => simp [multiplyPair, h, replacement, mul_assoc]
end

namespace Lists
variable {K}

def mulTerm (a b : K × Pair) : Poly K :=
  ((multiplyPair a.2 b.2).map (fun p => (a.1*b.1,p))).toList

def product (p q : Poly K) : Poly K :=
  p.flatMap (fun a => q.flatMap (mulTerm a))

noncomputable def value (p : Poly K) : algebra K := evaluate K (toArray p)

@[simp] theorem value_nil : value ([] : Poly K) = 0 := rfl
@[simp] theorem value_cons (a : K) (p : Pair) (ps : Poly K) :
    value ((a,p)::ps) = a • replacement K p + value ps := by
  simp [value]
@[simp] theorem value_append (p q : Poly K) : value (p++q) = value p + value q := by
  simp [value]

@[simp] theorem value_singleton (a : K) (p : Pair) :
    value [(a,p)] = a • replacement K p := by simp

 theorem value_mulTerm (a b : K × Pair) :
    value (mulTerm a b) = (a.1 • replacement K a.2) * (b.1 • replacement K b.2) := by
  rw [smul_mul_smul_comm, replacement_mul]
  cases h : multiplyPair a.2 b.2 <;> simp [mulTerm, h]

 theorem value_product (p q : Poly K) : value (product p q) = value p * value q := by
  induction p with
  | nil => simp [product]
  | cons a p ih =>
    rcases a with ⟨a,v⟩
    simp only [product, List.flatMap_cons, value_append, value_cons, add_mul] at *
    rw [ih]
    congr 1
    clear ih
    induction q with
    | nil => simp
    | cons b q ih =>
      rcases b with ⟨b,w⟩
      simp only [List.flatMap_cons, value_append, value_cons, value_mulTerm, mul_add, ih]

theorem value_surjective : Function.Surjective (value (K:=K)) := by
  intro x
  have hx := x.property
  change x.val ∈ Algebra.adjoin K (Set.range (left K) ∪ Set.range (right K)) at hx
  have hh : ∃ p : Poly K, (value p : Module.End K (Space K)) = x.val := by
    apply Algebra.adjoin_induction (p := fun x _ => ∃ p : Poly K,
      (value p : Module.End K (Space K)) = x) ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hx with ⟨i,rfl⟩ | ⟨i,rfl⟩
      · exact ⟨[(1,([i],[]))], by simp [replacement, l]⟩
      · exact ⟨[(1,([],[i]))], by simp [replacement, r]⟩
    · intro a
      exact ⟨[(a,([],[]))], by simp [replacement, Algebra.algebraMap_eq_smul_one]⟩
    · intro x y hx hy hp hq
      obtain ⟨p,rfl⟩ := hp
      obtain ⟨q,rfl⟩ := hq
      exact ⟨p++q, by simp⟩
    · intro x y hx hy hp hq
      obtain ⟨p,rfl⟩ := hp
      obtain ⟨q,rfl⟩ := hq
      exact ⟨product p q, by simp [value_product]⟩
  obtain ⟨p,hp⟩ := hh
  exact ⟨p, Subtype.ext hp⟩

end Lists
end BinaryPrefixOperators.Arithmetic

end OAI
