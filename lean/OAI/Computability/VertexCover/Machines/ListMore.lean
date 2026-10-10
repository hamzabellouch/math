import Mathlib
import OAI.Computability.VertexCover.Machines.Lists

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                         
section

namespace VertexCover.Machine
open UniqueGames.Foundations.Complexity

noncomputable def Poly.outputPolynomial {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (c : Poly ea eb f) : Polynomial ℕ :=
  Polynomial.X + Polynomial.C (Runtime.programPushBound c.computation.tm) * c.computation.time

theorem Poly.output_length {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (c : Poly ea eb f) (a : α) :
    (eb (f a)).length ≤ c.outputPolynomial.eval (ea a).length :=
  Runtime.encodedOutputLength c.computation a

theorem listBits_member_length {α : Type} (e : α → List Bool) {a : α} {xs : List α} (h : a ∈ xs) :
    (e a).length ≤ (listBits e xs).length := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rw [listBits_cons_length]
    rcases h with rfl | h
    · omega
    · have hh := ih h; omega

theorem foldl_cons_eq_reverse_append {α : Type} (xs b : List α) :
    xs.foldl (fun b a => a::b) b = xs.reverse ++ b := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih => simp [ih, List.append_assoc]

noncomputable def Poly.reverseAppend {α : Type} (e : α → List Bool) (a₀ : α) :
    Poly (prodBits (listBits e) (listBits e)) (listBits e)
      (fun p : List α × List α => p.2.reverse++p.1) := by
  let c := (Poly.swap (listBits e) e).comp (Poly.listCons e)
  have bound (b xs pre suf : List α) (h : pre++suf=xs) :
      (prodBits (listBits e) (listBits e) (pre.foldl (fun b a => a::b) b, suf)).length ≤
        (Polynomial.C 2 * Polynomial.X + 1).eval
          (prodBits (listBits e) (listBits e) (b,xs)).length := by
    simp only [prodBits, pairBits_length, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_one, foldl_cons_eq_reverse_append]
    have h₁ := listBits_append_length e pre.reverse b
    have h₂ := listBits_append_length e pre suf
    rw [listBits_reverse_length] at h₁
    rw [h] at h₂
    omega
  exact (Poly.fold e (listBits e) a₀ c (Polynomial.C 2 * Polynomial.X+1) bound).congr
    (fun p => foldl_cons_eq_reverse_append p.2 p.1)

noncomputable def Poly.listReverse {α : Type} (e : α → List Bool) (a₀ : α) :
    Poly (listBits e) (listBits e) List.reverse :=
  (((Poly.const (listBits e) (listBits e) []).pair (Poly.identity (listBits e))).comp
    (Poly.reverseAppend e a₀)).congr (fun _ => List.append_nil _)

noncomputable def Poly.listAppend {α : Type} (e : α → List Bool) (a₀ : α) :
    Poly (prodBits (listBits e) (listBits e)) (listBits e)
      (fun p : List α × List α => p.1++p.2) := by
  let c := Poly.snd (listBits e) (listBits e)
  let d := (Poly.fst (listBits e) (listBits e)).comp (Poly.listReverse e a₀)
  exact ((c.pair d).comp (Poly.reverseAppend e a₀)).congr
    (fun p => by simp only [Function.comp_apply, List.reverse_reverse])

theorem listBits_map_bound {α β : Type} (eb : β → List Bool)
    (f : α → β) (xs : List α) (B : ℕ) (h : ∀ a ∈ xs, (eb (f a)).length ≤ B) :
    (listBits eb (xs.map f)).length ≤ (2*B+2)*xs.length+1 := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have h₁ := h a (by simp)
    have h₂ := ih (fun x hx => h x (by simp [hx]))
    simp only [List.map_cons, listBits_cons_length, List.length_cons]
    nlinarith

theorem foldl_map_cons {α β : Type} (f : α → β) (xs : List α) (b : List β) :
    xs.foldl (fun b a => f a::b) b = (xs.map f).reverse++b := by
  induction xs generalizing b with
  | nil => rfl
  | cons a as ih => simp [ih, List.append_assoc]

noncomputable def Poly.mapFold {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a₀ : α)
    {f : α → β} (cf : Poly ea eb f) :
    Poly (prodBits (listBits eb) (listBits ea)) (listBits eb)
      (fun p : List β × List α => (p.2.map f).reverse++p.1) := by
  let c := (((Poly.snd (listBits eb) ea).comp cf).pair
    (Poly.fst (listBits eb) ea)).comp (Poly.listCons eb)
  let size : Polynomial ℕ := 3*Polynomial.X +
    2*(2*cf.outputPolynomial+2)*Polynomial.X + 4
  have bound (b : List β) (xs pre suf : List α) (h : pre++suf=xs) :
      (prodBits (listBits eb) (listBits ea)
        (pre.foldl (fun b a => f a::b) b,suf)).length ≤
          size.eval (prodBits (listBits eb) (listBits ea) (b,xs)).length := by
    let N := (prodBits (listBits eb) (listBits ea) (b,xs)).length
    have hs : (listBits ea xs).length ≤ N := by dsimp [N,prodBits]; rw [pairBits_length]; omega
    have hb : (listBits eb b).length ≤ N := by dsimp [N,prodBits]; rw [pairBits_length]; omega
    have hp : pre.length ≤ N := by
      have := list_length_le_bits ea xs
      have hh := congrArg List.length h
      simp only [List.length_append] at hh
      omega
    have hparts := listBits_append_length ea pre suf
    rw [h] at hparts
    have hsf : (listBits ea suf).length ≤ N := by
      have := listBits_length_pos ea pre
      omega
    have hmap : (listBits eb (pre.map f)).length ≤
        (2*cf.outputPolynomial.eval N+2)*pre.length+1 :=
      listBits_map_bound eb f pre _ (fun a ha =>
        (cf.output_length a).trans (MachineComposition.natPolynomial_eval_mono _
          ((listBits_member_length ea (show a ∈ xs by rw [← h]; simp [ha])).trans hs)))
    have hac := listBits_append_length eb (pre.map f).reverse b
    rw [listBits_reverse_length] at hac
    change _ ≤ size.eval N
    simp only [prodBits, pairBits_length, foldl_map_cons]
    have hm := Nat.mul_le_mul_left (2*cf.outputPolynomial.eval N+2) hp
    simp only [size, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    nlinarith
  exact (Poly.fold ea (listBits eb) a₀ c size bound).congr (fun p => foldl_map_cons f p.2 p.1)

noncomputable def Poly.listMap {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {f : α → β} (cf : Poly ea eb f) :
    Poly (listBits ea) (listBits eb) (List.map f) := by
  let c := ((Poly.const (listBits ea) (listBits eb) []).pair
    (Poly.identity (listBits ea))).comp (Poly.mapFold ea eb a₀ cf)
  exact (c.comp (Poly.listReverse eb b₀)).congr (fun p => by
    simp only [Function.comp_apply, List.append_nil, List.reverse_reverse, id_eq])

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
