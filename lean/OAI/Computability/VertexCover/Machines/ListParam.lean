import Mathlib
import OAI.Computability.VertexCover.Machines.ListMore

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

namespace WithParam
variable {α β : Type}

def step (p : (α × List (α × β)) × β) : α × List (α × β) :=
  (p.1.1,(p.1.1,p.2)::p.1.2)

theorem fold (xs : List β) (a : α) (out : List (α × β)) :
    xs.foldl (fun s b => step (s,b)) (a,out) = (a,(xs.map (a,·)).reverse++out) := by
  induction xs generalizing out with
  | nil => rfl
  | cons b xs ih =>
    change xs.foldl (fun s b => step (s,b)) (a,(a,b)::out) = _
    rw [ih]
    simp only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

theorem mapped_length (ea : α → List Bool) (eb : β → List Bool) (a : α) (xs : List β) :
    (listBits (prodBits ea eb) (xs.map (a,·))).length =
      (4*(ea a).length+2)*xs.length + (listBits eb xs).length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.map_cons,listBits_cons_length,prodBits,pairBits_length,ih,List.length_cons]
    ring

noncomputable def poly (ea : α → List Bool) (eb : β → List Bool) :
    Poly (prodBits (prodBits ea (listBits (prodBits ea eb))) eb)
      (prodBits ea (listBits (prodBits ea eb))) step := by
  let s := Poly.fst (prodBits ea (listBits (prodBits ea eb))) eb
  let a := s.comp (Poly.fst ea (listBits (prodBits ea eb)))
  let out := s.comp (Poly.snd ea (listBits (prodBits ea eb)))
  let b := Poly.snd (prodBits ea (listBits (prodBits ea eb))) eb
  exact (a.pair (((a.pair b).pair out).comp (Poly.listCons (prodBits ea eb)))).congr (fun _ => rfl)

end WithParam

noncomputable def Poly.withParam {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) :
    Poly (prodBits ea (listBits eb)) (listBits (prodBits ea eb))
      (fun p : α × List β => p.2.map (p.1,·)) := by
  let e := prodBits ea (listBits (prodBits ea eb))
  let size : Polynomial ℕ := 20*(Polynomial.X+1)^2
  have bound (s : α × List (α × β)) (xs pre suf : List β) (h : pre++suf=xs) :
      (prodBits e (listBits eb) (pre.foldl (fun s b => WithParam.step (s,b)) s,suf)).length ≤
        size.eval (prodBits e (listBits eb) (s,xs)).length := by
    rcases s with ⟨a,out⟩
    have hparts := listBits_append_length eb pre suf
    rw [h] at hparts
    have hp := list_length_le_bits eb pre
    have hadd := listBits_append_length (prodBits ea eb) (pre.map (a,·)).reverse out
    rw [listBits_reverse_length,WithParam.mapped_length] at hadd
    let N := (prodBits e (listBits eb) ((a,out),xs)).length
    have ha : (ea a).length ≤ N := by dsimp [N,e,prodBits]; rw [pairBits_length,pairBits_length]; omega
    have hx : (listBits eb xs).length ≤ N := by dsimp [N,prodBits]; rw [pairBits_length]; omega
    have hout : (listBits (prodBits ea eb) out).length ≤ N := by
      dsimp [N,e,prodBits]; rw [pairBits_length,pairBits_length]; omega
    have hpre : pre.length ≤ N := by
      have := listBits_length_pos eb suf
      omega
    have hpr := Nat.mul_le_mul ha hpre
    change _ ≤ size.eval N
    simp only [prodBits,e,pairBits_length,WithParam.fold,size,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,
      Polynomial.eval_one]
    nlinarith
  let c := Poly.fold eb e b₀ (WithParam.poly ea eb) size bound
  let input := ((Poly.fst ea (listBits eb)).pair
    (Poly.const (prodBits ea (listBits eb)) (listBits (prodBits ea eb)) [])).pair
      (Poly.snd ea (listBits eb))
  exact (((input.comp c).comp (Poly.snd ea (listBits (prodBits ea eb)))).comp
    (Poly.listReverse (prodBits ea eb) (a₀,b₀))).congr (fun p => by
      simp only [Function.comp_apply,WithParam.fold,List.append_nil,List.reverse_reverse])

noncomputable def Poly.listMapWith {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool)
    (ec : γ → List Bool) (a₀ : α) (b₀ : β) (c₀ : γ) {f : α × β → γ}
    (cf : Poly (prodBits ea eb) ec f) :
    Poly (prodBits ea (listBits eb)) (listBits ec)
      (fun p : α × List β => p.2.map (fun b => f (p.1,b))) :=
  ((Poly.withParam ea eb a₀ b₀).comp
    (Poly.listMap (prodBits ea eb) ec (a₀,b₀) c₀ cf)).congr (fun p => by
      simp only [Function.comp_apply,List.map_map,Function.comp_def])

theorem listBits_flatten_bound {α : Type} (e : α → List Bool) (xss : List (List α)) :
    (listBits e xss.flatten).length ≤ (listBits (listBits e) xss).length := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    have hh := listBits_append_length e xs xss.flatten
    simp only [List.flatten_cons,listBits_cons_length]
    omega

theorem foldl_reverseAppend {α : Type} (xs : List (List α)) (out : List α) :
    xs.foldl (fun b a => a.reverse++b) out = xs.flatten.reverse++out := by
  induction xs generalizing out with
  | nil => rfl
  | cons a xs ih => simp [List.foldl_cons,ih,List.append_assoc]

noncomputable def Poly.listFlatten {α : Type} (e : α → List Bool) (a₀ : α) :
    Poly (listBits (listBits e)) (listBits e) List.flatten := by
  have bound (out : List α) (xs pre suf : List (List α)) (h : pre++suf=xs) :
      (prodBits (listBits e) (listBits (listBits e))
        (pre.foldl (fun b a => a.reverse++b) out,suf)).length ≤
          (3*Polynomial.X+3).eval (prodBits (listBits e) (listBits (listBits e)) (out,xs)).length := by
    have hp := listBits_append_length (listBits e) pre suf
    rw [h] at hp
    have hf := listBits_flatten_bound e pre
    have hh := listBits_append_length e pre.flatten.reverse out
    rw [listBits_reverse_length] at hh
    simp only [prodBits,pairBits_length,foldl_reverseAppend,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  let c := Poly.fold (listBits e) (listBits e) [] (Poly.reverseAppend e a₀)
    (3*Polynomial.X+3) bound
  let input := (Poly.const (listBits (listBits e)) (listBits e) []).pair
    (Poly.identity (listBits (listBits e)))
  exact ((input.comp c).comp (Poly.listReverse e a₀)).congr (fun xs => by
    simp only [Function.comp_apply,foldl_reverseAppend,List.append_nil,List.reverse_reverse,id_eq])

noncomputable def Poly.listFlatMap {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (a₀ : α) (b₀ : β) {f : α → List β} (cf : Poly ea (listBits eb) f) :
    Poly (listBits ea) (listBits eb) (List.flatMap f) :=
  ((Poly.listMap ea (listBits eb) a₀ [] cf).comp (Poly.listFlatten eb b₀)).congr
    (fun _ => rfl)

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
