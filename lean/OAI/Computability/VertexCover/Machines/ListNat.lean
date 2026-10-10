import Mathlib
import OAI.Computability.VertexCover.PCP.PoweringLabels
import OAI.Computability.VertexCover.Machines.ListMore
import OAI.Computability.VertexCover.Machines.Naturals

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

theorem listBits_tail_length_le {α : Type} (e : α → List Bool) (xs : List α) :
    (listBits e xs.tail).length ≤ (listBits e xs).length := by
  cases xs with
  | nil => exact le_rfl
  | cons a xs => simp only [List.tail_cons,listBits_cons_length]; omega

theorem listBits_drop_length_le {α : Type} (e : α → List Bool) (n : ℕ) (xs : List α) :
    (listBits e (xs.drop n)).length ≤ (listBits e xs).length := by
  have h := listBits_append_length e (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  have := listBits_length_pos e (xs.take n)
  omega

theorem iterate_tail {α : Type} (k : ℕ) (xs : List α) :
    Iterate.run List.tail k xs = xs.drop k := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => simp only [Iterate.run,ih,List.drop_tail]

noncomputable def Poly.listDrop {α : Type} (e : α → List Bool) :
    Poly (prodBits natBits (listBits e)) (listBits e)
      (fun p : ℕ × List α => p.2.drop p.1) := by
  let c := Poly.iterate (listBits e) (Poly.listTail e) Polynomial.X (by
    intro n xs k l h
    simp only [Polynomial.eval_X,prodBits,pairBits_length,natBits_length,iterate_tail]
    have hd := listBits_drop_length_le e k xs
    omega)
  exact c.congr (fun p => iterate_tail p.1 p.2)

noncomputable def Poly.listGetD {α : Type} (e : α → List Bool) (a : α) :
    Poly (prodBits natBits (listBits e)) e
      (fun p : ℕ × List α => (p.2.drop p.1).headD a) :=
  (Poly.listDrop e).comp (Poly.listHeadD e a)

theorem foldl_count {α : Type} (xs : List α) (a : ℕ) :
    xs.foldl (fun n _ => n+1) a = xs.length+a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons,ih,List.length_cons]; omega

noncomputable def Poly.lengthFold {α : Type} (e : α → List Bool) (a : α) :
    Poly (prodBits natBits (listBits e)) natBits
      (fun p : ℕ × List α => p.2.length+p.1) := by
  let step := (Poly.fst natBits e).comp Poly.natSucc
  let size : Polynomial ℕ := 3*Polynomial.X+3
  have bound (b : ℕ) (xs pre suf : List α) (h : pre++suf=xs) :
      (prodBits natBits (listBits e) (pre.foldl (fun n _ => n+1) b,suf)).length ≤
        size.eval (prodBits natBits (listBits e) (b,xs)).length := by
    have hd := listBits_append_length e pre suf
    rw [h] at hd
    have hl := list_length_le_bits e pre
    simp only [prodBits,pairBits_length,natBits_length,size,Polynomial.eval_add,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,foldl_count]
    omega
  exact (Poly.fold e natBits a step size bound).congr (fun p => foldl_count p.2 p.1)

noncomputable def Poly.listLength {α : Type} (e : α → List Bool) (a : α) :
    Poly (listBits e) natBits List.length :=
  (((Poly.const (listBits e) natBits 0).pair (Poly.identity (listBits e))).comp
    (Poly.lengthFold e a)).congr (fun _ => Nat.add_zero _)

namespace RawList

def trans (_ : Unit) (b : Bool) : Unit × List Bool := ((),[true,true,b,false])

theorem encode (bs : List Bool) :
    Stream.output trans (fun _ => [false]) () bs = listBits boolBits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [Stream.output,trans, ih]; rfl

end RawList

noncomputable def Poly.rawToList : Poly (id : List Bool → List Bool) (listBits boolBits) id :=
  (Stream.poly () RawList.trans (fun _ => [false]) 4 (by intros; rfl) (by intros; decide)).realizes
    RawList.encode

namespace Range

def step (p : ℕ × List ℕ) : ℕ × List ℕ := (p.1+1,p.1::p.2)

theorem run (k a : ℕ) (xs : List ℕ) :
    Iterate.run step k (a,xs) = (a+k,(List.range' a k).reverse++xs) := by
  induction k generalizing a xs with
  | zero => simp [Iterate.run]
  | succ k ih =>
    simp only [Iterate.run,step,ih,List.range'_succ,List.reverse_cons,List.append_assoc,
      List.singleton_append]
    congr 1; omega

theorem bits_bound (k a : ℕ) :
    (listBits natBits (List.range' a k)).length ≤ (2*(a+k)+2)*k+1 := by
  have h := listBits_map_bound natBits id (List.range' a k) (a+k) (by
    intro b hb
    simp only [id_eq,natBits_length]
    exact (List.mem_range'_1.mp hb).2.le)
  simpa using h

noncomputable def poly : Poly (prodBits natBits (listBits natBits))
    (prodBits natBits (listBits natBits)) step := by
  let n := Poly.fst natBits (listBits natBits)
  let xs := Poly.snd natBits (listBits natBits)
  exact ((n.comp Poly.natSucc).pair ((n.pair xs).comp (Poly.listCons natBits))).congr (fun _ => rfl)

end Range

noncomputable def Poly.range : Poly natBits (listBits natBits) List.range := by
  let e := prodBits natBits (listBits natBits)
  let size : Polynomial ℕ := 20*(Polynomial.X+1)^2
  have bound (n : ℕ) (p : ℕ × List ℕ) (k l : ℕ) (h : k+l=n) :
      (prodBits natBits e (l,Iterate.run Range.step k p)).length ≤
        size.eval (prodBits natBits e (n,p)).length := by
    rcases p with ⟨a,xs⟩
    have hk : k ≤ n := by omega
    have hl : l ≤ n := by omega
    have hd := listBits_append_length natBits (List.range' a k).reverse xs
    rw [listBits_reverse_length] at hd
    have hb := Range.bits_bound k a
    have hk₂ := Nat.mul_le_mul hk hk
    have hak := Nat.mul_le_mul_left a hk
    simp only [prodBits,e,pairBits_length,natBits_length,Range.run,size,
      Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    nlinarith
  let c := Poly.iterate e Range.poly size bound
  let input := (Poly.identity natBits).pair
    ((Poly.const natBits natBits 0).pair (Poly.const natBits (listBits natBits) []))
  exact (((input.comp c).comp (Poly.snd natBits (listBits natBits))).comp
    (Poly.listReverse natBits 0)).congr (fun n => by
      simp only [Function.comp_apply,Range.run,Nat.zero_add,← List.range_eq_range',
        List.append_nil,List.reverse_reverse,id_eq])

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
