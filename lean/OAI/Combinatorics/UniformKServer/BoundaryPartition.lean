import Mathlib
import OAI.Combinatorics.UniformKServer.EpochPartition

namespace OAI

noncomputable section
                                        
section

namespace UniformKServer.BoundaryPartition
open EpochShadow RawPartition EpochPartition

def join {A : Type} (R : ℕ) : ℕ → List A → List (List A) → List (List A)
  | _,acc,[] => if acc=[] then [] else [acc]
  | c,acc,b::bs => if c+1=R then (acc++b)::join R 0 [] bs else join R (c+1) (acc++b) bs

def split {n : ℕ} (k R : ℕ) : Finset (Fin n) → ℕ → List (Fin n) → List (Fin n) → List (List (Fin n))
  | _,_,acc,[] => if acc=[] then [] else [acc]
  | seen,c,acc,r::w =>
    if k<(insert r seen).card then
      if c+1=R then (acc++[r])::split k R ∅ 0 [] w
      else split k R ∅ (c+1) (acc++[r]) w
    else split k R (insert r seen) c (acc++[r]) w

theorem join_last {A : Type} (R c : ℕ) (acc b : List A) (hb : b≠[]) :
    join R c acc [b]=[acc++b] := by
  have hab : acc++b≠[] := by simp [hb]
  simp [join,hab]

theorem split_join {n : ℕ} (k R : ℕ) (c : ℕ) (pre p w : List (Fin n)) :
    split k R p.toFinset c (pre++p) w = join R c pre (pack k p w) := by
  induction w generalizing c pre p with
  | nil =>
    by_cases hp : p=[]
    · simp [split,pack,join,hp]
    · rw [pack,ite_eq_right hp,join_last R c pre p hp]
      have hh : pre++p≠[] := by simp [hp]
      simp [split,hh]
  | cons r w ih =>
    have he : (p++[r]).toFinset=insert r p.toFinset := by ext x;simp
    by_cases hend : k<(insert r p.toFinset).card
    · simp only [split,pack,he,ite_eq_left hend]
      by_cases hc : c+1=R
      · simp only [ite_eq_left hc,join]
        rw [←ih 0 [] []]
        simp
      · simp only [ite_eq_right hc,join]
        rw [←ih (c+1) (pre++(p++[r])) []]
        simp [List.append_assoc]
    · simp only [split,pack,he,ite_eq_right hend]
      simpa only [he,List.append_assoc] using ih c pre (p++[r])

theorem join_formula {A : Type} (R : ℕ) (c : ℕ) (hc : c<R) (acc : List A)
    (bs : List (List A)) (hbs : bs≠[]) (hb : ∀b∈bs,b≠[]) :
    join R c acc bs = (acc++(bs.take (R-c)).flatten)::join R 0 [] (bs.drop (R-c)) := by
  induction bs generalizing c acc with
  | nil => contradiction
  | cons b bs ih =>
    by_cases he : c+1=R
    · have hr : R-c=1 := by omega
      simp [join,he,hr]
    · have hr : R-c=(R-(c+1))+1 := by omega
      have hc' : c+1<R := by omega
      cases bs with
      | nil =>
        have hbn := hb b (by simp)
        rw [join_last R c acc b hbn]
        simp [hr,join]
      | cons b' bs =>
        have htail : ∀a∈b'::bs,a≠[] := fun a ha => hb a (by simp_all)
        rw [join,ite_eq_right he,ih (c+1) hc' (acc++b) (by simp) htail]
        simp only [hr,List.take_succ_cons,List.drop_succ_cons,List.flatten_cons,List.append_assoc]

theorem join_chunks {A : Type} (R : ℕ) (hR : 0<R) (bs : List (List A))
    (hb : ∀b∈bs,b≠[]) :
    join R 0 [] bs = (chunks R hR bs).map List.flatten := by
  induction bs using chunks.induct R hR with
  | case1 => simp [join,chunks]
  | case2 b bs ih =>
    rw [join_formula R 0 hR [] (b::bs) (by simp) hb]
    simp only [Nat.sub_zero,List.nil_append,chunks,List.map_cons]
    congr 1
    exact ih (fun a ha => hb a (List.mem_of_mem_drop ha))

theorem streamed_epochs {n : ℕ} (k R : ℕ) (hR : 0<R) (w : List (Fin n)) :
    split k R ∅ 0 [] w = epochs k R hR w := by
  have hh := split_join k R 0 [] [] w
  simp only [List.toFinset_nil,List.append_nil] at hh
  rw [hh,join_chunks R hR]
  · rfl
  · intro b hb
    obtain ⟨p,r,he,-⟩ := pack_good k [] w (by simp) b hb
    simp [he]

end UniformKServer.BoundaryPartition

end


end

end OAI
