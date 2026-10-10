import Mathlib
import OAI.Combinatorics.UniformKServer.BoundaryPartition

namespace OAI

noncomputable section
                               
section

namespace UniformKServer.EpochCut
open EpochShadow BoundaryPartition

def cut {n : ℕ} (k R : ℕ) : Finset (Fin n) → ℕ → List (Fin n) → List (Fin n) × List (Fin n)
  | _,_,[] => ([],[])
  | seen,c,r::w =>
    if k<(insert r seen).card ∧ c+1=R then ([r],w)
    else
      let q := cut k R (bookStep (k:=k) seen r) (c+if k<(insert r seen).card then 1 else 0) w
      (r::q.1,q.2)

theorem cut_append {n : ℕ} (k R : ℕ) (seen : Finset (Fin n)) (c : ℕ) (w : List (Fin n)) :
    (cut k R seen c w).1++(cut k R seen c w).2=w := by
  induction w generalizing seen c with
  | nil => rfl
  | cons r w ih =>
    by_cases h : k<(insert r seen).card ∧ c+1=R
    · simp only [cut,ite_eq_left h,List.singleton_append]
    · simpa only [cut,ite_eq_right h,List.cons_append,List.cons.injEq,true_and] using
        ih (bookStep seen r) (c+if k<(insert r seen).card then 1 else 0)

theorem cut_nonempty {n : ℕ} (k R : ℕ) (seen : Finset (Fin n)) (c : ℕ)
    (r : Fin n) (w : List (Fin n)) : (cut k R seen c (r::w)).1≠[] := by
  rw [cut]
  split_ifs <;> simp

theorem tail_shorter {n : ℕ} (k R : ℕ) (seen : Finset (Fin n)) (c : ℕ)
    (r : Fin n) (w : List (Fin n)) : (cut k R seen c (r::w)).2.length<(r::w).length := by
  have hh := congrArg List.length (cut_append k R seen c (r::w))
  have hn := List.length_pos_iff.mpr (cut_nonempty k R seen c r w)
  simp only [List.length_append] at hh
  omega

theorem split_cut {n : ℕ} (k R : ℕ) (seen : Finset (Fin n)) (c : ℕ)
    (acc w : List (Fin n)) (hw : w≠[]) :
    split k R seen c acc w =
      (acc++(cut k R seen c w).1)::split k R ∅ 0 [] (cut k R seen c w).2 := by
  induction w generalizing seen c acc with
  | nil => contradiction
  | cons r w ih =>
    by_cases he : k<(insert r seen).card
    · by_cases hc : c+1=R
      · simp [cut,split,he,hc]
      · simp only [cut,he,hc,and_false,ite_false,split,ite_true,bookStep]
        cases w with
        | nil => simp [split,cut]
        | cons r' w =>
          simpa only [List.append_assoc,List.singleton_append] using ih ∅ (c+1) (acc++[r]) (by simp)
    · simp only [cut,he,false_and,ite_false,split,bookStep,Nat.add_zero]
      cases w with
      | nil => simp [split,cut]
      | cons r' w =>
        simpa only [List.append_assoc,List.singleton_append] using ih (insert r seen) c (acc++[r]) (by simp)

end UniformKServer.EpochCut

end


end

end OAI
