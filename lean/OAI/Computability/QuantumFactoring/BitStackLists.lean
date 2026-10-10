import Mathlib
import OAI.Computability.QuantumFactoring.BitStackPrograms

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram
variable {K : Type} [DecidableEq K]

/-- Reverse one stack onto another, preserving all symbols. -/
def reverseMove (a b : K) : Program K := .loop a (.push b false) (.push b true)
def clear (a : K) : Program K := .loop a .skip .skip

def duplicateReverse (a b t : K) : Program K :=
  .seq (.loop a (.seq (.push b false) (.push t false))
    (.seq (.push b true) (.push t true))) (reverseMove t a)

lemma update_comm (s : Store K) (a b : K) (x y : List Bool) (hab : a≠b) :
    Function.update (Function.update s a x) b y =
      Function.update (Function.update s b y) a x := by
  funext k
  by_cases ha : k=a <;> by_cases hb : k=b <;> simp_all [Function.update]

lemma clear_runs (a : K) (s : Store K) :
    Runs (clear a) s (Function.update s a []) (2*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update s a []=s := by rw [←hs,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    have ht : Function.update s a xs a=xs := by simp
    have hh := ih (Function.update s a xs) ht
    cases x
    · have hr := Runs.loop_false hs (Runs.skip (Function.update s a xs)) hh
      convert hr using 1 <;> first | rfl | simp only [Function.update_idem]
    · have hr := Runs.loop_true hs (Runs.skip (Function.update s a xs)) hh
      convert hr using 1 <;> first | rfl | simp only [Function.update_idem]

lemma reverseMove_runs (a b : K) (hab : a≠b) (s : Store K) :
    Runs (reverseMove a b) s
      (Function.update (Function.update s a []) b ((s a).reverse++s b))
      (2*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update s a []) b ([].reverse++s b)=s := by
      rw [List.reverse_nil,List.nil_append,←hs,Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let t := Function.update s a xs
    let u := Function.update t b (x::t b)
    have hua : u a=xs := by simp [u,t,hab]
    have htail := ih u hua
    have body : Runs (.push b x) t u 1 := Runs.push _ _ _
    have hr : Runs (reverseMove a b) s
        (Function.update (Function.update u a []) b (xs.reverse++u b)) (2*xs.length+1+1+1) := by
      cases x
      · exact Runs.loop_false (a:=1) (b:=2*xs.length+1) hs body htail
      · exact Runs.loop_true (a:=1) (b:=2*xs.length+1) hs body htail
    convert hr using 1
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;>
      simp_all [u,t,Function.update,List.reverse_cons,List.append_assoc]

lemma duplicateReverse_loop_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) :
    Runs (.loop a (.seq (.push b false) (.push t false))
      (.seq (.push b true) (.push t true))) s
      (Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
        t ((s a).reverse++s t)) (3*(s a).length+1) := by
  generalize hs : s a=xs at *
  induction xs generalizing s with
  | nil =>
    have he : Function.update (Function.update (Function.update s a []) b ([].reverse++s b))
        t ([].reverse++s t)=s := by
      rw [List.reverse_nil,List.nil_append,List.nil_append,←hs,Function.update_eq_self,
        Function.update_eq_self,Function.update_eq_self]
    rw [he]
    exact Runs.loop_nil hs
  | cons x xs ih =>
    let u := Function.update s a xs
    let w := Function.update u b (x::u b)
    let v := Function.update w t (x::w t)
    have hva : v a=xs := by simp [v,w,u,hab,hat]
    have htail := ih v hva
    have body : Runs (.seq (.push b x) (.push t x)) u v 2 :=
      Runs.seq (Runs.push _ _ _) (Runs.push _ _ _)
    have hr : Runs (.loop a (.seq (.push b false) (.push t false))
      (.seq (.push b true) (.push t true))) s
      (Function.update (Function.update (Function.update v a []) b (xs.reverse++v b))
        t (xs.reverse++v t)) (3*xs.length+1+2+1) := by
      cases x
      · exact Runs.loop_false (a:=2) (b:=3*xs.length+1) hs body htail
      · exact Runs.loop_true (a:=2) (b:=3*xs.length+1) hs body htail
    convert hr using 1
    funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht : k=t <;>
      simp_all [v,w,u,Function.update,List.reverse_cons,List.append_assoc]

lemma duplicateReverse_runs (a b t : K) (hab : a≠b) (hat : a≠t) (hbt : b≠t)
    (s : Store K) (ht : s t=[]) :
    Runs (duplicateReverse a b t) s (Function.update s b ((s a).reverse++s b))
      (5*(s a).length+2) := by
  let v := Function.update (Function.update (Function.update s a []) b ((s a).reverse++s b))
    t ((s a).reverse++s t)
  have hr := reverseMove_runs t a hat.symm v
  have hh := Runs.seq (duplicateReverse_loop_runs a b t hab hat hbt s) hr
  change Runs (.seq _ _) _ _ _
  convert hh using 1
  · funext k
    by_cases ha : k=a <;> by_cases hb : k=b <;> by_cases ht' : k=t <;>
      simp_all [v,Function.update]
  · simp only [v,Function.update_self,ht,List.append_nil,List.length_reverse]; omega

end ExactQuantumFactoring.BitStackProgram

end


end OAI
