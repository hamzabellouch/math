import OAI.Computability.MatchingCount.StackMacros

namespace OAI

section

namespace BinaryMatching.StackCode.Block
variable {r : ℕ}

def moveTwoBody (src dst aux : Fin r) : Block r :=
  cases src skip
    ((pop src).seq ((push dst false).seq (push aux false)))
    ((pop src).seq ((push dst true).seq (push aux true)))

def reverseIntoTwo (src dst aux : Fin r) : Block r := loop src (moveTwoBody src dst aux)

lemma moveTwoBody_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (a : Bool) (l : List Bool) (hs : s src=a::l) :
    (moveTwoBody src dst aux).Runs s
      (Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)) 4 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have hd := push_runs dst a (Function.update s src l)
  rw [Function.update_of_ne hsd.symm] at hd
  have ha := push_runs aux a (Function.update (Function.update s src l) dst (a::s dst))
  rw [Function.update_of_ne hda.symm,Function.update_of_ne hsa.symm] at ha
  have hseq : ((pop src).seq ((push dst a).seq (push aux a))).Runs s
      (Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)) 3 :=
    seq_runs _ _ hp (seq_runs _ _ hd ha)
  cases a with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hseq
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hseq

lemma reverseIntoTwo_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) :
    (reverseIntoTwo src dst aux).Runs s
      (Function.update (Function.update (Function.update s src []) dst ((s src).reverse++s dst))
        aux ((s src).reverse++s aux)) (5*(s src).length+1) := by
  generalize hl : s src=l
  induction l generalizing s with
  | nil =>
    have he : Function.update (Function.update (Function.update s src []) dst ([].reverse++s dst))
        aux ([].reverse++s aux)=s := by
      rw [←hl,Function.update_eq_self]
      simp only [hl,List.reverse_nil,List.nil_append,Function.update_eq_self]
    rw [he]
    exact loop_runs_empty src (moveTwoBody src dst aux) s hl
  | cons a l ih =>
    let s' := Function.update (Function.update (Function.update s src l) dst (a::s dst)) aux (a::s aux)
    have hs' : s' src=l := by simp [s',hsd,hsa]
    have hi := ih s' hs'
    have hm := moveTwoBody_runs src dst aux hsd hsa hda s a l hl
    have hx := loop_runs_step src (moveTwoBody src dst aux) (by simp [hl]) hm hi
    have he : Function.update (Function.update (Function.update s' src []) dst (l.reverse++s' dst))
        aux (l.reverse++s' aux)=
        Function.update (Function.update (Function.update s src []) dst ((a::l).reverse++s dst))
          aux ((a::l).reverse++s aux) := by
      funext k
      by_cases hka : k=aux
      · subst k; simp [List.reverse_cons,List.append_assoc,s']
      · by_cases hkd : k=dst
        · subst k; simp [hda,List.reverse_cons,List.append_assoc,s']
        · by_cases hks : k=src
          · subst k; simp [hsd,hsa,s']
          · simp [Function.update_of_ne,hka,hkd,hks,s']
    rw [he] at hx
    have ht : 4+(5*l.length+1)+1=5*(a::l).length+1 := by simp only [List.length_cons]; omega
    rw [ht] at hx
    exact hx

def copy (src dst aux : Fin r) : Block r :=
  (clear dst).seq ((reverseInto src aux).seq (reverseIntoTwo aux src dst))

lemma copy_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (ha : s aux=[]) :
    (copy src dst aux).Runs s (Function.update s dst (s src))
      (2*(s dst).length+9*(s src).length+3) := by
  let s₁ := Function.update s dst []
  let s₂ := Function.update (Function.update s₁ src []) aux ((s₁ src).reverse++s₁ aux)
  have h₁ := clear_runs dst s
  have h₂ := reverseInto_runs src aux hsa s₁
  have h₃ := reverseIntoTwo_runs aux src dst hsa.symm hda.symm hsd s₂
  have he : Function.update
      (Function.update (Function.update s₂ aux []) src ((s₂ aux).reverse++s₂ src))
        dst ((s₂ aux).reverse++s₂ dst)=Function.update s dst (s src) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp [s₂,s₁,hsd,hsa,hda,hsd.symm,hda.symm,ha]
    · by_cases hks : k=src
      · subst k; simp [s₂,s₁,hsd,hsa,hda,hsd.symm,hda.symm,ha]
      · by_cases hka : k=aux
        · subst k; simp [s₂,s₁,hsd,hsa,hda,ha,Ne.symm]
        · simp [s₂,s₁,Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₃
  have hh := seq_runs (clear dst) _ h₁ (seq_runs _ _ h₂ h₃)
  change (copy src dst aux).Runs s (Function.update s dst (s src)) _ at hh
  have hlen₁ : (s₁ src).length=(s src).length := by simp [s₁,hsd]
  have hlen₂ : (s₂ aux).length=(s src).length := by simp [s₂,s₁,hsd,hda.symm,ha]
  rw [hlen₁,hlen₂] at hh
  have ht : (2*(s dst).length+1)+(4*(s src).length+1+(5*(s src).length+1))=
      2*(s dst).length+9*(s src).length+3 := by omega
  rw [ht] at hh
  exact hh

end BinaryMatching.StackCode.Block
end

end OAI
