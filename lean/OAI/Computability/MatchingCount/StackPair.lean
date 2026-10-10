import OAI.Computability.MatchingCount.StackRoutine

namespace OAI

section

namespace BinaryMatching.StackCode

def pairBits : List Bool → List Bool → List Bool
  | [],y => true::y
  | b::x,y => false::b::pairBits x y

@[simp] lemma pairBits_length (x y : List Bool) : (pairBits x y).length=2*x.length+y.length+1 := by
  induction x with
  | nil => simp [pairBits]
  | cons b x ih => simp only [pairBits,List.length_cons,ih]; omega

namespace Block
variable {r : ℕ}

def tagBody (src dst : Fin r) : Block r :=
  cases src skip ((pop src).seq ((push dst false).seq (push dst false)))
    ((pop src).seq ((push dst true).seq (push dst false)))

def tagAll (src dst : Fin r) : Block r := loop src (tagBody src dst)

lemma tagBody_runs (src dst : Fin r) (hne : src≠dst) (s : Store r) (b : Bool) (l : List Bool)
    (hs : s src=b::l) :
    (tagBody src dst).Runs s (Function.update (Function.update s src l) dst (false::b::s dst)) 4 := by
  have hp : (pop src).Runs s (Function.update s src l) 1 := by
    simpa only [hs,List.tail_cons] using pop_runs src s
  have hb := push_runs dst b (Function.update s src l)
  rw [Function.update_of_ne hne.symm] at hb
  have hf := push_runs dst false (Function.update (Function.update s src l) dst (b::s dst))
  simp only [Function.update_self,Function.update_idem] at hf
  have hx := seq_runs _ _ hp (seq_runs _ _ hb hf)
  cases b with
  | false => exact cases_runs_false _ _ _ _ (by simp [hs]) hx
  | true => exact cases_runs_true _ _ _ _ (by simp [hs]) hx

lemma pairBits_eq (x y : List Bool) :
    pairBits x y=x.flatMap (fun b => [false,b])++true::y := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [pairBits,ih]

lemma tagAll_runs (src dst : Fin r) (hne : src≠dst) (x y : List Bool) (s : Store r)
    (hs : s src=x.reverse) (hd : s dst=y) :
    (tagAll src dst).Runs s
      (Function.update (Function.update s src []) dst (x.flatMap (fun b => [false,b])++y))
      (5*x.length+1) := by
  induction x using List.reverseRecOn generalizing y s with
  | nil =>
    have he : Function.update (Function.update s src []) dst
        ([].flatMap (fun b => [false,b])++y)=s := by
      simp only [List.reverse_nil] at hs
      simp only [List.flatMap_nil,List.nil_append]
      rw [←hs,Function.update_eq_self,←hd,Function.update_eq_self]
    rw [he]
    apply loop_runs_empty
    simpa using hs
  | append_singleton x b ih =>
    have hs' : s src=b::x.reverse := by simpa using hs
    let s' := Function.update (Function.update s src x.reverse) dst (false::b::s dst)
    have hm := tagBody_runs src dst hne s b x.reverse hs'
    have hi := ih (false::b::y) s' (by simp [s',hne]) (by simp [s',hd])
    have hx := loop_runs_step src (tagBody src dst) (by simp [hs']) hm hi
    have he : Function.update (Function.update s' src []) dst
        (x.flatMap (fun b => [false,b])++false::b::y)=
        Function.update (Function.update s src []) dst
          ((x++[b]).flatMap (fun b => [false,b])++y) := by
      funext k
      by_cases hk : k=dst
      · subst k; simp [List.flatMap_append,List.append_assoc]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hk,hks]
    rw [he] at hx
    have ht : 4+(5*x.length+1)+1=5*(x++[b]).length+1 := by simp; omega
    rw [ht] at hx
    exact hx

def pairInto (src dst aux : Fin r) : Block r :=
  (reverseInto src aux).seq ((push dst true).seq (tagAll aux dst))

lemma pairInto_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (ha : s aux=[]) :
    (pairInto src dst aux).Runs s
      (Function.update (Function.update s src []) dst (pairBits (s src) (s dst)))
      (9*(s src).length+3) := by
  let s₁ := Function.update (Function.update s src []) aux ((s src).reverse++s aux)
  let s₂ := Function.update s₁ dst (true::s₁ dst)
  have h₁ := reverseInto_runs src aux hsa s
  have h₂ := push_runs dst true s₁
  have h₃ := tagAll_runs aux dst hda.symm (s src) (true::s dst) s₂
    (by simp [s₂,s₁,hda.symm,ha]) (by simp [s₂,s₁,hda,hsd.symm])
  rw [←pairBits_eq] at h₃
  have he : Function.update (Function.update s₂ aux []) dst (pairBits (s src) (s dst))=
      Function.update (Function.update s src []) dst (pairBits (s src) (s dst)) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp
    · by_cases hks : k=src
      · subst k; simp [s₂,s₁,hsd,hsa]
      · by_cases hka : k=aux
        · subst k; simp [s₂,s₁,ha,hda.symm,hsa.symm]
        · simp [s₂,s₁,Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₃
  have hx := seq_runs _ _ h₁ (seq_runs _ _ h₂ h₃)
  have ht : (4*(s src).length+1)+(1+(5*(s src).length+1))=9*(s src).length+3 := by omega
  rw [ht] at hx
  exact hx

def moveInto (src dst aux : Fin r) : Block r :=
  (reverseInto src aux).seq (reverseInto aux dst)

lemma moveInto_runs (src dst aux : Fin r) (hsd : src≠dst) (hsa : src≠aux) (hda : dst≠aux)
    (s : Store r) (hd : s dst=[]) (ha : s aux=[]) :
    (moveInto src dst aux).Runs s
      (Function.update (Function.update s src []) dst (s src)) (8*(s src).length+2) := by
  let s' := Function.update (Function.update s src []) aux ((s src).reverse++s aux)
  have h₁ := reverseInto_runs src aux hsa s
  have h₂ := reverseInto_runs aux dst hda.symm s'
  have he : Function.update (Function.update s' aux []) dst ((s' aux).reverse++s' dst)=
      Function.update (Function.update s src []) dst (s src) := by
    funext k
    by_cases hkd : k=dst
    · subst k; simp [s',ha,hd,hda,hsd.symm]
    · by_cases hks : k=src
      · subst k; simp [s',hsd,hsa]
      · by_cases hka : k=aux
        · subst k; simp [ha,hda.symm,hsa.symm]
        · simp [s',Function.update_of_ne,hkd,hks,hka]
  rw [he] at h₂
  have hh := seq_runs _ _ h₁ h₂
  have hl : (s' aux).length=(s src).length := by simp [s',ha]
  rw [hl] at hh
  have ht : (4*(s src).length+1)+(4*(s src).length+1)=8*(s src).length+2 := by omega
  rw [ht] at hh
  exact hh

def decodeRev (src dst : Fin r) : Block r where
  Label := Fin 7
  finite := inferInstance
  entry := 0
  code k := match k.val with
    | 0 => .branch src none (some 1) (some 6)
    | 1 => .pop src (some 2)
    | 2 => .branch src none (some 3) (some 4)
    | 3 => .push dst false (some 5)
    | 4 => .push dst true (some 5)
    | 5 => .pop src (some 0)
    | _ => .pop src none

lemma decodeRev_runs (src dst : Fin r) (hne : src≠dst) (x y : List Bool) (s : Store r)
    (hs : s src=pairBits x y) :
    (decodeRev src dst).Runs s
      (Function.update (Function.update s src y) dst (x.reverse++s dst)) (5*x.length+2) := by
  induction x generalizing s with
  | nil =>
    have hx : s src=true::y := hs
    have he : Function.update (Function.update s src y) dst ([].reverse++s dst)=
        Function.update s src y := by
      simp only [List.reverse_nil,List.nil_append]
      rw [←Function.update_of_ne hne.symm y s,Function.update_eq_self]
    rw [he]
    apply Steps.next
    simp [decodeRev,Instr.eval,hx]
    apply Steps.next
    simp [Instr.eval,hx]
    exact .refl _ _
  | cons b x ih =>
    let s' := Function.update (Function.update s dst (b::s dst)) src (pairBits x y)
    have hs' : s' src=pairBits x y := by simp [s']
    have hi := ih s' hs'
    have he : Function.update (Function.update s' src y) dst (x.reverse++s' dst)=
        Function.update (Function.update s src y) dst ((b::x).reverse++s dst) := by
      funext k
      by_cases hkd : k=dst
      · subst k; simp [s',hne.symm,List.reverse_cons,List.append_assoc]
      · by_cases hks : k=src
        · subst k; simp [s',hne]
        · simp [s',Function.update_of_ne,hkd,hks]
    rw [he] at hi
    have ht : 5*(b::x).length+2=(5*x.length+2)+1+1+1+1+1 := by simp; omega
    rw [ht]
    apply Steps.next
    simp [decodeRev,Instr.eval,hs,pairBits]
    apply Steps.next
    simp [Instr.eval,hs,pairBits]
    cases b <;>
      (apply Steps.next
       simp [Instr.eval]
       apply Steps.next
       simp [Instr.eval,hne.symm]
       apply Steps.next
       simp [Instr.eval,hne]
       convert hi using 1; simp [s',Function.update_comm hne,Function.update_idem,Block.Runs,decodeRev])

end Block
end BinaryMatching.StackCode
end

end OAI
