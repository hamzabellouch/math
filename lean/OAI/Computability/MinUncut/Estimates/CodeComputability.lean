import Mathlib
import OAI.Computability.MinUncut.Model

namespace OAI

namespace MinUncut.CodeEffective
open Turing.ToPartrec
abbrev NCode := Nat.Partrec.Code

def embed : Code → NCode
  | .zero' => .zero
  | .succ => .succ
  | .tail => .left
  | .cons f g => .pair (embed f) (embed g)
  | .comp f g => .comp (embed f) (embed g)
  | .case f g => .prec (embed f) (embed g)
  | .fix f => .rfind' (embed f)

def retract : NCode → Code
  | .zero => .zero'
  | .succ => .succ
  | .left => .tail
  | .right => .tail
  | .pair f g => .cons (retract f) (retract g)
  | .comp f g => .comp (retract f) (retract g)
  | .prec f g => .case (retract f) (retract g)
  | .rfind' f => .fix (retract f)
lemma retract_embed (c : Code) : retract (embed c)=c := by
  induction c <;> simp_all [embed,retract]

def normalize : NCode → NCode := fun c=>embed (retract c)
lemma primrec_normalize : Primrec normalize := by
  have h := Nat.Partrec.Code.primrec_recOn (α:=NCode) (σ:=NCode) (c:=id) Primrec.id
    (z:=fun _=>Nat.Partrec.Code.zero) (Primrec.const _) (s:=fun _=>Nat.Partrec.Code.succ) (Primrec.const _)
    (l:=fun _=>Nat.Partrec.Code.left) (Primrec.const _) (r:=fun _=>Nat.Partrec.Code.left) (Primrec.const _)
    (pr:=fun _ _ _ x y=>Nat.Partrec.Code.pair x y)
    (Nat.Partrec.Code.primrec₂_pair.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (co:=fun _ _ _ x y=>Nat.Partrec.Code.comp x y)
    (Nat.Partrec.Code.primrec₂_comp.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (pc:=fun _ _ _ x y=>Nat.Partrec.Code.prec x y)
    (Nat.Partrec.Code.primrec₂_prec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (rf:=fun _ _ x=>Nat.Partrec.Code.rfind' x)
    (Nat.Partrec.Code.primrec_rfind'.comp (Primrec.snd.comp Primrec.snd))
  apply h.of_eq
  intro c
  induction c <;> simp_all [normalize,embed,retract]

instance : Primcodable Code where
  __ := Encodable.ofLeftInverse embed retract retract_embed
  prim := by
    have h := (Primrec.succ.comp (Primrec.encode.comp
      (primrec_normalize.comp (Primrec.ofNat NCode))))
    apply (Primrec.nat_iff.mp h).of_eq
    intro n
    change Encodable.encode (embed (retract (Denumerable.ofNat NCode n))) + 1 =
      @Encodable.encode (Option Code) _ ((Encodable.decode (α:=NCode) n).bind (some ∘ retract))
    rw [Denumerable.decode_eq_ofNat]
    rfl

lemma primrec_embed : Primrec embed := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode

lemma primrec_retract : Primrec retract := by
  apply Primrec.encode_iff.mp
  exact Primrec.encode.comp primrec_normalize

lemma primrec_cons : Primrec₂ Code.cons := by
  change Primrec (fun p : Code × Code=>Code.cons p.1 p.2)
  exact (primrec_retract.comp
    (Nat.Partrec.Code.primrec₂_pair.comp
      (primrec_embed.comp Primrec.fst) (primrec_embed.comp Primrec.snd))).of_eq
        (by intro p; simp [retract,retract_embed])
lemma primrec_comp : Primrec₂ Code.comp := by
  exact (primrec_retract.comp
    (Nat.Partrec.Code.primrec₂_comp.comp
      (primrec_embed.comp Primrec.fst) (primrec_embed.comp Primrec.snd))).of_eq
        (by intro p; simp [retract,retract_embed])
lemma primrec_case : Primrec₂ Code.case := by
  exact (primrec_retract.comp
    (Nat.Partrec.Code.primrec₂_prec.comp
      (primrec_embed.comp Primrec.fst) (primrec_embed.comp Primrec.snd))).of_eq
        (by intro p; simp [retract,retract_embed])
lemma primrec_fix : Primrec Code.fix := by
  exact (primrec_retract.comp
    (Nat.Partrec.Code.primrec_rfind'.comp primrec_embed)).of_eq
      (by intro c; simp [retract,retract_embed])
lemma computable_cons : Computable₂ Code.cons := primrec_cons.to_comp
lemma computable_comp : Computable₂ Code.comp := primrec_comp.to_comp
lemma computable_case : Computable₂ Code.case := primrec_case.to_comp
lemma computable_fix : Computable Code.fix := primrec_fix.to_comp
end MinUncut.CodeEffective

namespace MinUncut.Costed
open Turing.ToPartrec

def bitsize (v : List ℕ) : ℕ := (Turing.PartrecToTM2.trList v).length

inductive CodeRun : Code → List ℕ → List ℕ → ℕ → Prop
  | zero (v) : CodeRun .zero' v (0::v) 1
  | succ (v) : CodeRun .succ v [v.headI+1] (32*(bitsize v+1))
  | tail (v) : CodeRun .tail v v.tail (32*(bitsize v+1))
  | cons {f fs v u w t t'} : CodeRun f v u t → CodeRun fs v w t' →
      CodeRun (.cons f fs) v (u.headI::w) (t+t'+32*(bitsize v+bitsize u+1))
  | comp {f g v u w t t'} : CodeRun g v u t → CodeRun f u w t' →
      CodeRun (.comp f g) v w (t+t'+1)
  | caseZero {f g v w t} : v.headI=0 → CodeRun f v.tail w t →
      CodeRun (.case f g) v w (t+32*(bitsize v+1))
  | caseSucc {f g v a w t} : CodeRun g (a::v) w t →
      CodeRun (.case f g) ((a+1)::v) w (t+32*(bitsize ((a+1)::v)+1))
  | fixDone {f v u t} : CodeRun f v u t → u.headI=0 →
      CodeRun (.fix f) v u.tail (t+1)
  | fixMore {f v u a w t t'} : CodeRun f v ((a+1)::u) t →
      CodeRun (.fix f) u w t' →
      CodeRun (.fix f) v w (t+t'+32*(bitsize ((a+1)::u)+1))

theorem CodeRun.sound {c v w t} (h : CodeRun c v w t) : w ∈ c.eval v := by
  induction h with
  | zero => simp
  | succ => simp
  | tail => simp
  | cons h h' ih ih' =>
    simp only [Code.cons_eval, Part.bind_eq_bind, Part.mem_bind_iff]
    exact ⟨_,ih,_,ih',by simp⟩
  | comp h h' ih ih' =>
    exact Part.mem_bind ih ih'
  | caseZero hz h ih => simpa only [Code.case_eval,hz,Nat.rec_zero] using ih
  | caseSucc h ih => simpa only [Code.case_eval,List.headI_cons,List.tail_cons,Nat.rec_add_one] using ih
  | fixDone h hz ih =>
    rw [Code.fix_eval]
    apply PFun.mem_fix_iff.mpr
    left
    exact (Part.mem_map_iff _).mpr ⟨_,ih,by simp [hz]⟩
  | @fixMore f v u a w t t' h h' ih ih' =>
    rw [Code.fix_eval]
    apply PFun.mem_fix_iff.mpr
    right
    refine ⟨u,?_,?_⟩
    · exact (Part.mem_map_iff _).mpr ⟨_,ih,by simp⟩
    · simpa only [Code.fix_eval] using ih'

theorem CodeRun.complete {c : Code} {v w : List ℕ} (h : w ∈ c.eval v) :
    ∃ t, CodeRun c v w t := by
  induction c generalizing v w with
  | zero' =>
    have hw : w=0::v := by simpa using h
    subst w
    exact ⟨_, .zero _⟩
  | succ =>
    have hw : w=[v.headI+1] := by simpa using h
    subst w
    exact ⟨_, .succ _⟩
  | tail =>
    have hw : w=v.tail := by simpa using h
    subst w
    exact ⟨_, .tail _⟩
  | cons f fs ih ih' =>
    rcases (Part.mem_bind_iff.mp h) with ⟨u,hu,hrest⟩
    rcases (Part.mem_bind_iff.mp hrest) with ⟨w',hw',hw⟩
    have he : w=u.headI::w' := by simpa using hw
    subst w
    obtain ⟨t,ht⟩ := ih hu
    obtain ⟨t',ht'⟩ := ih' hw'
    exact ⟨_, .cons ht ht'⟩
  | comp f g ih ih' =>
    obtain ⟨u,hu,hw⟩ := Part.mem_bind_iff.mp h
    obtain ⟨t,ht⟩ := ih' hu
    obtain ⟨t',ht'⟩ := ih hw
    exact ⟨_, .comp ht ht'⟩
  | case f g ih ih' =>
    cases v with
    | nil =>
      obtain ⟨t,ht⟩ := ih (by simpa using h)
      exact ⟨_, .caseZero rfl ht⟩
    | cons a v =>
      cases a with
      | zero =>
        obtain ⟨t,ht⟩ := ih (by simpa using h)
        exact ⟨_, .caseZero rfl ht⟩
      | succ a =>
        obtain ⟨t,ht⟩ := ih' (by simpa using h)
        exact ⟨_, .caseSucc ht⟩
  | fix f ih =>
    rw [Code.fix_eval] at h
    refine PFun.fixInduction' h ?_ ?_
    · intro v h
      obtain ⟨u,hu,he⟩ := (Part.mem_map_iff _).mp h
      by_cases hz : u.headI=0
      · rw [ite_eq_left hz] at he
        have he' : u.tail=w := Sum.inl.inj he
        subst w
        obtain ⟨t,ht⟩ := ih hu
        exact ⟨_, .fixDone ht hz⟩
      · rw [ite_eq_right hz] at he
        cases he
    · intro v u _ h hr
      obtain ⟨z,hz,he⟩ := (Part.mem_map_iff _).mp h
      by_cases hh : z.headI=0
      · rw [ite_eq_left hh] at he
        cases he
      · rw [ite_eq_right hh] at he
        have he' : z.tail=u := Sum.inr.inj he
        cases z with
        | nil => simp at hh
        | cons a z =>
          cases a with
          | zero => simp at hh
          | succ a =>
            simp only [List.tail_cons] at he'
            subst u
            obtain ⟨t,ht⟩ := ih hz
            obtain ⟨t',ht'⟩ := hr
            exact ⟨_, .fixMore ht ht'⟩

open Turing.PartrecToTM2 Turing.ToPartrec

lemma trPosNum_length_le (n : PosNum) : (trPosNum n).length≤(n:ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih =>
    have hp : 0<(n:ℕ) := PosNum.to_nat_pos n
    simp only [trPosNum,List.length_cons,PosNum.cast_bit0] at *
    omega
  | bit1 n ih =>
    simp only [trPosNum,List.length_cons,PosNum.cast_bit1] at *
    omega

lemma trNum_length_le (n : Num) : (trNum n).length≤(n:ℕ) := by
  cases n with
  | zero => rfl
  | pos n => exact trPosNum_length_le n

lemma trNat_length_le (n : ℕ) : (trNat n).length≤n := by
  have h := trNum_length_le (n:Num)
  simpa only [trNat,Num.to_of_nat] using h

def magnitude (v : List ℕ) : ℕ := (v.map (·+1)).sum

@[simp] lemma magnitude_nil : magnitude []=0 := rfl
@[simp] lemma magnitude_cons (a : ℕ) (v : List ℕ) : magnitude (a::v)=a+1+magnitude v := rfl
lemma magnitude_head (v : List ℕ) : v.headI≤ magnitude v := by
  cases v <;> simp only [List.headI_nil,List.headI_cons,magnitude_nil,magnitude_cons,Nat.default_eq_zero] <;> omega
lemma magnitude_tail (v : List ℕ) : magnitude v.tail≤ magnitude v := by
  cases v <;> simp [magnitude]
lemma magnitude_drop (n : ℕ) (v : List ℕ) : magnitude (v.drop n) ≤ magnitude v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [← List.tail_drop]
    exact (magnitude_tail _).trans ih
lemma bitsize_le_magnitude (v : List ℕ) : bitsize v≤ magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    have ha := trNat_length_le a
    simp only [bitsize,trList,List.length_append,List.length_cons] at *
    simp only [magnitude_cons]
    omega
lemma magnitude_length (v : List ℕ) : v.length≤ magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.length_cons,magnitude_cons]; omega

def Runs (c : Code) (v w : List ℕ) (bound : ℕ) : Prop :=
  ∃t, t≤bound ∧ CodeRun c v w t

lemma Runs.mono {c v w b b'} (h : Runs c v w b) (hb : b≤b') : Runs c v w b' := by
  obtain ⟨t,ht,hc⟩ := h
  exact ⟨t,ht.trans hb,hc⟩
lemma Runs.sound {c v w b} (h : Runs c v w b) : w∈c.eval v := by
  obtain ⟨_,_,hc⟩ := h; exact hc.sound
lemma run_zero (v : List ℕ) : Runs .zero' v (0::v) 1 := ⟨_,le_rfl,.zero v⟩
lemma run_succ (v : List ℕ) : Runs .succ v [v.headI+1] (32*(magnitude v+1)) :=
  ⟨_,by gcongr; exact bitsize_le_magnitude v,.succ v⟩
lemma run_tail (v : List ℕ) : Runs .tail v v.tail (32*(magnitude v+1)) :=
  ⟨_,by gcongr; exact bitsize_le_magnitude v,.tail v⟩
lemma run_comp {f g v u w b b'} (h : Runs g v u b) (h' : Runs f u w b') :
    Runs (.comp f g) v w (b+b'+1) := by
  obtain ⟨t,ht,hc⟩ := h
  obtain ⟨t',ht',hc'⟩ := h'
  exact ⟨_,by omega,.comp hc hc'⟩
lemma run_cons {f fs v u w b b'} (h : Runs f v u b) (h' : Runs fs v w b') :
    Runs (.cons f fs) v (u.headI::w) (b+b'+32*(magnitude v+magnitude u+1)) := by
  obtain ⟨t,ht,hc⟩ := h
  obtain ⟨t',ht',hc'⟩ := h'
  refine ⟨_,?_,.cons hc hc'⟩
  have := bitsize_le_magnitude v
  have := bitsize_le_magnitude u
  omega

lemma run_id (v : List ℕ) : Runs .id v v (70*(magnitude v+1)) := by
  have h : Runs .id v v (1+32*(magnitude (0::v)+1)+1) := run_comp (run_zero v) (run_tail (0::v))
  apply h.mono
  simp only [magnitude_cons]; omega
lemma run_nil (v : List ℕ) : Runs .nil v [] (140*(magnitude v+1)) := by
  have h : Runs .nil v [] (32*(magnitude v+1)+32*(magnitude [v.headI+1]+1)+1) :=
    run_comp (run_succ v) (run_tail [v.headI+1])
  apply h.mono
  have := magnitude_head v
  simp only [magnitude_cons,magnitude_nil]
  omega
lemma run_head (v : List ℕ) : Runs .head v [v.headI] (300*(magnitude v+1)) := by
  have h := run_cons (run_id v) (run_nil v)
  apply h.mono
  omega
lemma run_const_zero (v : List ℕ) : Runs .zero v [0] (210*(magnitude v+1)) := by
  have h := run_cons (run_zero v) (run_nil v)
  apply h.mono
  simp only [magnitude_cons]; omega

open Turing.ToPartrec

lemma run_caseZero {f g : Code} {v w : List ℕ} {b : ℕ} (hz : v.headI=0)
    (h : Runs f v.tail w b) : Runs (.case f g) v w (b+32*(magnitude v+1)) := by
  obtain ⟨t,ht,hc⟩ := h
  exact ⟨_,by have := bitsize_le_magnitude v; omega,.caseZero hz hc⟩
lemma run_caseSucc {f g : Code} {v w : List ℕ} {a b : ℕ}
    (h : Runs g (a::v) w b) :
    Runs (.case f g) ((a+1)::v) w (b+32*(magnitude ((a+1)::v)+1)) := by
  obtain ⟨t,ht,hc⟩ := h
  exact ⟨_,by have := bitsize_le_magnitude ((a+1)::v); omega,.caseSucc hc⟩
lemma run_pred (v : List ℕ) : Runs .pred v [v.headI-1] (332*(magnitude v+1)) := by
  cases v with
  | nil =>
    apply (run_caseZero (g:=.head) rfl (run_const_zero [])).mono
    simp only [magnitude_nil]; omega
  | cons a v =>
    cases a with
    | zero =>
      apply (run_caseZero (g:=.head) rfl (run_const_zero v)).mono
      simp only [magnitude_cons]; omega
    | succ a =>
      apply (run_caseSucc (f:=.zero) (run_head (a::v))).mono
      simp only [magnitude_cons]; omega

def dropCode : ℕ → Code
  | 0 => .id
  | n+1 => .comp .tail (dropCode n)

lemma run_drop (n : ℕ) (v : List ℕ) :
    Runs (dropCode n) v (v.drop n) ((71+33*n)*(magnitude v+1)) := by
  induction n with
  | zero => exact (run_id v).mono (by omega)
  | succ n ih =>
    have hb : magnitude (v.drop n)≤ magnitude v := magnitude_drop n v
    have h := run_comp ih (run_tail (v.drop n))
    rw [List.tail_drop] at h
    apply h.mono
    have hm : 32*(magnitude (v.drop n)+1)≤32*(magnitude v+1) := by omega
    nlinarith

def atCode (n : ℕ) : Code := .comp .head (dropCode n)
lemma run_at (n : ℕ) (v : List ℕ) :
    Runs (atCode n) v [(v.drop n).headI] ((372+33*n)*(magnitude v+1)) := by
  have hb : magnitude (v.drop n)≤ magnitude v := magnitude_drop n v
  apply (run_comp (run_drop n v) (run_head (v.drop n))).mono
  have : 300*(magnitude (v.drop n)+1)≤300*(magnitude v+1) := by omega
  nlinarith

def constCode : ℕ → Code
  | 0 => .zero
  | n+1 => .comp .succ (constCode n)

lemma run_const (n : ℕ) (v : List ℕ) :
    Runs (constCode n) v [n] ((250*(n+1)^2)*(magnitude v+1)) := by
  induction n with
  | zero => exact (run_const_zero v).mono (by nlinarith)
  | succ n ih =>
    have h := run_comp ih (run_succ [n])
    apply h.mono
    simp only [magnitude_cons,magnitude_nil]
    nlinarith

lemma run_fix_bounded {body : Code} {state : ℕ → List ℕ} {out : List ℕ}
    (n M B : ℕ)
    (hsize : ∀i≤n,magnitude (state i)≤M)
    (hstep : ∀i<n,Runs body (state i) (1::state (i+1)) B)
    (hdone : Runs body (state n) (0::out) B) :
    Runs (.fix body) (state 0) out ((n+1)*(B+32*(M+3))) := by
  have aux : ∀m i, i+m=n → Runs (.fix body) (state i) out ((m+1)*(B+32*(M+3))) := by
    intro m
    induction m with
    | zero =>
      intro i hi
      have he : i=n := by omega
      subst i
      obtain ⟨t,ht,hc⟩ := hdone
      exact ⟨_,by omega,.fixDone hc rfl⟩
    | succ m ih =>
      intro i hi
      obtain ⟨t,ht,hc⟩ := hstep i (by omega)
      obtain ⟨t',ht',hc'⟩ := ih (i+1) (by omega)
      refine ⟨_,?_,CodeRun.fixMore (a:=0) hc hc'⟩
      have hs := bitsize_le_magnitude (1::state (i+1))
      have hm := hsize (i+1) (by omega)
      simp only [magnitude_cons] at hs
      have hb : 32*(bitsize (1::state (i+1))+1)≤32*(M+3) := by omega
      nlinarith
  exact aux n 0 (by omega)

open Turing.ToPartrec

def dynamicDropBody : Code :=
  .case .zero' (.cons (.comp .succ .zero) (.cons .head (.comp .tail .tail)))
def dynamicDrop : Code := .fix dynamicDropBody

lemma run_dynamicDropBody_zero (v : List ℕ) :
    Runs dynamicDropBody (0::v) (0::v) (2000*(magnitude (0::v)+1)) := by
  exact (run_caseZero rfl (run_zero v)).mono (by omega)

lemma run_dynamicDropBody_succ (n : ℕ) (v : List ℕ) :
    Runs dynamicDropBody ((n+1)::v) (1::n::v.tail)
      (2000*(magnitude ((n+1)::v)+1)) := by
  have h1 := run_comp (run_const_zero (n::v)) (run_succ [0])
  have ht := run_comp (run_tail (n::v)) (run_tail v)
  have hh := run_caseSucc (f:=.zero') (run_cons h1 (run_cons (run_head (n::v)) ht))
  apply hh.mono
  have hv := magnitude_tail v
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  omega

lemma run_dynamicDrop (n : ℕ) (v : List ℕ) :
    Runs dynamicDrop (n::v) (v.drop n)
      ((n+1)*2100*(magnitude (n::v)+1)) := by
  induction n generalizing v with
  | zero =>
    obtain ⟨t,ht,hc⟩ := run_dynamicDropBody_zero v
    exact ⟨_,by simp only [magnitude_cons] at *; omega,.fixDone hc rfl⟩
  | succ n ih =>
    obtain ⟨t,ht,hc⟩ := run_dynamicDropBody_succ n v
    obtain ⟨t',ht',hc'⟩ := ih v.tail
    have he : v.tail.drop n=v.drop (n+1) := List.drop_tail ..
    rw [he] at hc'
    refine ⟨_,?_,CodeRun.fixMore (a:=0) hc hc'⟩
    have hs := bitsize_le_magnitude (1::n::v.tail)
    have hv := magnitude_tail v
    simp only [magnitude_cons] at *
    have hm : (n+1)*2100*(n+1+magnitude v.tail+1)≤
      (n+1)*2100*((n+1)+1+magnitude v+1) := by gcongr; omega
    nlinarith

def dynamicAt : Code := .comp .head dynamicDrop
lemma run_dynamicAt (n : ℕ) (v : List ℕ) :
    Runs dynamicAt (n::v) [(v.drop n).headI]
      ((n+1)*2500*(magnitude (n::v)+1)) := by
  have h := run_comp (run_dynamicDrop n v) (run_head (v.drop n))
  apply h.mono
  have hv := magnitude_drop n v
  simp only [magnitude_cons]
  nlinarith

open Turing.ToPartrec

def precBody (g : Code) : Code :=
  .cons .tail <| .cons .succ <| .cons (.comp .pred .tail) <|
    .cons (.comp g (.cons .id (.comp .tail .tail))) (.comp .tail (.comp .tail .tail))

lemma run_precBody (g : Code) (a b r r' : ℕ) (v : List ℕ) (M B : ℕ)
    (ha : a≤M) (hb : b≤M) (hr : r≤M) (hr' : r'≤M) (hv : magnitude v≤M)
    (hg : Runs g (a::r::v) [r'] B) :
    Runs (precBody g) (a::b::r::v) (b::(a+1)::(b-1)::r'::v) (B+10000*(M+1)) := by
  have htail := run_tail (a::b::r::v)
  have htt := run_comp htail (run_tail (b::r::v))
  have httt := run_comp htt (run_tail (r::v))
  have hargs := run_cons (run_id (a::b::r::v)) htt
  have hg' := run_comp hargs hg
  have hp := run_comp htail (run_pred (b::r::v))
  have h := run_cons htail (run_cons (run_succ (a::b::r::v))
    (run_cons hp (run_cons hg' httt)))
  apply h.mono
  simp only [magnitude_cons,magnitude_nil,List.headI_cons,List.tail_cons]
  omega

lemma run_precLoop (g : Code) (n : ℕ) (r : ℕ → ℕ) (v : List ℕ) (M B : ℕ)
    (hn : n+1≤M) (hr : ∀i≤n+1,r i≤M) (hv : magnitude v≤M)
    (hg : ∀i≤n,Runs g (i::r i::v) [r (i+1)] B) (a b : ℕ) (hab : a+b=n) :
    Runs (.fix (precBody g)) (a::b::r a::v) ((n+1)::0::r (n+1)::v)
      ((b+1)*(B+11000*(M+1))) := by
  induction b generalizing a with
  | zero =>
    have han : a=n := by omega
    subst a
    obtain ⟨t,ht,hc⟩ := run_precBody g n 0 (r n) (r (n+1)) v M B
      (by omega) (by omega) (hr n (by omega)) (hr (n+1) le_rfl) hv (hg n le_rfl)
    exact ⟨_,by omega,.fixDone hc rfl⟩
  | succ b ih =>
    obtain ⟨t,ht,hc⟩ := run_precBody g a (b+1) (r a) (r (a+1)) v M B
      (by omega) (by omega) (hr a (by omega)) (hr (a+1) (by omega)) hv (hg a (by omega))
    simp only [Nat.add_sub_cancel] at hc
    obtain ⟨t',ht',hc'⟩ := ih (a+1) (by omega)
    refine ⟨_,?_,CodeRun.fixMore (a:=b) hc hc'⟩
    have hs := bitsize_le_magnitude ((b+1)::(a+1)::b::r (a+1)::v)
    have hm := hr (a+1) (by omega)
    simp only [magnitude_cons] at hs
    have hb : 32*(bitsize ((b+1)::(a+1)::b::r (a+1)::v)+1)≤1000*(M+1) := by omega
    nlinarith

lemma run_prec (f g : Code) (n : ℕ) (r : ℕ → ℕ) (v : List ℕ) (M A B : ℕ)
    (hn : n≤M) (hr : ∀i≤n,r i≤M) (hv : magnitude v≤M)
    (hf : Runs f v [r 0] A) (hg : ∀i<n,Runs g (i::r i::v) [r (i+1)] B) :
    Runs (.prec f g) (n::v) [r n] (A+(n+2)*(B+50000*(M+1))) := by
  let F := Code.case .id (.comp (.comp (.comp .tail .tail) (.fix (precBody g))) .zero')
  have hpre := run_cons (run_head (n::v)) (run_cons (run_comp (run_tail (n::v)) hf) (run_tail (n::v)))
  have hf' : Runs F (n::r 0::v) (r n::v) ((n+1)*(B+15000*(M+1))) := by
    cases n with
    | zero =>
      apply (run_caseZero (g:=.comp (.comp (.comp .tail .tail) (.fix (precBody g))) .zero')
        rfl (run_id (r 0::v))).mono
      have := hr 0 le_rfl
      simp only [magnitude_cons]
      nlinarith
    | succ n =>
      have hloop := run_precLoop g n r v M B hn hr hv (fun i hi => hg i (by omega)) 0 n (by omega)
      have htail := run_comp (run_tail ((n+1)::0::r (n+1)::v)) (run_tail (0::r (n+1)::v))
      have hh := run_caseSucc (f:=.id) (run_comp (run_zero (n::r 0::v)) (run_comp hloop htail))
      apply hh.mono
      have h0 := hr 0 (by omega)
      have hend := hr (n+1) le_rfl
      simp only [magnitude_cons]
      nlinarith
  have h := run_cons (run_comp hpre hf') (run_nil (n::v))
  change Runs (.prec f g) (n::v) [r n] _ at h
  apply h.mono
  have h0 := hr 0 (by omega)
  have hend := hr n le_rfl
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  nlinarith

end MinUncut.Costed

noncomputable section
namespace MinUncut.Costed
open Turing.ToPartrec Polynomial

lemma evalNat_mono (p : Polynomial ℕ) {x y : ℕ} (h : x≤y) : p.eval x≤p.eval y := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  apply Finset.sum_le_sum
  intro i hi
  gcongr

structure PolyProgram (f : List ℕ → List ℕ) where
  code : Code
  bound : Polynomial ℕ
  run : ∀v,Runs code v (f v) (bound.eval (magnitude v))
  size : ∀v,magnitude (f v)≤bound.eval (magnitude v)

namespace PolyProgram
variable {f g : List ℕ → List ℕ}

def id : PolyProgram (fun v=>v) where
  code := .id
  bound := C 70*(X+1)
  run v := by simpa using run_id v
  size v := by simp; omega

def tail : PolyProgram List.tail where
  code := .tail
  bound := C 32*(X+1)
  run v := by simpa using run_tail v
  size v := by have := magnitude_tail v; simp; omega

def head : PolyProgram (fun v=>[v.headI]) where
  code := .head
  bound := C 300*(X+1)
  run v := by simpa using run_head v
  size v := by have := magnitude_head v; simp; omega

def nil : PolyProgram (fun _=>[]) where
  code := .nil
  bound := C 140*(X+1)
  run v := by simpa using run_nil v
  size v := by simp

def zero : PolyProgram (fun v=>0::v) where
  code := .zero'
  bound := X+1
  run v := (run_zero v).mono (by simp)
  size v := by simp; omega

def succ : PolyProgram (fun v=>[v.headI+1]) where
  code := .succ
  bound := C 32*(X+1)
  run v := by simpa using run_succ v
  size v := by have := magnitude_head v; simp; omega

def pred : PolyProgram (fun v=>[v.headI-1]) where
  code := .pred
  bound := C 332*(X+1)
  run v := by simpa using run_pred v
  size v := by have := magnitude_head v; simp; omega

def const (n : ℕ) : PolyProgram (fun _=>[n]) where
  code := constCode n
  bound := C (250*(n+1)^2)*(X+1)
  run v := by simpa using run_const n v
  size v := by simp; nlinarith

def drop (n : ℕ) : PolyProgram (fun v=>v.drop n) where
  code := dropCode n
  bound := C (71+33*n)*(X+1)
  run v := by simpa using run_drop n v
  size v := by have := magnitude_drop n v; simp; nlinarith

def projection (n : ℕ) : PolyProgram (fun v=>[(v.drop n).headI]) where
  code := atCode n
  bound := C (372+33*n)*(X+1)
  run v := by simpa using run_at n v
  size v := by have := magnitude_drop n v; have := magnitude_head (v.drop n); simp; nlinarith

def comp (F : PolyProgram f) (G : PolyProgram g) : PolyProgram (f ∘ g) where
  code := .comp F.code G.code
  bound := G.bound+F.bound.comp G.bound+1
  run v := by
    have hh := run_comp (G.run v) (F.run (g v))
    apply hh.mono
    have hm := evalNat_mono F.bound (G.size v)
    simp only [eval_add,eval_comp,eval_one]
    omega
  size v := by
    have hm := (F.size (g v)).trans (evalNat_mono F.bound (G.size v))
    simpa using (hm.trans (Nat.le_add_left _ _)).trans (Nat.le_add_right _ 1)

def cons (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>(f v).headI::g v) where
  code := .cons F.code G.code
  bound := F.bound+G.bound+C 32*(X+F.bound+1)+1
  run v := by
    apply (run_cons (F.run v) (G.run v)).mono
    have hf := F.size v
    simp only [eval_add,eval_mul,eval_C,eval_X,eval_one]
    omega
  size v := by
    have hh := (magnitude_head (f v)).trans (F.size v)
    have hg := G.size v
    simp only [magnitude_cons,eval_add,eval_mul,eval_C,eval_X,eval_one]
    omega

def ofEq (F : PolyProgram f) (h : ∀v,f v=g v) : PolyProgram g where
  code := F.code
  bound := F.bound
  run v := h v ▸ F.run v
  size v := h v ▸ F.size v

open Turing.ToPartrec Polynomial

variable {f g e : List ℕ → List ℕ}

def branch (E : PolyProgram e) (F : PolyProgram f) (G : PolyProgram g) :
    PolyProgram (fun v=>if (e v).headI=0 then f v else g v) where
  code := .comp (.case F.code (.comp G.code .tail)) (.cons E.code .id)
  bound := E.bound+F.bound+G.bound+C 300*(X+E.bound+1)+1
  run v := by
    have hp := run_cons (E.run v) (run_id v)
    have hs := (magnitude_head (e v)).trans (E.size v)
    by_cases he : (e v).headI=0
    · simp only [ite_eq_left he]
      have hb := run_caseZero (g:=.comp G.code .tail) (v := (e v).headI::v) (by simpa using he) (F.run v)
      have hh := run_comp hp hb
      apply hh.mono
      simp only [eval_add,eval_mul,eval_C,eval_X,eval_one,magnitude_cons]
      have hh := E.size v
      omega
    · simp only [ite_eq_right he]
      obtain ⟨a,ha⟩ := Nat.exists_eq_succ_of_ne_zero he
      have hb := run_caseSucc (f:=F.code) (run_comp (run_tail (a::v)) (G.run v))
      change Runs _ ((a+1)::v) _ _ at hb
      rw [← show (e v).headI=a+1 from ha] at hb
      have hh := run_comp hp hb
      apply hh.mono
      have heq : (e v).headI=a+1 := ha
      simp only [eval_add,eval_mul,eval_C,eval_X,eval_one,magnitude_cons]
      have hh := E.size v
      omega
  size v := by
    have hf := F.size v
    have hg := G.size v
    split_ifs <;> simp only [eval_add,eval_mul,eval_C,eval_X,eval_one] <;> omega

def collect : (fs : List (List ℕ → List ℕ)) → (∀f∈fs,PolyProgram f) →
    (G : PolyProgram g) → PolyProgram (fun v=>fs.map (fun f=>(f v).headI)++g v)
  | [], _, G => G
  | f::fs, H, G =>
    (H f (by simp)).cons (collect fs (fun f hf=>H f (by simp [hf])) G)

def replace (n : ℕ) (E : PolyProgram e) :
    PolyProgram (fun v=>(List.range n).map (fun i=>(v.drop i).headI)++
      (e v).headI::v.drop (n+1)) := by
  let fs := (List.range n).map (fun i (v : List ℕ)=>[(v.drop i).headI])
  let P := collect fs (by
    intro f hf
    let ex := List.mem_map.mp hf
    let i := Classical.choose ex
    have hi : (fun v : List ℕ=>[(v.drop i).headI])=f := (Classical.choose_spec ex).2
    exact hi ▸ projection i) (E.cons (drop (n+1)))
  exact P.ofEq (by intro v; simp [fs,List.map_map])

end PolyProgram
end MinUncut.Costed

end

end OAI
