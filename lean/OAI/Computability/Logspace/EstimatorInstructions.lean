import OAI.Computability.Logspace.EstimatorInterfaces
import OAI.Computability.Logspace.FiniteFieldPrograms
import OAI.Computability.Logspace.SparseRows

namespace OAI

/-!
Instruction encodings and resource parameters for the estimator.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Helix
open Counter Relay Rill Fret Chime Finset

/- Types used by the spine of the system. -/
abbrev ID := ℕ × ℕ × ℕ×ℕ
abbrev ChoiceX:= ℕ × ℕ × Bool
abbrev Scout := ID×ChoiceX
abbrev ClockH := ℕ×ℕ
abbrev Crt := ℕ × ClockH × Scout × ℕ
variable {α} [Wire α]

namespace Age
abbrev MV (a:Crt) := a.2.1.1
abbrev g (a:Crt):=a.2.1.2
abbrev styx (a:Crt):=a.2.2.1
abbrev env (a:Crt):=a.2.2.2
abbrev L (n:ℕ):= n.log2+1
abbrev gap (n j:ℕ):=2^(L n-1-j)
def Brole (i:ℕ):Prop:= i  ≤  5
instance roleD (i:ℕ):Decidable (Brole i):=by unfold Brole; infer_instance

abbrev Period (n i:ℕ):= if Brole i then L n else 1
abbrev slackT (n i j:ℕ):=if Brole i then gap n j else 1
def weight (n i j:ℕ):ℕ:=128*(n+1)-(64-i)*slackT n i j
def act (a:Crt):ℕ := weight (MV a) a.1 (g a)
def due (a:Crt):ℕ:= slackT (MV a) a.1 (g a)
lemma gap_pos (n j): 1 ≤ gap n j:=Nat.one_le_pow _ _ (by omega)
lemma gap_le (n j):gap n j ≤  n+1:=by
    by_cases ht:n=0
    · subst n; simp [gap,L]
    have he:= Nat.log2_self_le ht
    apply le_trans (Nat.pow_le_pow_right Nat.zero_lt_two (show _  ≤  n.log2 by unfold L; omega))
                (le_trans he (by omega))
lemma pace (n i j): 1 ≤  slackT n i j ∧ slackT n i j  ≤  n+1:=by
    unfold slackT; split
    · exact ⟨gap_pos ..,gap_le ..⟩
    omega
lemma weights (n i j):64*(n+1) ≤ weight n i j ∧ weight n i j+(64-i)*slackT n i j=128*(n+1):=by
    have hg:=(pace n i j).2
    have he:(64-i)*slackT n i j ≤  64*(n+1):=Nat.mul_le_mul (by omega) hg
    unfold weight; omega
lemma well (a:Crt):1  ≤  due a∧ due a ≤  act a:= by
   have h:=pace (MV a) a.1 (g a)
   have he := weights (MV a) a.1 (g a)
   exact ⟨h.1,h.2.trans (le_trans (by omega) he.1)⟩

lemma sooner {n a i j k:ℕ} (hi:slackT n a i=slackT n j k) (he:a<j) (hk:j ≤ 64):
    weight n a i+slackT n j k ≤ weight n j k := by
   have h1:=(weights n a i).2
   rw [hi] at h1
   have h2:=(weights n j k).2
   have ht:64-j+1  ≤  64-a:=by omega
   nlinarith [Nat.mul_le_mul_right (slackT n j k) ht]
lemma gap_step {n i:ℕ} (h:i+1<L n):gap n i=2*gap n (i+1):=by
   unfold gap; rw [show L n-1-i=L n-1-(i+1)+1 by omega,pow_succ]; omega
lemma oldpay {n i a b:ℕ} (he:i+1<L n)(ha:Brole a)(hb:Brole b):
    weight n b i+slackT n a (i+1) ≤ weight n a (i+1):=by
    have he1:= (weights n b i).2; have he2:= (weights n a (i+1)).2
    unfold slackT at *; rw [ite_eq_left ha] at *; rw [ite_eq_left hb,gap_step he] at he1
    unfold Brole at *
    have hp:64-a+1 ≤  (64-b)*2:=by omega
    nlinarith [Nat.mul_le_mul_right (gap n (i+1)) hp]
lemma renewal {n i a b m j:ℕ}(he:m+slackT n a i ≤ n):
    weight m b j+slackT n a i  ≤  weight n a i:=by
    have h1:=(weights n a i).2
    have h2:=(weights m b j).2
    have h3:=Nat.mul_le_mul_right (slackT n a i) (show 64-a ≤ 64 by omega)
    omega
lemma endbirth {n i a b:ℕ}(h:i+1=L n)(ha:Brole a)(hb:¬Brole b)(ht:b ≤ 64):
    slackT n a i=1∧ weight n a i+1 ≤ weight n b 0:=by
   have hk:slackT n a i=1:=by unfold slackT gap; rw [ite_eq_left ha,h.symm]; simp
   have hc:slackT n b 0=1:=ite_eq_right hb
   have hp:= sooner (k:=0) (hk.trans hc.symm)
                    (show a<b by unfold Brole at *; omega) ht
   rw [hc] at hp; exact ⟨hk,hp⟩

lemma LB (n:PT α ℕ)(h:Kn n): Kn (fun x a=> L (n x a)):=h.bl
lemma gapK {n i:PT α ℕ}(h:Kn n)(g:Kn i):Kn (fun x a=>gap (n x a) (i x a)):=by
    convert Kn.cap h.succ (Kn.fix 2) (((LB n h).pred).sub g) using 1
    ext x a; exact (min_eq_right (gap_le (n x a) (i x a))).symm
lemma slackK {n i j:PT α ℕ}(h:Kn n)(e:Kn i)(hk:Kn j):Kn (fun x a=>slackT (n x a) (i x a) (j x a)):=
    e.cond_le (Kn.fix 5) (gapK h hk) (Kn.fix _)
lemma actK {v:PT α Crt}(h:Kn v):Kn (fun x a=>act (v x a)) :=
     let n:=h.right.left.left
     let e:=h.left
     (((Kn.fix 128).times n.succ).sub (((Kn.fix 64).sub e).times (slackK n e h.right.left.right)))

def W (q:ℕ):ℕ:= if q=0 then 1 else act (dec q)
def D (q:ℕ):ℕ:= if q=0 then 1 else due (dec q)
lemma WK:Kn (fun (_:Word) (a:ℕ)=> W a):= Kn.identity.cond_eq (Kn.fix _) (Kn.fix _) (actK Kn.unpack)
lemma DK:Kn (fun (_:Word) (a:ℕ)=> D a):= Kn.identity.cond_eq (Kn.fix _) (Kn.fix _)
                       (slackK (Kn.unpack (α:=Crt)).right.left.left (Kn.unpack (α:=Crt)).left
                                           (Kn.unpack (α:=Crt)).right.left.right)
lemma cpos (x:Crt): enc x ≠0:=ne_of_gt (lt_trans Nat.zero_lt_one (cord_fine _ _).2.2)
@[simp] lemma WI (x:Crt): W (enc x)=act x:=by simp [W,cpos]
@[simp] lemma DI (x:Crt): D (enc x)=due x:=by simp [D,cpos]
end Age
end ExactDerandomization.Helix

end

section

namespace ExactDerandomization.Helix
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage

namespace Foil
abbrev kit (p:ℕ)(j:ℕ×ℕ)(q:Scout)(x:ℕ):Crt:=(p,j,q,x)
def aspect (a:ℕ×ℕ) : Kind :=
     if a.1=0 then .chip else if a.1=1 then .slot a.2 else if a.1=2 then .echo true a.2
     else if a.1=3 then .echo false a.2 else .score a.2
def shaped : Kind→ℕ×ℕ
     | .chip=>(0,0)
     | .slot b=>(1,b)
     | .echo true b=>(2,b)
     | .echo false b=>(3,b)
     | .score b=>(4,b)
abbrev dataR (p:Scout):= (p.2.1,p.2.2.1)
def claim (p:Scout):Quest :=
     let z:=p.1
     ⟨z.1,z.2.1,z.2.2.1,z.2.2.2,aspect (dataR p),p.2.2.2⟩
def bitR (p:Quest):Scout:=
     let b:=shaped p.tag
     ((p.i,p.u,p.a,p.t),b.1,b.2,p.main)
def gaze (p:Scout):Peek := ⟨p.1.1,p.1.2.1,
                           if p.2.1=5 then none else some p.2.2.1⟩
def bitV (p:Peek):Scout:=
     ((p.i,p.u,0,0),(if p.ask=none then 5 else 6),p.ask.getD 0,false)
@[simp] lemma recovery (q:Quest): claim (bitR q)=q:=by
     cases q with | mk i u a t s b => cases s <;> first | rfl| (rename_i b' n; cases b'; rfl;rfl)
@[simp] lemma recovered (q:Peek): gaze (bitV q)=q:=by cases q with
                                                    | mk i u k=> cases k <;> rfl

def faceR (p:Scout):Prop:= p.2.1 < 5∧ (p.2.1 ≠ 0∨p.2.2.1=0)
def faceV (p:Scout):Prop:=
    ((p.2.1=5∧p.2.2.1=0)∨p.2.1=6)∧p.1.2.2.1=0∧p.1.2.2.2=0∧p.2.2.2=false
lemma copyR {p:Scout}(h:faceR p):bitR (claim p)=p:=by
     obtain ⟨a,b,c,w⟩:=p
     change b<5∧(b≠0∨c=0) at h
     rcases h with ⟨hp,h⟩; interval_cases b <;> simp [claim,bitR,aspect,shaped] ; grind
lemma copyV {p:Scout}(h:faceV p):bitV (gaze p)=p:=by
     simp only [gaze,bitV]; unfold faceV at h
     split <;> simp_all
     all_goals grind
lemma rightR (q:Quest):faceR (bitR q):=by
     cases h:q.tag
     · simp [faceR,bitR,h,shaped]
     · simp [faceR,bitR,h,shaped]
     · next b i=> cases b <;> simp [faceR,bitR,h,shaped]
     simp [faceR,bitR,h,shaped]
lemma rightV (q:Peek):faceV (bitV q):=by cases h:q.ask <;> simp [faceV,bitV,h]
lemma solely {p:Scout}(h:faceR p):¬ faceV p:=by unfold faceR faceV at *; omega

noncomputable section
variable (w:Wares)
def testR (M L H:ℕ)(q:Scout) : Prop :=
     let p:=claim q
     p.i ≤ L ∧ p.i  ≤ p.u ∧ p.a ≤ p.t ∧ p.u+M ≤ H ∧ p.t+M  ≤ H∧ p.tag.sane w.p p.i p.a
def testV (M L H:ℕ)(q:Scout) : Prop :=
     let p:= gaze q
     p.i  ≤  L∧ p.i  ≤  p.u ∧ p.u+M  ≤ H ∧ match p.ask with | none=>True|some j=>p.i=p.u∧j<w.p.T
def operateR (M:ℕ)(s:Scout):Prop:=
     let q:=claim s
     2*q.a+2*q.u+w.A0*(1+coreR w.p q.i+q.tag.depth w.p+(if q.main then 1 else 0)) < M/8
def operateV (M:ℕ)(s:Scout):Prop:=
     let q:=gaze s
     2*q.i+2*q.u+w.A0*(1+coreR w.p q.i+(match q.ask with| none=>0|some k=>12+6*k)) < M/8

def delta0 (p:Scout):Prop:=p.2.1=2 ∨ p.2.1=3
def redV (p:Scout):Prop:=p.2.1=4∧p.2.2.2=true
def Bob (i m:ℕ) (s:Scout):Prop:= ((1  ≤  i∧i  ≤  4) ∨ (9  ≤  i∧i  ≤  11) ∨ (i=13∧delta0 s))∧operateR w m s
def rowUnit(i m:ℕ)(s:Scout):Prop:= faceR s ∧ (Bob w i m s∨
                (i=12∧delta0 s)∨i=14∨i=15∨(i=16∧redV s))
def vecUnit(i m:ℕ)(s:Scout):Prop:=faceV s ∧ ((i=5∧operateV w m s)∨i=17)
def permit (B n:ℕ)(v:Crt):Prop:=
    let u:=v.2.1.1
    let g:= Age.g v
    let s:= Age.styx v
    let H:=w.ceiling B
    Print.publish n (Age.env v)=true ∧
    u ≤ w.top B ∧ g<Age.Period u v.1 ∧
          (rowUnit w v.1 u s∧testR w u B H s∨vecUnit w v.1 u s∧testV w u B H s)
end
end Foil
end ExactDerandomization.Helix

end

section

namespace ExactDerandomization.Helix
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage
noncomputable section
variable {α β} [Wire α] [Wire β]
def GK (p:PT α Prop) := ∃ f:PT α Bool, Kn f ∧ ∀ x a, f x a=true ↔ p x a
namespace GK
variable {p q:PT α Prop}
lemma orG (h:GK p)(e:GK q):GK (fun x a=> p x a ∨ q x a):=by
    obtain ⟨f,h,ht⟩:=h; obtain ⟨g,k,hg⟩:=e
    exact ⟨_,h.cond (Kn.fix true) k,fun x a=> by dsimp only; rw [← ht,← hg]; cases f x a <;> simp⟩
lemma andG (h:GK p)(e:GK q):GK (fun x a=> p x a ∧ q x a):=by
    obtain ⟨f,h,ht⟩:=h; obtain ⟨g,k,hg⟩:=e
    exact ⟨_, Print.both h k,fun x a=> by simp [ht,hg]⟩
lemma notG (h:GK p):GK (fun x a=>¬p x a):=by
    obtain ⟨f,h,ht⟩:=h; exact ⟨_,Kn.bneg _ h,fun x a=>by dsimp only; rw [← ht]; cases f x a <;> simp⟩
lemma forth {f:PT α Bool}(h:Kn f):GK (fun x a=> f x a=true):=⟨f,h,fun _ _=>Iff.rfl⟩
lemma backG {f:PT α Bool}(h:Kn f):GK (fun x a=> f x a=false):=by
    convert (forth h).notG using 1; ext x a; cases f x a <;> simp
lemma decideK (h:GK p)[∀ x a,Decidable (p x a)] :Kn (fun x a=> decide (p x a)):=by
    obtain ⟨f,h,ht⟩:=h; convert h using 1; ext x a; apply Bool.eq_iff_iff.2; rw [decide_eq_true_eq,ht]
lemma ofdec {p:PT α Prop}[∀ x a,Decidable (p x a)]
    (h:Kn (fun x a=>decide (p x a))):GK p:= ⟨_,h,fun x a=>by simp⟩
variable {f g:PT α ℕ}
lemma eqG (h:Kn f)(e:Kn g):GK (fun x a=> f x a=g x a):=ofdec (h.eq e)
lemma ltG (h:Kn f)(e:Kn g):GK (fun x a=> f x a<g x a):= ofdec (h.lt e)
lemma leG (h:Kn f)(e:Kn g):GK (fun x a=>f x a ≤ g x a):= ofdec (h.le e)
lemma ifG (h:GK p)(e:GK q) {f g: PT α ℕ}(ht:Kn f)(hs:Kn g):
       GK (fun x a=>if f x a=g x a then p x a else q x a):=by
    have he:=eqG ht hs
    convert orG (he.andG h) (he.notG.andG e) using 1
    ext x a; split <;> simp_all
end GK

namespace Foil
open GK
variable {p:PT α Scout}
lemma faceRK (h:Kn p): GK (fun x a=>faceR (p x a)):=
    let c:=h.right.left
    andG (ltG c (Kn.fix _)) ((notG (eqG c (Kn.fix _))).orG (eqG h.right.right.left (Kn.fix _)))
lemma faceVK (h:Kn p): GK (fun x a=> faceV (p x a)):=
    let c:=h.right.left
    let g:=h.left.right.right
    (((eqG c (Kn.fix _)).andG (eqG h.right.right.left (Kn.fix _))).orG (eqG c (Kn.fix _))).andG
       ((eqG g.left (Kn.fix _)).andG ((eqG g.right (Kn.fix _)).andG (backG h.right.right.right)))

variable {t H M:PT α ℕ}(w:Wares)
lemma testRK (h:Kn p)(he:Kn M)(hr:Kn t)(hv:Kn H):GK (fun x a=> testR w (M x a) (t x a) (H x a) (p x a)):=by
   let i:=h.left.left
   let u:=h.left.right.left
   let j:=h.left.right.right.left
   let k:=h.left.right.right.right
   let v:=h.right.left
   let z:=h.right.right.left
   let e:= leG i (j.add (Kn.fix (pad w.p)))
   let f:= andG (eqG i j) (ltG z (Kn.fix w.p.T))
   let E:= ifG e (ifG (e.andG (ltG z (Kn.fix w.p.M))) (ifG f (ifG f f v (Kn.fix 3)) v (Kn.fix 2)) v
                                (Kn.fix 1)) v (Kn.fix 0)
   let R:= (leG i hr).andG ((leG i u).andG ((leG j k).andG ((leG (u.add he) hv).andG
                                                               ((leG (k.add he) hv).andG E))))
   convert R using 1
   ext x a; unfold testR claim aspect
   repeat' first | split | rfl

lemma testVK (h:Kn p)(he:Kn M)(hr:Kn t)(hv:Kn H):GK (fun x a=> testV w (M x a) (t x a) (H x a) (p x a)):=by
   let i:=h.left.left
   let u:=h.left.right.left
   let v:=h.right.left
   let f:= (eqG i u).andG (ltG h.right.right.left (Kn.fix w.p.T))
   have ht:GK (fun (_:Word) (_:α)=>True):=⟨_,Kn.fix true,by simp⟩
   convert (leG i hr).andG ((leG i u).andG ((leG (u.add he) hv).andG (ifG ht f v (Kn.fix 5)))) using 1
   ext x a; unfold testV gaze; split <;> simp_all
lemma coreK {u:PT α ℕ}(h:Kn u):Kn (fun x a=> coreR w.p (u x a)):= (Kn.fix _).times h

lemma heightK (h:Kn p):
    Kn (fun x a=> (claim (p x a)).tag.depth w.p) := by
   let c:=h.right.left
   let v:= h.right.right.left
   unfold claim; dsimp only
   have hu(c i:ℕ): Kn (fun x a=> c+i*(p x a).2.2.1):= (Kn.fix _).add ((Kn.fix _).times v)
   convert c.cond_eq (Kn.fix 0) (Kn.fix 3) (c.cond_eq (Kn.fix 1) (Kn.fix (20+8*w.p.T))
                       (c.cond_eq (Kn.fix 2) (hu 13 6) (c.cond_eq (Kn.fix 3) (hu (16+6*w.p.T) 2) (hu 10 6))))
           using 1
   ext x a; simp only [aspect]
   split
   · next h=> simp [Kind.depth]
   next h0=> split
             · next h=>simp [Kind.depth]
             next h1=> split
                       · next h=>simp [Kind.depth]
                       next h2=> split
                                 · next h=>simp [Kind.depth]
                                 next h=>simp [Kind.depth]

theorem XrankK {u g j h e :PT α ℕ}(hi:Kn u)(hc:Kn g)(hh:Kn j)(ht:Kn h)(hz:Kn e):
     Kn (fun x a=> 2*(j x a)+2*(g x a)+w.A0*(1+coreR w.p (u x a)+h x a+e x a)):=
   let m:Kn (fun (_:Word)(_a:α)=>(2:ℕ)):= Kn.fix 2
   ((m.times hh).add (m.times hc)).add ((Kn.fix _).times ((((Kn.fix 1).add (coreK w hi)).add ht).add hz))
lemma onRK (h:Kn p)(he:Kn M):GK (fun x a=> operateR w (M x a) (p x a)):=
   ltG (XrankK w h.left.left h.left.right.left h.left.right.right.left (heightK w h)
                       (h.right.right.right.cond (Kn.fix _) (Kn.fix _))) (he.div (Kn.fix 8))
lemma onVK (h:Kn p)(he:Kn M):GK (fun x a=> operateV w (M x a) (p x a)):=by
   let i:= h.left.left
   let z:= h.right.left.cond_eq (Kn.fix 5) (Kn.fix 0) ((Kn.fix 12).add ((Kn.fix 6).times h.right.right.left))
   convert ltG (XrankK w i h.left.right.left i z (Kn.fix 0)) (he.div (Kn.fix 8)) using 1
   ext x a; unfold operateV gaze; split <;> simp_all
lemma bobG (h:Kn p)(he:Kn M){u:PT α ℕ}(hz:Kn u):
    GK (fun x a=> rowUnit w (u x a) (M x a) (p x a)):=
    let v:=h.right.left
    let e:= (eqG v (Kn.fix 2)).orG (eqG v (Kn.fix 3))
    let i:=((leG (Kn.fix _) hz).andG (leG hz (Kn.fix _))).orG
               (((leG (Kn.fix _) hz).andG (leG hz (Kn.fix _))).orG ((eqG hz (Kn.fix _)).andG e))
    andG (faceRK h) ((i.andG (onRK w h he)).orG (((eqG hz (Kn.fix _)).andG e).orG
                          ((eqG hz (Kn.fix _)).orG ((eqG hz (Kn.fix _)).orG ((eqG hz (Kn.fix _)).andG
                                    ((eqG v (Kn.fix 4)).andG (forth h.right.right.right)))))))
lemma topK {t:PT α ℕ}(hr:Kn t): Kn (fun x a=> w.top (t x a)):=by
   have h := (Kn.fix w.A0).times ((Kn.fix 1).add (coreK w hr))
   exact (Kn.fix 8).times (((((Kn.fix 4).times hr).add h).add ((Kn.fix (1+w.p.M)).times hr)).add
                                                      ((Kn.fix 2).times hr))
lemma roofK {t:PT α ℕ}(hr:Kn t): Kn (fun x a=> w.ceiling (t x a)):= by
   exact (((topK w hr).add hr).add ((Kn.fix (1+w.p.M)).times hr)).add (Kn.fix 1)
lemma permitted {B n:PT α ℕ} {t:PT α Crt}(hp:Kn t)(hb:Kn B)(hn:Kn n):
    GK (fun x a=> permit w (B x a) (n x a) (t x a)):=by
   let i:=hp.left
   let v:= hp.right
   let u:=v.right.left
   let k:=v.left.left
   exact (forth (Print.pubK hn v.right.right)).andG
          ((leG k (topK w hb)).andG
            ((ltG v.left.right (i.cond_le (Kn.fix 5) (k.bl) (Kn.fix 1))).andG
             (((bobG w u k i).andG (testRK w u k hb (roofK w hb))).orG
               (((faceVK u).andG (((eqG i (Kn.fix 5)).andG (onVK w u k)).orG (eqG i (Kn.fix 17)))).andG
                              (testVK w u k hb (roofK w hb))))))
end Foil
end
end ExactDerandomization.Helix

end

section

namespace ExactDerandomization.Helix
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage
open Foil Age
noncomputable section
variable {q w h:ℕ}(r:Rock q w h)
namespace Moon

/-- Live structure prices and hyperparameters selected before running the program. -/
structure Tags where
    e:ℕ
    A:ℕ
    slope:ℕ
    extra:ℕ
    bonus:ℕ
    payL:ℕ

abbrev M (x:Word):=r.w.top (r.B x)
abbrev planets (x:Word):=128*(M r x+1)
abbrev T (v:Tags)(x):=v.slope*(planets r x+1)+v.extra
lemma Mk {α}[Wire α]:Kn (fun x (_:α)=>M r x):=topK _ r.BKn
lemma TKn (v:Tags){α}[Wire α]:Kn (fun x (_:α)=>T r v x):=
   ((Kn.fix _).times (((Kn.fix 128).times (Mk r).succ).succ)).add (Kn.fix _)
abbrev roof (x) := r.w.ceiling (r.B x)
lemma crowX (x): T r ⟨0,0,0,0,0,0⟩ x=0:=by simp [T]
abbrev WaresCap (x) := Print.pages (r.n x)

abbrev hill0 (x) := M r x+roof r x + r.w.p.M + r.w.p.T + 17 + WaresCap r x
abbrev hill (n:ℕ):Scout:= ((n,n,n,n),n,n,true)
abbrev fillA (n:ℕ):Crt:=(n,(n,n),hill n,n)
def topo (x:Word) := enc (fillA (hill0 r x))

section
variable {α}[Wire α]
lemma hillKn:Kn (fun x (_:α)=>hill0 r x):=by
   have hp:= Print.pagesK (r.nKn (α:=α))
   exact (((((Mk r).add (roofK _ r.BKn)).add (Kn.fix _)).add (Kn.fix _)).add (Kn.fix _)).add hp
lemma maxK : Kn (fun x (_:α)=> topo r x):= by
   have hp:= hillKn r (α:=α)
   have hh:=hp.tuple hp
   have he:=hp.tuple (hp.tuple hh); have hz:=hp.tuple (hp.tuple (Kn.fix true))
   exact Kn.wash.comp (hp.tuple (hh.tuple ((he.tuple hz).tuple hp)))

lemma upclock (c:ℕ):Kn (fun x (_:α)=> (2:ℕ)^(planets r x*c)):=by
    have h:∀ x,r.w.top (r.B x) = r.linE (8*r.w.A0)
                          (8*(4+r.w.A0*lag r.w.p +(1+r.w.p.M)+2)) x:=by
         intro x; unfold Wares.top Wares.tolls Wares.density Rock.linE coreR; ring
    let a:=8*r.w.A0; let b:=8*(4+r.w.A0*lag r.w.p+(1+r.w.p.M)+2)
    have he:∀ x,planets r x*c=r.linE (128*(a+1)*c) (128*b*c) x := by
         intro x; unfold planets M; rw [h]; unfold a b Rock.linE; ring
    simp only [he]; exact r.exprKn ..
lemma stationK (v:Tags): Kn (fun x (_:α)=> (2:ℕ)^(T r v x)):=by
    convert ((upclock r (α:=α) v.slope).times (Kn.fix (2^(v.slope+v.extra)))) using 1
    ext x a
    rw [← pow_add]; congr 1; unfold T; ring
lemma storageK (v:Tags):
    Kn (fun x (_:α)=> (2:ℕ)^charge v.A (planets r x) (T r v x)):=by
    convert ((stationK r v (α:=α)).power v.A).times (upclock r (v.A*v.A)) using 1
    ext x a; rw [← pow_mul,← pow_add]; congr 1; unfold charge; ring
abbrev Candle := (ℕ×Bool)×(ℕ×ℕ)×(ℕ×ℕ)×ℕ
def capAX(v:Tags)(x:Word):Candle:= ((16,true),(roof r x,roof r x),
                      (r.w.ell * M r x,2^(planets r x*v.e)),WaresCap r x)
def wax (v:Tags)(x:Word) :ℕ:= enc (capAX r v x)
lemma waxK(v):Kn (fun x (_:α)=> wax r v x):= by
   have hp:= roofK r.w (r.BKn (α:=α))
   exact Kn.wash.comp ((Kn.fix ((16,true):ℕ×Bool)).tuple ((hp.tuple hp).tuple
                   ((((Kn.fix _).times (Mk r)).tuple (upclock r v.e)).tuple (Print.pagesK r.nKn))))
end
lemma craned (x:Word) (a:ℕ) (he:Print.publish (r.n x) a=true):
   a ≤  hill0 r x:=by
   change decide _=_ at he; obtain ⟨hg,hx⟩:=of_decide_eq_true he
   obtain ⟨s,hA⟩:= Print.fill (dec a) hg
   have h0:=Print.boxbound s; rw [hA,hx] at h0
   exact h0.le.trans (by unfold hill0 WaresCap; omega)

lemma scouttop {v:Crt} (x) (hp:permit r.w (r.B x) (r.n x) v):
   enc v  ≤  topo r x:=by
   obtain ⟨a,⟨m,l⟩,⟨⟨i,u,k,t⟩,b,j,h1⟩,p⟩:=v
   let N:=hill0 r x
   have he:m ≤ M r x:= hp.2.1
   have hG:l<Period m a:= hp.2.2.1
   have hl:l ≤ m:= by
       unfold Period at hG
       split at hG
       · have hx:= Relay.lb_le_inc m; change l<Relay.lb m at hG; omega
       omega
   have hz:p ≤ N:= craned r x p hp.1
   let q:Scout:=((i,u,k,t),b,j,h1)
   have HH:a ≤ N∧ m  ≤  N :=by
       have hx: a ≤ 17:=by
         obtain ⟨⟨_,hj⟩,_⟩|⟨⟨_,hj⟩,_⟩:=hp.2.2.2
         all_goals dsimp only at hj
         · unfold Bob at hj
           change _ ∨ a=12∧ _ ∨ a=14 ∨a=15 ∨a=16∧_ at hj
           grind
         grind
       unfold N hill0; omega
   have hk : i ≤ N ∧ u ≤ N ∧ k ≤ N ∧ t ≤ N∧ b ≤ N∧ j ≤ N:=by
      let L:=roof r x
      rcases hp.2.2.2 with ⟨hs,ht⟩|⟨hs,ht⟩
      · obtain ⟨h1,h2,h3,h4,h5,h6⟩:=ht
        obtain ⟨ha,hb⟩:=hs.1
        change b<5 at ha; change b≠0∨j=0 at hb
        change i ≤ u at h2; change k ≤ t at h3; change u+m ≤ roof r x at h4; change t+m ≤ roof r x at h5
        change (aspect (b,j)).sane r.w.p i k at h6
        unfold N hill0
        interval_cases b <;> simp_all [aspect,Kind.sane] <;> omega
      obtain ⟨hg,hv,hU,ht⟩:=ht
      obtain ⟨ha,hb,hc,hd⟩:=hs.1
      change i ≤ u at hv; change u+m ≤ roof r x at hU; change t=0 at hc; change k=0 at hb; unfold N hill0
      change _∨b=6 at ha
      rcases ha with ha|ha
      · change b=5∧j=0 at ha; omega
      subst b; change i=u ∧ j< r.w.p.T at ht; omega
   obtain ⟨hk,hk1,hk2,hk3,hk4,hk5⟩:=hk
   have hsB:enc q ≤  enc (hill N):=by
      refine bead_mono (bead_mono hk (bead_mono hk1 (bead_mono hk2 hk3)))
                    (bead_mono hk4 (bead_mono hk5 (show enc h1  ≤  enc true from ?_)))
      cases h1 <;> decide
   exact bead_mono HH.1 (bead_mono (bead_mono HH.2 (hl.trans HH.2)) (bead_mono hsB hz))

end Moon
end
end ExactDerandomization.Helix

end

section

namespace ExactDerandomization.Helix
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage
open Foil Age Moon Scheme
noncomputable section
open scoped Classical

namespace Orbit
variable {q w h:ℕ}(r:Rock q w h)

def licensed (x:Word)(v:ℕ):Prop:= v=0 ∨ permit r.w (r.B x) (r.n x) (dec v)∧ enc (dec v:Crt)=v
abbrev post (a o i t:ℕ):ℕ:= bell a (hole o i) t
def opt(q:ℕ):ℕ:= cell (which q)
def posn(q:ℕ):ℕ:= Scheme.inside (which q)
@[simp] lemma optionX(a o i t):opt (post a o i t)=o:=by simp [post,opt,hole,cell]
@[simp] lemma targetX(a o i t):posn (post a o i t)=i:=by simp [post,posn,hole,Scheme.inside]
def omegaQ(o i:ℕ):Prop:= o=0∨ (i=9∧o=3)
def colorQ(o i:ℕ):Prop:= (i=9∧o=4) ∨ (i=14∧o=1)
def taps(i o t:ℕ):Prop:=
       ((i=1∨i=3∨ i=9∨i=14)∧ omegaQ o i ∧ t=0) ∨ colorQ o i

def entitled (v:Tags)(x:Word)(u:ℕ):Prop:=
      let a:= unitK u
      let i:=posn u
      a≠0∧licensed r x a∧u=post a (opt u) i (date u)∧taps (dec a:Crt).1 (opt u) (date u)∧ lb i  ≤  v.e*Age.D a

def paired (v:Tags)(x:Word)(t:History):Prop:=
     let a:= cell t.1
     let z:= t.2
     let i:=Scheme.inside t.1
     t.1=hole a i ∧ if a=0 then i ≤ v.bonus ∧ z  ≤ v.bonus else
         licensed r x a∧ (dec a:Crt).1=12∧ i < r.w.p.K ∧ 1 ≤ z∧ z ≤ At.clim r.w.p
abbrev idx (b:Bool)(i j:ℕ):ℕ:=enc (b,i,j)
def location (b:Bool)(_x:Word)(t:History) := idx b (Scheme.inside t.1) t.2

variable (v:Tags)

open GK
lemma licensedK :GK (licensed r):=by
    have hp := Kn.unpack (α:=Crt)
    exact (eqG Kn.identity (Kn.fix _)).orG ((permitted r.w hp r.BKn r.nKn).andG (eqG (Kn.wash.comp hp) Kn.identity))
lemma entitlementK:GK (entitled r v):= by
    let a:=unitK0
    let j:=tokenK.left
    let Y:=(tokenK.comp j).right
    let o:=cellK.comp Y; let t:= (tokenK.comp Y).right
    let T:=tokenK.right
    let u:=((Kn.unpack (α:=Crt)).comp a).left
    have hl:GK (fun x (b:ℕ)=> licensed r x (unitK b)):=by
       obtain ⟨f,h,hp⟩:= licensedK r; exact ⟨_,h.comp a,fun x b=>hp x (unitK b)⟩
    have hp:=Kn.wash.comp ((Kn.wash.comp (a.tuple (Kn.wash.comp (o.tuple t)))).tuple T)
    have h0 {α} [Wire α] (f:PT α ℕ)(h:Kn f)(i:ℕ):GK (fun x a=> f x a=i):=eqG h (Kn.fix i)
    let A (i):=h0 _ u i; let C (i):=h0 _ o i
    let D:= A 1|>.orG ((A 3).orG ((A 9).orG (A 14)))
    let E:= (C 0).orG ((A 9).andG (C 3))
    let H:= ((A 9).andG (C 4)).orG ((A 14).andG (C 1))
    exact ((eqG a (Kn.fix 0)).notG).andG (hl.andG ((eqG Kn.identity hp).andG
       (((andG D (E.andG (h0 _ T 0))).orG H).andG (leG t.bl ((Kn.fix v.e).times (Age.DK.comp a))))))

lemma pledgeK:GK (paired r v):=by
   have ht:= tokenK.comp (Kn.first (β:=ℕ))
   have hp:=ht.left
   have hz:=Kn.next (α:=ℕ) (β:=ℕ)
   have hl:GK (fun x (a:History)=> licensed r x (cell a.1)):= by
       obtain ⟨f,h,hp'⟩:= licensedK r; exact ⟨_, h.comp hp,fun x b=>hp' x (cell b.1)⟩
   let a:=(leG ht.right (Kn.fix v.bonus)).andG (leG hz (Kn.fix v.bonus))
   have hu:=((Kn.unpack (α:=Crt)).comp hp).left
   let b:= hl.andG ((eqG hu (Kn.fix 12)).andG ((ltG ht.right (Kn.fix r.w.p.K)).andG
                              ((leG (Kn.fix 1) hz).andG (leG hz (Kn.fix (At.clim r.w.p))))))
   exact (eqG Kn.first (Kn.wash.comp ht)).andG (ifG a b hp (Kn.fix 0))

def schedule: Scheme:=
   ⟨⟨_, Age.WK⟩,⟨_, Age.DK⟩,⟨_, GK.decideK (licensedK r)⟩,
     ⟨_, GK.decideK (entitlementK r v)⟩,⟨_, GK.decideK (pledgeK r v)⟩,
     fun b=>⟨location b,Kn.wash.comp ((Kn.fix b).tuple ((tokenK.comp Kn.first).right.tuple Kn.next))⟩,
     ⟨_, storageK r v⟩⟩

lemma licensedW{x a}(he:licensed r x a): Age.W a ≤  planets r x:=by
    rcases he with he|⟨he,hh⟩
    · unfold W; rw [ite_eq_left he]; unfold planets; omega
    rw [←hh,WI]; unfold act weight planets
    have hp : MV (dec a:Crt)  ≤  M r x:= he.2.1
    omega
lemma licensedD{x a}(he:licensed r x a): 1 ≤  Age.D a ∧ Age.D a  ≤ Age.W a:=by
    rcases he with he|⟨he,hh⟩
    · subst a; decide
    rw [← hh,DI,WI]; exact well _
end Orbit
end
end ExactDerandomization.Helix

end

section

namespace ExactDerandomization.Helix
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass
open Foil Age Moon Scheme Orbit
noncomputable section
open scoped Classical
namespace Night
variable {q w h:ℕ}(r:Rock q w h)(v:Tags)
abbrev pigmentA (x:Word) : Rod :=⟨r.n x⟩
abbrev qlim (x:Word):ℕ:= 2^(planets r x*v.e)
abbrev tiny :ℕ := r.w.p.K+At.clim r.w.p+v.bonus
def billQ (x:Word):ℕ :=
    let H:=qlim r v x
    let a:=pigmentA r x
    let P:= hole 32 H
    let q:= enc (H,((a.peak,a.peak),wax r v x))
    P+q+idx true (tiny r v) (tiny r v)
def fRock (x:Word):ℕ :=
    let a:= pigmentA r x
    let z:=Dome.glove (a.F,a.M,a.Q) a.peak
    let b:=bell (topo r x) (billQ r v x) (T r v x)
    b+z
section
variable {α} [Wire α]
lemma billK:Kn (fun x (_:α)=> billQ r v x):=by
   have hp:= upclock r v.e (α:=α)
   have hA:=r.nKn (α:=α)
   have hf := Kn.wash.comp (hp.tuple ((hA.tuple hA).tuple (waxK r v)))
   exact ((Kn.wash.comp ((Kn.fix (α:=α) (32:ℕ)).tuple hp)).add hf).add (Kn.fix _)
lemma fRockK:Kn (fun x (_:α)=>fRock r v x):=by
   have hp:= Kn.wash.comp ((Kn.wash.comp ((maxK r (α:=α)).tuple (billK r v))).tuple (TKn r v))
   have he:=r.nKn (α:=α)
   have hs:= Rod.fFun he
   have hz:= Kn.wash.comp (he.tuple (hs.tuple ((Rod.mFun he).tuple (Rod.qFun he))))
   exact hp.add hz
end

def stageC (x:Word) (P:Cog): Dome:=
    let b:=schedule r v
    let B:=b.based x
    { spec:=b, l:=⟨x,P,⟨fRock r v x,fun t=>charge v.slope (B t).w (B t).t⟩,B⟩,
      peak:=r.n x,slope:=v.slope,H:=T r v x }
def field (x:Word) (P:Cog):Cone.ConeX:= ⟨stageC r v x P,topo r x,v.e⟩
def wick (x:Word)(P:Cog): Harp.Wick:=⟨field r v x P,wax r v x⟩
lemma scenic (x:Word) (P:Cog) (he:2 ≤ v.slope): (stageC r v x P).Shape:=by
   let z:=stageC r v x P
   refine ⟨fun _=>rfl,fun _=>rfl,he,?_,?_,?_⟩
   · intro q ha; change decide _=true; change decide (entitled r v x q)=true at ha
     exact decide_eq_true (of_decide_eq_true ha).2.1
   · intro q i ha; change decide _=true; change decide (paired r v x (q,i))=true at ha
     have he0:=(of_decide_eq_true ha).2
     by_cases hm:cell q=0
     · exact decide_eq_true (Or.inl hm)
     rw [ite_eq_right hm] at he0; exact decide_eq_true he0.1
   intro i hi a ha
   have hh:i ≤  z.peak:= Nat.le_of_lt_succ (mem_range.1 hi)
   obtain ⟨h1,h2,h3⟩:=ha
   apply le_trans (bead_mono hh (bead_mono h1.le (bead_mono h2.le h3.le)))
   change Dome.glove ((pigmentA r x).F,(pigmentA r x).M,(pigmentA r x).Q) (r.n x)  ≤  fRock r v x
   exact Nat.le_add_left ..

lemma topo_hi (x P a) (he:(stageC r v x P).active a):a ≤ topo r x := by
    change decide _=true at he
    obtain h|⟨ht,hq⟩:= of_decide_eq_true he
    · rw [h]; omega
    rw [← hq]; exact scouttop r x ht
lemma dawn (x:Word)(P:Cog)(a:ℕ) (he:licensed r x a)(hk:2 ≤  v.slope):
      (stageC r v x P).Suite a:=by
    let q:=stageC r v x P
    refine ⟨scenic r v x P hk,decide_eq_true he,?_,licensedD r he⟩
    change 0+ v.slope*Age.W a ≤  T r v x
    unfold T; nlinarith [Nat.mul_le_mul_left v.slope (licensedW r he)]

lemma cap_time (x P a t) (he:t  ≤  (stageC r v x P).high a):
     t  ≤  T r v x:=he.trans (Nat.sub_le ..)
lemma Orchestra (x P a i) (h:(stageC r v x P).active a)
    (he: lb i ≤  v.e*Age.D a): i  ≤  qlim r v x:=by
   change decide _=true at h
   apply (below i).le.trans
   unfold qlim; apply Nat.pow_le_pow_right (by omega)
   exact he.trans (by rw [mul_comm v.e]; refine Nat.mul_le_mul_right _ ?_
                      exact (licensedD r (of_decide_eq_true h)).2.trans (licensedW r (of_decide_eq_true h)))

lemma town (x a b z:ℕ)(h:a ≤ x) (hf:b ≤ z):hole a b ≤ hole x z:=bead_mono h hf
lemma launch (x P a c t) (he:(stageC r v x P).active a)(hb:c ≤ billQ r v x)(hh:t ≤ (stageC r v x P).high a):
    bell a c t  ≤  (stageC r v x P).F.limit:=by
    apply le_trans (town _ _ _ _ (town _ _ _ _ (topo_hi r v x P a he) hb) (cap_time r v x P a t hh))
    change bell (topo r x) (billQ r v x) (T r v x)  ≤  fRock r v x; exact Nat.le_add_right ..
lemma localC(x P a o i t)(hq:(stageC r v x P).active a)(h:lb i  ≤  v.e*Age.D a)
     (ho:o  ≤  32)(he:t ≤ (stageC r v x P).high a):
    post a o i t  ≤  (stageC r v x P).F.limit:=by
   apply launch _ _ _ _ _ _ _ hq _ he
   unfold billQ; dsimp only
   have hp:= Orchestra r v x P a i hq h
   exact le_trans (town _ _ _ _ ho hp) (by omega)
lemma chask (x P a i b) (hq:(stageC r v x P).active a)(h:lb i  ≤  v.e*Age.D a)
     (he: (wick r v x P).Ok b):Harp.quoteQ a i b  ≤  (stageC r v x P).F.limit:=by
   obtain ⟨h1,h2,h3⟩:=he
   apply launch r v _ P a _ _ hq _ (Nat.zero_le _)
   have ht:= Orchestra r v x P a i hq h
   let K:=pigmentA r x
   have hz: enc (i,b) ≤ enc (qlim r v x,(K.peak,K.peak),wax r v x):=
                          bead_mono ht (bead_mono (bead_mono h2 h3) h1)
   apply hz.trans; unfold billQ; dsimp only [K]; omega
lemma pairbill (x P i j) (h:(stageC r v x P).dual i j)(b:Bool): (stageC r v x P).pulseQ i j b  ≤
                (stageC r v x P).F.limit:=by
   change decide _=true at h
   have hp: paired r v x (i,j):= of_decide_eq_true h
   let q:=stageC r v x P; change bell _ (idx b (Scheme.inside i) j) _  ≤  _
   obtain hh : licensed r x (cell i) ∧ Scheme.inside i  ≤  tiny r v ∧ j ≤ tiny r v:=by
       have hu:=hp.2; dsimp only at hu
       unfold tiny; split at hu
       · next hx=> exact ⟨Or.inl hx,by omega,by omega⟩
       obtain ⟨he,ht,h0,h1,h2⟩:=hu; exact ⟨he,by omega,by omega⟩
   apply launch r v _ P (cell i) _ 0 (decide_eq_true hh.1) _ (Nat.zero_le _)
   have hv : idx b (Scheme.inside i) j  ≤  idx true (tiny r v) (tiny r v):=
                         bead_mono (show enc b ≤ enc true by cases b <;> decide)
                                       (bead_mono hh.2.1 hh.2.2)
   unfold billQ; dsimp only; omega
end Night
end
end ExactDerandomization.Helix

end

section

namespace ExactDerandomization.Helix
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Foil Age Moon Night
open Glass.Rod
noncomputable section

namespace Torch
variable {q w h:ℕ}(r:Rock q w h)(v:Tags)
abbrev innate : Mode → ℕ
   | .push=>0
   | .step2=>1
   | .ret=>2
   | .dial=>3
abbrev denote(i:ℕ):Mode:= if i=0 then .push else if i=1 then .step2 else if i=2 then .ret else .dial
abbrev Part:=(Candle×ℕ)× Pane

def ray (x:Word) (a:Part):Bool × Pane:=
   let ((m,b),(k,j),(L,n),s):=a.1.1
   let t:=a.1.2
   if m<4 then (false, pigment (pigmentA r x) (denote m) b t a.2)
   else
    let v: Issue:=dec s
    if m=4 then (Print.shoot (r.n x) j t v.2.1,a.2)
    else (Print.touched false (r.n x) k j t L n v,a.2)
lemma decorK :Kn (ray r):= by
   have hp:=Kn.first (α:=Candle×ℕ) (β:=Pane)
   have hz:= hp.left; have hh:= hp.right
   have hm:= (r.nKn (α:=Part))
   have he: Kn (fun (_:Word) (a:Part)=> a.2):=Kn.next
   let f(M:Mode)(b:Bool) (x:Word)(a:Part):Pane:= pigment (pigmentA r x) M b a.1.2 a.2
   have hx (M b):Kn (f M b):=by
      cases M
      · exact Rod.firstK _ hm hh he
      · exact Rod.secondK _ hm hh he
      · exact Rod.svK _ hm hh he
      exact Rod.upzK _ hm hh he
   let g(M) (x:Word)(a:Part):Pane:= f M a.1.1.1.2 x a
   have hg (M):Kn (g M):=by
      convert (hz.left.right).cond (hx M true) (hx M false) using 1
      funext x a; unfold g; split
      · next h=>rw [h]
      next h=> have he:a.1.1.1.2=false:=by grind
               rw [he]
   let u:=hz.left.left
   have hs:Kn (fun x (a:Part)=>g (denote a.1.1.1.1) x a):=by
      convert u.cond_eq (Kn.fix 0) (hg Mode.push)
           (u.cond_eq (Kn.fix 1) (hg Mode.step2)
                  (u.cond_eq (Kn.fix 2) (hg Mode.ret) (hg Mode.dial))) using 1
      funext x a; unfold denote; split <;> first|rfl | (split <;> first | rfl| (split <;> rfl))
   let e:= hz.right.left; let d:= hz.right.right.left
   have hb:=(Kn.unpack (α:=Issue)).comp hz.right.right.right
   exact u.cond_lt (Kn.fix _) ((Kn.fix _).tuple hs)
           (u.cond_eq (Kn.fix _) ((Print.shootK hm e.right hh hb.right.left).tuple he)
                 ((Print.touchedK false hm e.left e.right hh d.left d.right hb).tuple he))
def lamp (x:Word)(a:Pr):Bool ×Pane:= ray r x ((dec a.1.1,a.1.2),a.2)
lemma lampK : Kn (lamp r):= (decorK r).comp (((Kn.unpack.comp Kn.first.left).tuple Kn.first.right).tuple Kn.next)
def harp (p:Cone):Harp:=⟨p,Orbit.schedule r v,⟨_,r.nKn⟩,⟨_,lampK r⟩⟩

lemma tints (x:Word)(a:Part)(he:(pigmentA r x).proper a.2): (pigmentA r x).proper (ray r x a).2:=by
    rcases a with ⟨⟨⟨⟨m,b⟩,⟨k,j⟩,⟨L,n⟩,s⟩,i⟩, t⟩
    simp only [ray]
    by_cases h:m<4
    · simp only [ite_eq_left h]
      have ht := (pigmentA r x).stay b i he
      cases denote m
      · exact ht.1
      · exact ht.2.1
      · exact ht.2.2.1
      exact ht.2.2.2
    rw [ite_eq_right h]
    split <;> exact he
lemma life (x:Word)(P:Cog)(p:Cone)(he:2  ≤  v.slope):Harp.Wick.Life (harp r v p) (wick r v x P) := by
   refine ⟨scenic _ _ _ _ he,rfl,rfl,fun q h u _ a z=>?_⟩
   exact tints r x ((dec q.2,ray0 (r.n x) q.1 u),a) z

abbrev charm(m:Mode)(b:Bool): Candle := ((innate m,b),(0,0),(0,0),0)
abbrev trail(j s:ℕ):Candle:=((4,false),(0,j),(0,0),s)
abbrev measureL(k j H i s:ℕ): Candle:=((5,false),(k,j),(H,i),s)
abbrev waxy(p:Candle):NoteM:=((1,0),enc p)
lemma housed(x:Word){a:Candle} (h:a.1.1 ≤  16)(ha:a.2.1.1  ≤  roof r x)(hk:a.2.1.2 ≤ roof r x)
   (hu:a.2.2.1.1 ≤ r.w.ell*M r x)(hz:a.2.2.1.2  ≤ 2^(planets r x*v.e))(hh:a.2.2.2  ≤ WaresCap r x):
    enc a ≤ wax r v x:=by
   exact bead_mono (bead_mono h (show enc a.1.2 ≤ enc true from by cases b:a.1.2 <;> decide)) (bead_mono (bead_mono ha hk)
                                                  (bead_mono (bead_mono hu hz) hh))
lemma litwax (x:Word)(p:Cone)(f:Candle)(b i)(he:i ≤ r.n x):
    (harp r v p).lit x (waxy f) i b=ray r x ((f,i),b):=by
    simp only [harp,Harp.lit,Harp.port,ray0,lamp]; simp [he]
lemma litmode (x i b m f) :
    ray r x ((charm m b,i),f)= (false,pigment (pigmentA r x) m b i f):=by
    cases m<;>rfl

end Torch
end
end ExactDerandomization.Helix

end

section

namespace ExactDerandomization.Helix.Was
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass
open Foil Age Moon Scheme Orbit Night

noncomputable section
open scoped Classical
variable {q w h:ℕ}(r:Rock q w h)

def air (x:Word)(i j:ℕ):Prop:=0<r.P.edge x i j
lemma atm (x i j):air r x i j↔0 < r.P.S x i j:=by
    unfold air Base.Source.S; norm_num
lemma birth (x i j)(h:air r x i j): i ∈ r.P.dom x ∧ j∈r.P.dom x:= by
    have hp(b)(e:r.P.next x i b=some j):i∈r.P.dom x ∧ j∈r.P.dom x:=
              ⟨r.P.mem (r.P.steps_to e).1,r.P.mem (r.P.steps_to e).2.2.1⟩
    rcases r.P.S_pos.1 ((atm r ..).1 h) with he|he <;> exact hp _ he

def moon0 (x:Word)(b:Bool)(i j:ℕ):Prop:= if b then air r x i j else air r x j i
def bin0 (x:Word) (b:Bool) (i j:ℕ) :Finset ℕ:= (range j).filter (moon0 r x b i)
abbrev bright (x:Word)(b:Bool)(i j:ℕ):= (bin0 r x b i j).card
lemma lower0(x b i j k)(hj:j<k)(hi:moon0 r x b i j):bright r x b i j < bright r x b i k:= by
   apply card_lt_card
   rw [Finset.ssubset_iff_subset_ne]
   refine ⟨by unfold bin0; gcongr,fun hn=>?_⟩
   have hp:j∈bin0 r x b i k:=mem_filter.2 ⟨mem_range.2 hj,hi⟩
   rw [← hn] at hp
   exact lt_irrefl _ (mem_range.1 (mem_filter.1 hp).1)
lemma equal0 (x b i j k)(hj:moon0 r x b i j)(hk:moon0 r x b i k)(he:bright r x b i j=bright r x b i k):
    j=k:=by
   rcases lt_trichotomy j k with h|h|h
   · have ht:=lower0 r x b i j k h hj; omega
   · exact h
   have ht:=lower0 r x b i k j h hk; omega

abbrev Kpre (_p:Rock q w h):= Fintype.card (Base.R.Hint q w h)
lemma passage(x i j)(he:air r x i j):bright r x true i j < 2 ∧ bright r x false j i < Kpre r:=by
    obtain ⟨ha,hb⟩:=birth r x i j he
    refine ⟨lt_of_lt_of_le (lower0 r x true i _ _ (mem_range.1 hb) he) ?_,
               lt_of_lt_of_le (lower0 r x false j _ _ (mem_range.1 ha) he) ?_⟩
    · have hh:bin0 r x true i (r.P.size x)=(r.P.dom x).filter (fun j=>0<r.P.S x i j) := by
           ext j; simp [bin0,moon0,Base.Source.dom,atm]
      unfold bright; rw [hh]; exact r.P.out_degree x i
    have hh:bin0 r x false j (r.P.size x)=(r.P.dom x).filter (fun i=>0<r.P.S x i j):=by
        ext i; simp [bin0,moon0,Base.Source.dom,atm]
    unfold bright; rw [hh]; exact r.P.in_degree x j

abbrev atom(i:ℕ):=hole 0 i
abbrev radixG:=r.w.p.M
abbrev fan(i:ℕ):=3+i
abbrev downX(r:Rock q w h)(i):=fan (i+radixG r)
abbrev avails(x:Word):=range (r.n x+1)

def Flight (x:Word)(i z a b:ℕ):Prop:=
    a  ≤  r.n x ∧ b  ≤  r.n x ∧
    if i=0 then a=b∧ z=0
    else if i=1∨ i=2 then air r x a b∧ i=bright r x true a b+1 ∧ z=bright r x false b a+1
    else
     let M:= r.w.p.M
     z=0∧ if i-3<M then b=radix M a (i-3) else i-3-M < M∧ a=radix M b (i-3-M)
lemma fly_pair {x i z h v a b} (he:Flight r x i z a b)(hz:Flight r x i h a v):b=v∧ z=h:= by
    unfold Flight at he hz
    split at he
    · next hw=> simp only [hw,ite_true] at hz; grind
    next hn=> split at he
              · rename_i hw; simp only [hn,hw,ite_true,ite_false] at hz
                obtain ⟨_,_,hl,hR,hU⟩:=he
                obtain ⟨_,_,hp,hM,hB⟩:=hz
                have hs:=equal0 r x true a b v hl hp (by omega); subst b; exact ⟨rfl,by omega⟩
              next hm=>
                simp only [hn,hm,ite_false] at hz
                let M:=r.w.p.M; have hk : 0<M:=by have hh:=r.w.p.mOK; unfold M; omega
                dsimp only [radix] at *
                by_cases he0:i-3<r.w.p.M
                · simp only [ite_eq_left he0] at *; grind
                simp only [ite_eq_right he0] at *
                obtain ⟨_,_,hA,hB,hE⟩:=he; obtain ⟨_,_,hs,hV,hU⟩:=hz
                unfold M at hk
                constructor <;> nlinarith
lemma fly_one {x i z u v b} (he:Flight r x i z u b)(hz:Flight r x i z v b):u=v:=by
    unfold Flight at he hz; let M:=r.w.p.M
    have hk :0<M:=by have hh:=r.w.p.mOK; unfold M;omega
    split at he
    · next hw=> simp only [hw,ite_true] at hz; grind
    next hn=> split at he
              · rename_i hw; simp only [hn,hw,ite_true,ite_false] at hz
                obtain ⟨_,_,hl,hR,hU⟩:=he; obtain ⟨_,_,hp,hM,hB⟩:=hz
                exact equal0 r x false b u v hl hp (by omega)
              next hm=>
                simp only [hn,hm,ite_false] at hz
                dsimp only [radix] at *
                by_cases he0:i-3<r.w.p.M
                · simp only [ite_eq_left he0] at *
                  obtain ⟨_,_,_,hB⟩:=he; obtain ⟨_,_,_,hU⟩:=hz
                  unfold M at hk; nlinarith
                simp only [ite_eq_right he0] at *; grind

section
variable {α}[Wire α] {i j n a b: PT α ℕ}
lemma edgeK(hi:Kn i)(hj:Kn j):Kn (fun x u=> r.P.edge x (i x u) (j x u)):=fun _ h=>r.P.eWeight (hi h) (hj h)
lemma moonG(v:Bool)(hi:Kn i)(hj:Kn j):GK (fun x u=>moon0 r x v (i x u) (j x u)):=by
    cases v
    · exact GK.ltG (Kn.fix _) (edgeK r hj hi)
    exact GK.ltG (Kn.fix _) (edgeK r hi hj)
lemma brightK (v:Bool)(hi:Kn i)(hj:Kn j):Kn (fun x u=> bright r x v (i x u) (j x u)):=by
   let f:PT (α×ℕ×ℕ) ℕ:=fun x a=> a.2.2+(if moon0 r x v (i x a.1) a.2.1 then 1 else 0)
   have hf:Kn f:=Kn.next.right.add (by
      let k:=GK.decideK (moonG r v (hi.comp (Kn.first (β:=ℕ×ℕ))) Kn.next.left)
      simpa only [decide_eq_true_eq] using k.cond (Kn.fix (1:ℕ)) (Kn.fix 0))
   have hr(x p a): forNat (fun k u=>f x (a,k,u)) 0 p=bright r x v (i x a) p:=by
        induction p with
        | zero=> simp [forNat,bright,bin0]
        | succ p ih=> rw [forNat,ih]; exact (Survey.swing _).symm
   simpa only [hr] using Kn.stroll f _ _ _ hf hj (Kn.fix 0) hj (by
         intro x a j hj; rw [hr]; apply le_trans _ hj
         unfold bright bin0; exact (card_filter_le ..).trans (le_of_eq (card_range _)))
lemma faf(hi:Kn i)(he:Kn n)(hv:Kn a)(hh:Kn b):GK (fun x u=>Flight r x (i x u) (n x u) (a x u) (b x u)):=by
   let k:= hi.sub (Kn.fix 3)
   let M:= (Kn.fix (α:=α) (radixG r))
   let p:= GK.eqG he (Kn.fix 0)
   let h1:= (moonG r true hv hh).andG ((GK.eqG hi (brightK r true hv hh).succ).andG
                                    (GK.eqG he (brightK r false hh hv).succ))
   have h2:GK (fun x u=> if i x u-3 < radixG r then b x u=radix (radixG r) (a x u) (i x u-3)
              else i x u-3-radixG r < radixG r ∧ a x u=radix (radixG r) (b x u) (i x u-3-radixG r)):=by
      let g:= GK.ltG k M
      convert (g.andG (GK.eqG hh (k.add (M.times hv)))).orG
              (g.notG.andG ((GK.ltG (k.sub M) M).andG (GK.eqG hv ((k.sub M).add (M.times hh))))) using 1
      ext x u; dsimp only [radix]; split <;> simp_all
   have hg := (GK.leG hv r.nKn).andG ((GK.leG hh r.nKn).andG (GK.ifG ((GK.eqG hv hh).andG p)
       (GK.ifG h1 (GK.ifG h1 (p.andG h2) hi (Kn.fix 2)) hi (Kn.fix 1)) hi (Kn.fix 0)))
   convert hg using 1
   ext x u; unfold Flight
   simp only [radixG,moon0,ite_true]; split <;> first | rfl| grind
end
end
end ExactDerandomization.Helix.Was

end

section

namespace ExactDerandomization.Helix.Was
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass
open Foil Age Moon Scheme Orbit Night Dome
noncomputable section
open scoped Classical
variable {q w h:ℕ}(r:Rock q w h)(v:Tags)

def map0 (x:Word)(i z:ℕ)(s:Bool)(a b:ℕ):Prop:= if s then Flight r x i z a b else Flight r x i z b a
abbrev Clasp := ((ℕ×ℕ) × Bool)× ℕ
def lastP (x:Word)(t:Clasp)(b:ℕ):Bool:= decide (map0 r x t.1.1.1 t.1.1.2 t.1.2 t.2 b)
def unitN (x:Word)(a:Clasp):ℕ:= Prime.tube (fun x y=>lastP r x y.1 y.2) x a (r.n x+1)
lemma unitKN: Kn (unitN r):= by
    let f:PT (Clasp×ℕ) Prop:=fun x a=>map0 r x a.1.1.1.1 a.1.1.1.2 a.1.1.2 a.1.2 a.2
    have h:Kn (fun x a=>decide (f x a)):= by
       have hp:= (Kn.first (α:=Clasp) (β:=ℕ)).left
       have ht:= hp.left.left
       have hf:= hp.left.right
       have hv1:= Kn.first (α:=Clasp) (β:=ℕ)|>.right
       have he:= (hp.right).cond (GK.decideK (faf r ht hf hv1 Kn.next)) (GK.decideK (faf r ht hf Kn.next hv1))
       convert he using 1
       ext x a; unfold f map0; split <;> rfl
    exact Prime.tubeK h (r.nKn.succ)
abbrev walkq(i j:ℕ)(b:Bool)(a:ℕ):Clasp:=(((i,j),b),a)
def stopped (x:Word)(i:ℕ):Tide:= fun z b a=>
    let t:= unitN r x (walkq i z b a)
    if t=0 then none else some (t-1)

lemma travel(x i z s a b): stopped r x i z s a=some b ↔ map0 r x i z s a b := by
   let f(j):=lastP r x (walkq i z s a) j
   let n:=unitN r x (walkq i z s a)
   have he(j):f j=true↔ map0 r x i z s a j:=by simp [lastP,f]
   have ht(j)(h:n=j+1): f j=true:= (Prime.uniquely h).2
   have hs (h:n=0) : ∀ j<r.n x+1,f j=false:=Prime.unique_small.1 h
   unfold stopped; change (if n=0 then none else some (n-1))=_↔ _
   cases e:n with
   | zero=>
     simp only [ite_true,reduceCtorEq,false_iff]
     intro h
     have hg : b<r.n x+1:=by cases s <;> unfold map0 at h <;> unfold Flight at h <;> simp at h <;> omega
     have hh := hs e b hg
     simp [(he b).2 h] at hh
   | succ j=>
     have ha := (he j).1 (ht j e)
     simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,Option.some.injEq]
     refine ⟨fun ht=>ht ▸ ha,fun hv=>?_⟩
     cases s
     · exact fly_one r ha hv
     exact (fly_pair r ha hv).1

abbrev Cube:= Bool × ℕ× ℕ
def wrapP (x:Word)(p:Plot):Site:=
     let (b,i,z):Cube:= dec (Scheme.which p.1)
     let (q,h):Glass.Foot:=dec p.2.2
     let n:=unitN r x (walkq i z b q)
     if n=0 then (0,p.2.2) else (1,Dome.glove h (n-1))
lemma wrapK:Kn (wrapP r):=by
    have h:= ((((tokenK.comp tokenK.left).right)))
    have hh:= ((Kn.unpack (α:=Cube)).comp h).comp (Kn.first (β:=Site))
    have hp:= (Kn.unpack (α:=Foot)).comp (Kn.next (α:=ℕ) (β:=Site)).right
    let H:=(unitKN r).comp ((hh.right.tuple hh.left).tuple hp.left)
    exact H.cond_eq (Kn.fix _) ((Kn.fix _).tuple Kn.next.right) ((Kn.fix _).tuple
                                                          (Kn.wash.comp (H.pred.tuple hp.right)))
def basic := Cog.edit ⟨_,wrapK r⟩

abbrev packB(b:Bool)(i j:ℕ):ℕ:= bell 0 (idx b i j) 0
lemma decideWay (x i z b a w):
   wrapP r x (packB b i z,0,glove w a)=AtM (stopped r x i z b a) w a:=by
    unfold wrapP stopped; simp only [packB,bellV,idx,glove,dec_round,Dome.AtM]
    split<;> rfl

theorem motion (x:Word)(P:Cog)(Lt:6  ≤  v.slope)
    (hp:∀ b i j a m,Lot.Mane (stageC r v x P).l v.slope ⟨1,0⟩ 1 (packB b i j)
                      (basic r) a m →Lot.Mane (stageC r v x P).l v.slope ⟨1,0⟩ 1 (packB b i j) P a m)
    (i:ℕ):
    (stageC r v x P).Streams (atom i) (stopped r x i):=by
   let u:=stageC r v x P
   have he:=dawn r v x P 0 (Or.inl rfl) (by omega)
   have hC (a:ℕ)(h:a∈u.P)(b:Rod.Pane)(hh:u.r.proper b)(t:ℕ)(ht:t ≤ 1):
                         u.l.state v.slope ⟨1,0⟩ (t,glove b a) := by
      refine ⟨he.shape.account _ h b hh,?_⟩
      unfold span; dsimp only; have hm:lb t  ≤ 1:= lb_mono (y:=1) ht
      nlinarith
   have htop (z b a c)(h:stopped r x i z b a=some c):c∈ u.P:=by
      have he:=(travel r ..).1 h
      apply mem_range.2; cases b <;> simp only [map0,Flight,Bool.false_eq_true,ite_false,ite_true] at he
      · exact Nat.lt_succ_of_le he.1
      exact Nat.lt_succ_of_le he.2.1
   constructor
   · intro z hz a ha b w hw
     have ht:= decideWay r x i z b a w
     have hm : u.l.state v.slope ⟨1,0⟩ (AtM (stopped r x i z b a) w a) := by
        cases he:stopped r x i z b a
        · exact hC a ha w hw 0 (by omega)
        · next e=> exact hC e (htop z b a _ he) w hw 1 le_rfl
     have he0 : u.pulseQ (atom i) z b=packB b i z:=by
            unfold Dome.pulseQ; simp [u,stageC,Dome.s,Scheme.before,schedule,Orbit.location,
                                                packB,cell,Scheme.inside,atom,hole]
     change u.talk (u.pulseQ (atom i) z b) _ _
     rw [he0]
     have hi: Lot.Mane u.l v.slope ⟨1,0⟩ 1 (packB b i z) P (0,glove w a) _ :=
         hp b i z _ _ (Lot.Mane.edit ht (hC _ ha w hw _ (by omega)) hm)
     have hc := Night.pairbill r v x P (atom i) z hz b
     change u.pulseQ (atom i) z b ≤ u.F.limit at hc; rw [he0] at hc
     exact he.hired _ _ hc (by omega) (by change v.slope ≤ v.slope; exact le_rfl) hi
   · intro z _ a _ b w he
     refine ⟨htop _ _ _ _ he,?_⟩
     rw [travel]; rw [travel] at he; cases b <;> exact he
   intro i0 _ z hz j hj a b he hv
   rw [travel] at he hv; exact (fly_pair r he hv).2
end
end ExactDerandomization.Helix.Was

end

section

namespace ExactDerandomization.Helix.Mold
open Counter Relay Rill Fret Chime Finset Grain Net Hie Est Analysis Stage Glass Foil Age Moon Night
open Scheme Orbit Rod Torch
noncomputable section

abbrev Crux:=ℕ×ℕ×Arch

abbrev Aide:=(ℕ×ℕ)×(Bool ×ℕ ×ℕ)× (ℕ × Arch)
abbrev Croft:= Mint.Bean
abbrev lips (g:Crt)(o:ℕ): Crt :=(o,g.2)
abbrev stint(g:Crt)(i m:ℕ):Crt:=(i,(MV g,m),g.2.2)
abbrev pointer (a i:ℕ):ℕ:=enc (lips (dec a) i)
abbrev uphold (a:ℕ):Crt:= dec a
def visitX (_:Word)(a:ℕ):Bool := decide ((uphold a).1=2 ∨ (uphold a).1=4 ∨
                              (uphold a).1=10 ∨ (uphold a).1=11 ∨ (uphold a).1=15)
lemma visitXK : Kn visitX:=by
    let h:= (Kn.unpack (α:=Crt)).left
    unfold visitX uphold
    apply GK.decideK
    let u (i:ℕ):=GK.eqG h (Kn.fix i)
    exact (u 2).orG ((u 4).orG ((u 10).orG ((u 11).orG (u 15))))
abbrev assignT (g:Crt):ℕ := if g.1=11 then 9 else g.1-1
abbrev selop (a:ℕ):ℕ:=if a=11 then 3 else 0
def send (_:Word)(a:Mint.Node):ℕ :=
     let g:= uphold a.1
     post (pointer a.1 (assignT g)) (selop g.1) a.2 0
lemma sendK:Kn send:=by
    let G:= (Kn.unpack (α:=Crt)).comp (Kn.first (β:=ℕ)); let v:=G.left
    let h:= v.cond_eq (Kn.fix 11) (Kn.fix 9) v.pred
    let hp:= v.cond_eq (Kn.fix 11) (Kn.fix 3) (Kn.fix 0)
    have hl:= Kn.wash.comp ((Kn.wash.comp (h.tuple G.right)).tuple (Kn.wash.comp (hp.tuple Kn.next)))
    exact Kn.wash.comp (hl.tuple (Kn.fix _))

def rope (a i:ℕ): Aide := ((Was.atom 0,0),(true,a,i),(Was.atom 0,1,0))
variable {α} [Wire α]
lemma ropeK {f g:PT α ℕ}(h:Kn f)(e:Kn g):Kn (fun x a=> rope (f x a) (g x a)):=
    (Kn.fix _).tuple (((Kn.fix true).tuple (h.tuple e)).tuple (Kn.fix _))
def tailR (g:Crt):ℕ:= enc (stint g 4 (Age.L (Age.MV g)-1))
lemma tailRK {g:PT α Crt}(h:Kn g):Kn (fun x a=> tailR (g x a)):= by
   have hv:=h.right.left.left
   exact Kn.wash.comp ((Kn.fix (4:ℕ)).tuple ((hv.tuple hv.bl.pred).tuple h.right.right))

abbrev Pose:=Cub Croft Aide
def offer (p:Pose)(x:Word)(a:Croft):Aide :=
    let g:= uphold a.1
    let i:= Relay.mark a.2.2
    if g.1=2 then p.f x a else
    if g.1=4 then rope (enc (lips g 2)) i else
    if g.1=15 then rope (enc (lips g 10)) a.2.1 else
           rope (tailR g) i
lemma offerK (p):Kn (offer p):=by
    have hp:= (Kn.unpack (α:=Crt)).comp (Kn.first (β:=History))
    have hf:= cellK.comp (Kn.next (α:=ℕ) (β:=History)).right
    exact hp.left.cond_eq (Kn.fix _) p.runs
        (hp.left.cond_eq (Kn.fix _) (ropeK (Kn.wash.comp ((Kn.fix _).tuple hp.right)) hf)
             (hp.left.cond_eq (Kn.fix _) (ropeK (Kn.wash.comp ((Kn.fix _).tuple hp.right)) Kn.next.left)
                 (ropeK (tailRK hp) hf)))

variable {q w h:ℕ}(r:Rock q w h)(v:Tags)
def flexQ (x:Word)(u:ℕ):ℕ:=min (2^planets r x) (2^Age.D u)
lemma flexK:Kn (flexQ r):=by
    have he:Kn (fun x (_:ℕ)=> (2:ℕ)^planets r x):= by simpa using upclock r (α:=ℕ) 1
    exact Kn.cap he (Kn.fix 2) Age.DK
def coneX (p:Pose) : Cone:=
    let h:=offerK p
    { limit:=⟨_,maxK r⟩, pad:=⟨_,flexK r⟩, spur:=⟨_,sendK⟩, head:=⟨_,h.left.left⟩,
      tail0:=⟨_,h.right.right.left⟩, bud:=⟨_,h.right.left.right.left⟩,
      nest:=⟨_,h.right.left.right.right⟩, splitQ:=⟨_,h.right.left.left⟩,
      tip:=⟨_,h.left.right⟩, ispath0:=⟨_,visitXK⟩,shift:=⟨_,h.right.right.right⟩ }

def knob : Knob:=⟨⟨_,Age.DK⟩,⟨_,flexK r⟩,⟨_,stationK r v⟩⟩

lemma highflex(x)(g)(hx:licensed r x g): flexQ r x g=2^Age.D g :=
   min_eq_right (Nat.pow_le_pow_right Nat.zero_lt_two ((licensedD r hx).2.trans (licensedW r hx)))

abbrev bandD (x:Word)(P:Cog)(u i:ℕ): Fret.Seats:=(stageC r v x P).chord u i u
lemma knows(x P u i) (hq:licensed r x u) (hk:i∈ (stageC r v x P).P)(hs:2 ≤ v.slope):
       (bandD r v x P u i).stable (knob r v):=
   fun b hb=> ⟨(dawn r v x P u hq hs).pit hk u b hb,rfl, highflex r x u hq⟩

structure Stash where
    pave: Pose
    scripted : ℕ → Cog

def codeRank (r:Rock q w h)(v:Tags)(s:Stash)(i:ℕ):Cog:=
   if i=0 then Was.basic r else if i=2 ∨ i=4 ∨ i=10 ∨ i=11 ∨ i=15 then
       (Torch.harp r v (coneX r s.pave)).cueV.play else s.scripted i
def who (a:ℕ):ℕ:= if unitK a=0 then 0 else (uphold (unitK a)).1
lemma whoK : Kn (fun (_:Word)a=>who a):= unitK0.cond_eq (Kn.fix 0) (Kn.fix _)
                   ((Kn.unpack (α:=Crt)).comp unitK0).left
def dust (i:ℕ):Flag:=⟨_,((whoK.comp Kn.first).eq (Kn.fix i))⟩
def visitMain (s:Stash):ℕ → Cog
    | 0=>codeRank r v s 0
    | i+1=> Cog.bif (dust (i+1)) (codeRank r v s (i+1)) (visitMain s i)
abbrev woven (s:Stash):=visitMain r v s 17

variable (s:Stash) {l:Lot}
lemma seated {c b q d a y}(h:Lot.Mane l c b d q (codeRank r v s (who q)) a y){m:ℕ}(he:who q ≤ m):
    Lot.Mane l c b d q (visitMain r v s m) a y:=by
   induction m with
   | zero=> rw [Nat.eq_zero_of_le_zero he] at h; exact h
   | succ m ih=>
     by_cases hf:who q=m+1
     · rw [hf] at h
       exact .yes (show decide (who q=m+1)=true from decide_eq_true hf) h
     exact .no (show decide (who q=m+1)=false by simp [hf]) (ih (by omega))

abbrev unitV (p:Crt):=enc p
lemma sizeR {i:Crt} (x) (ht: licensed r x (unitV i)):i.1 ≤ 17:=by
   rcases ht with h|⟨he,hx⟩
   · exact (Age.cpos i h).elim
   rw [show (dec (unitV i):Crt)=i from Wire.eq _] at he
   obtain ⟨⟨_,hm⟩,_⟩|⟨⟨_,hm⟩,_⟩:=he.2.2.2
   · unfold Bob at hm; grind
   grind

end
end ExactDerandomization.Helix.Mold

end

end OAI
