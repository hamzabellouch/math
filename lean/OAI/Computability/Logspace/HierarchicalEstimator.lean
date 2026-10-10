import OAI.Computability.Logspace.EstimatorOperations
import OAI.Computability.Logspace.ProbabilityHierarchy

namespace OAI

/-!
The hierarchical estimator and its well-founded error induction.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! Analytical estimator over the hierarchy. -/
namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset

variable {n : ℕ} [Fact n.Prime]

structure Scene (n : ℕ) [Fact n.Prime] where
   H : Prize
   N : ℕ
   height : ℕ
   roof : ℕ
   gap : ℕ
   lam : ℕ

namespace Scene
variable (v : Scene n)
def P := v.H.P.p
def frame (i : ℕ) : Prize := v.H.iterate n i
def stage (i : ℕ) : Stg := (v.frame i).P
lemma aligned (i) : (v.stage i).p=v.P := Prize.par ..
def mode (i u a : ℕ) : Axis := ⟨(v.stage i).S,v.N,u,a⟩

/-- Uniform hypotheses supplied for the whole finite stage range. -/
structure SetUp : Prop where
   correct : v.H.Correct
   init : v.H.P.i=0
   radix_small : v.P.M<n
   fuel : 2^v.roof≤n
   count : ∀ i ≤v.height, ((v.stage i).S).card≤v.N
   ids : ∀ i ≤v.height,Hie.legal n (v.stage i).S
   wind : Est.Wind 18 v.lam
lemma phase (h:v.SetUp) (i) : (v.stage i).i=i := by simp [stage,frame,Prize.index,h.init]
lemma rights (h:v.SetUp) (i) : (v.frame i).Correct:=Prize.all n h.correct i
lemma rankok (h:v.SetUp) (i) : Step (v.stage i).S (rate i) (v.stage i).C := by
    have he:= v.phase h i
    have hu := (v.rights h i).step
    change Step (v.stage i).S (v.stage i).f _ at hu; unfold Stg.f at hu; rwa [he] at hu
lemma fits (h:v.SetUp) {i} (hi:i≤v.roof) : 2^i ≤ n :=
    le_trans (Nat.pow_le_pow_right (by omega) hi) h.fuel

end Scene

def pad (p : Const) := p.T+10
lemma stayed (p : Const) (k l : ℕ) (he:l≤k+pad p) :
   rate k/rate l≤box (4*pad p) := by
   rcases le_total l k with hs|hs
   · rw [shrink hs]; calc _ ≤ (1:ℝ)^4 := pow_le_pow_left₀ (dry0 _).le (dry_one _) 4
                          _ ≤ _:=by norm_num; exact box_one _
   · rw [swell hs, ← boxM]; apply box_mono; omega
lemma beyond (p : Const) {k l : ℕ} (h:k+pad p<l) {x}
    (he:x ≤ (p.T+1:ℝ)*rate l) : bin k x=0 := by
   have hs : x/rate k ≤ 1/2 := by
      have hl : 2*(p.T+1:ℝ) ≤ rate k/rate l := by
         rw [swell (by omega)]
         have he0 : (p.T+1:ℝ)≤ box p.T:=box_big _
         have hk : box p.T*box 1≤box (l-k):=by rw [← boxP]; apply box_mono; unfold pad at h; omega
         rw [show box 1=2 from by simp [Est.box]] at hk
         have ha :=box_one (l-k)
         have ha1 : box (l-k) ≤ box (l-k)^4 := by simpa using pow_le_pow_right₀ ha (show 1≤(4:ℕ) by omega)
         linarith
      have ht := (le_div_iff₀ (rate_pos l)).1 hl
      rw [div_le_iff₀ (rate_pos k)]
      linarith
   rw [bin,sw_bot hs]; ring

/-- Echo labels have k as the predecessor iteration number. -/
inductive Kind where
 | chip
 | slot (j:ℕ)
 | echo (b:Bool) (k:ℕ)
 | score (k:ℕ)
 deriving DecidableEq

structure Quest where
   i : ℕ
   u : ℕ
   a : ℕ
   t : ℕ
   tag : Kind
   main : Bool

structure Peek where
    i : ℕ
    u : ℕ
    ask : Option ℕ

namespace Kind

def theta : Kind → ℝ
 | chip => 1/2
 | slot _=>1/2
 | echo _ _=> Hie.A
 | score _=> delta
def depth (p : Const) : Kind → ℕ
 | chip => 3
 | slot _=> 20+8*p.T
 | echo true k=> 13+6*k
 | echo false k=> 16+6*p.T+2*k
 | score k=> 10+6*k

def matrix (n : ℕ) [Fact n.Prime] (p : Stg) : Kind → Mat
 | chip => p.C
 | slot _=> p.D n
 | echo true k=> p.testG n k
 | echo false k=> p.nextG n k
 | score k=>p.testG n k

def piece (p:Const) (k l : ℕ) : Kind → ℝ→ℝ
 | chip => bfrag p k l none
 | slot i=> bfrag p k l (some i)
 | score _=> light
 | echo _ _=> Qc p

def narrow : Kind→Bool
 | echo _ _=>true
 | _ => false
def paired : Kind→Bool
 | score _=>false
 | _=>true

def sane (p : Const) (i a:ℕ) : Kind→ Prop
 | chip=> i≤a+pad p
 | slot j=> i≤a+pad p ∧ j<p.M
 | echo _ k=> i=a∧k<p.T
 | score k=>i=a∧ k<p.T

lemma lowp (k : Kind) : delta ≤ k.theta := by cases k <;> norm_num [theta,delta,A]
lemma highp (k : Kind) : k.theta≤1:=by cases k <;> norm_num [theta,delta,A]
lemma wall (p : Const) (k l) (v : Kind) {x} (h:x≤v.theta) :
    v.piece p k l x=0 := by
   cases v
   · exact bfrag_low _ _ _ _ h
   · exact bfrag_low _ _ _ _ h
   · exact Qc_low h
   · exact rzero _ h

end Kind

def lag (p : Const) := 50+8*p.T
def coreR (p:Const) (i : ℕ) := lag p*i

namespace Quest
variable (p:Quest)

def plan (s : Scene n) := s.mode p.i p.u p.a
def key (s : Scene n) : StepKey :=
    ⟨p.a,p.u, 1+coreR s.P p.i + Kind.depth s.P p.tag + (if p.main then 1 else 0)⟩
def stair (s : Scene n) (M:ℕ) : Stair := ⟨M,s.gap,p.key s,s.lam⟩

def ready (s : Scene n) (M:ℕ) :=
    p.i≤ s.height∧p.i≤p.u∧p.a≤p.t∧p.u+M≤ s.roof∧p.t+M≤ s.roof∧p.tag.sane s.P p.i p.a

def question (s : Scene n) : Ask :=
   ⟨s.P,(s.stage p.i).S,p.tag.matrix n (s.stage p.i),p.u,p.a,p.t,p.tag.theta,p.tag.narrow⟩

def builder (s : Scene n) : Builder (p.plan s) :=
   ⟨s.P,p.t,p.tag.theta,p.tag.narrow⟩

def two := p.main && p.tag.paired
def phi (s : Scene n) : ℝ→ℝ :=
   if p.main then p.tag.piece s.P p.a p.i else prep p.tag.theta
def trio (s:Scene n) : Trio :=
    mainT p.tag.theta (p.phi s) p.two

def steps (s : Scene n) : ℕ :=
   match p.tag with
   | .echo b k=> if b then k+1 else s.P.T
   | _=>0

def damp (s : Scene n) : Vec :=
    if p.main && p.tag.narrow then (s.stage p.i).gm n (p.steps s) else fun _=>1
def guardP (s : Scene n) := fun (_:Pool n)=>p.damp s

/-- true stochastic row represented by the same building blocks. -/
def truth_second (s : Scene n) : Mat :=
   let q:=p.question s
   if p.two then fun i j=> zeta * (q.tooth n i j)
   else fun _ _=>0
def origin (s : Scene n) : Builder.Block n :=
    fun u x=>let q:=p.question s
             ⟨0,fun y=>(q.d x y, if y∈retain p.t (p.plan s).S u.2.1 then
                               p.truth_second s x y else 0)⟩
def need (s : Scene n) := (p.builder s).wrapped (p.origin s) (p.trio s) p.two (p.guardP s)

lemma normal (s : Scene n) {p:Quest} (h:p.two=true) :
    p.need s=bed.pat (p.question s) (p.phi s) (p.damp s) := by
   have he(u i) : p.origin s u i=(p.question s).rawplus u.2.1 i := by
     simp only [origin,Ask.rawplus,Ask.raw,truth_second,h,ite_true]; rfl
   ext u i j
   simp only [need,bed.pat,Builder.wrapped,Ask.atomTrue,trio,h,show p.origin s u=
                   (p.question s).rawplus u.2.1 from funext (he u)]
   rfl

lemma prepared (s : Scene n) {p:Quest} (h:p.main=false) :
    p.need s=bed.bath (p.question s) := by
   have hz : p.two=false := by simp [two,h]
   have he (u i) : p.origin s u i=(p.question s).botRow i := by simp [origin,Ask.botRow,
                     Ask.raw,truth_second,hz]
   ext u i j
   simp only [need,bed.bath,Builder.wrapped,Ask.bath,show p.origin s u=(p.question s).botRow
                              from funext (he u)]
   simp only [trio,phi,h,hz,Bool.false_eq_true,ite_false,guardP,damp,Bool.false_and]
   rfl
lemma wall0 (s:Scene n) {x} (h:x≤p.tag.theta/2) : p.phi s x=0 := by
   have hz :=p.tag.lowp; have he :=dp
   unfold phi; split
   · apply Kind.wall; linarith
   · exact rising_bot (by linarith) h
lemma dammed (s:Scene n) (x) : in01 (p.damp s x) := by
    unfold damp; split; apply gamma_mem; norm_num [in01]

lemma ampl {s : Scene n} {M} (h : p.ready s M) : p.i≤p.a+pad s.P := by
   obtain ⟨-,-,-,-,-,ht⟩:=h
   cases he:p.tag <;> rw [he] at ht <;>
     first | exact ht | exact ht.1 | (obtain rfl':= show p.i=p.a from ht.1; omega)

end Quest

namespace Peek
variable (p : Peek)
def plan (s:Scene n) : Axis := s.mode p.i p.u p.i
def key (s:Scene n) : StepKey := ⟨p.i,p.u,1+coreR s.P p.i+(match p.ask with | none=>0| some k=>12+6*k)⟩
def stair (s:Scene n) (M:ℕ) : Stair := ⟨M,s.gap,p.key s,s.lam⟩
def ready (s:Scene n) (M:ℕ) := p.i≤ s.height∧p.i≤p.u∧p.u+M≤ s.roof∧
                match p.ask with
                | some k=> p.i=p.u∧ k< s.P.T
                | none=>True

def pursue (s:Scene n) : Vec :=
    match p.ask with
    | none => (s.frame p.i).W
    | some k=> (s.stage p.i).testU n k
def wear (s:Scene n) : Paint n:=fun _=>p.pursue s

end Peek
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset
variable {n : ℕ} [Fact n.Prime]

structure Surround (v C A:ℝ) : Prop where
   pre : ∀ b, TS v A (mainT v (prep v) b)
   main : ∀ f, Frag C f → (∀ x≤v,f x=0) → ∀ b,TS v A (mainT v f b)
   more : TS v A (suppT v false)
lemma surround_exists {v C:ℝ} (h:0<v) : ∃ A, Surround v C A := by
   obtain ⟨c,hc,-⟩:= frag_switch (show v/2<3*v/4 by linarith)
   obtain ⟨p,hp⟩:=main_ts (C:=max C c) h
   obtain ⟨q,hq⟩:=supp_ts h
   refine ⟨max p q, fun i=>(hp _ (hc.raise (le_max_right ..)) (fun x hx=>?_ ) i).extend
                             (le_max_left ..),fun f hf he b=>?_,(hq false).extend (le_max_right ..)⟩
   · exact rising_bot (by linarith) hx
   · exact (hp _ (hf.raise (le_max_left ..)) (fun x hx=> he x (by linarith)) b).extend (le_max_left ..)

structure Tonic (p : Const) where
    R : ℝ
    one : 1 ≤ R
    entry : ∀ (v : Kind) i k a b, i≤ k+pad p →
          TS v.theta R (mainT v.theta (if a=true then v.piece p k i else prep v.theta) b)
    support : ∀ v:Kind, TS v.theta R (suppT v.theta false)
    boostR : Lip R (fun x=>fourth (boost x))
    gammaR : Lip R (fun x=>fourth (gamma x))
    shutR : Lip R (fun x=>fourth (shutoff x))

def width (p : Const) := p.K+clim p
namespace Tonic
variable {p : Const} (u : Tonic p)
abbrev size:=u.R^3
lemma size1 : 1 ≤ u.size := one_le_pow₀ u.one
lemma fee {q:Quest} {s:Scene n} (hv:Tonic s.P) {M} (h:q.ready s M) :
    TS q.tag.theta hv.R (q.trio s) :=
    hv.entry q.tag q.i q.a q.main q.two (q.ampl h)
end Tonic

lemma tonic_up (P : Const) : Nonempty (Tonic P) := by
   obtain ⟨c,hc⟩:=bin_reg P (Est.box (4*pad P))
   obtain ⟨p,hp⟩:=shoulder_reg P
   obtain ⟨s,hs,_⟩:=frag_switch (show delta<2*delta by norm_num [delta,A])
   let C:= max c (max p s)
   have he (v : Kind) (i k) (h:i≤ k+pad P) : Frag C (v.piece P k i) := by
       cases v
       · exact (hc k i none (stayed P k i h)).raise (le_max_left ..)
       · exact (hc k i (some _) (stayed P k i h)).raise (le_max_left ..)
       · exact hp.raise (by unfold C; grind)
       · exact hs.raise (by unfold C; grind)
   obtain ⟨x,hx⟩:= surround_exists (C:=C) (by norm_num : 0<(1/2:ℝ))
   obtain ⟨y,hy⟩:= surround_exists (C:=C) dp
   obtain ⟨z,hz⟩:= surround_exists (C:=C) (by norm_num [A] : (0:ℝ)<A)
   obtain ⟨g,hg,-⟩:=frag_switch (by norm_num : (1/4:ℝ)<1/2)
   obtain ⟨q,-,hq⟩:=frag_switch (by norm_num : (1/2:ℝ)<4/5)
   obtain ⟨r,-,hr⟩:=frag_switch (by norm_num : (1/4:ℝ)<1/2)
   let R:=max x (max y (max z (max g (max q r))))
   have hl : x≤R ∧ y≤R ∧ z≤R ∧ g≤R ∧ q≤R ∧ r≤R := by simp [R,le_max_iff]
   have hu {v A : ℝ} (h:Surround v C A) (e:A≤R):Surround v C R :=
         ⟨fun b=>(h.pre b).extend e,fun f ht hv b=>(h.main f ht hv b).extend e,h.more.extend e⟩
   have H (v:Kind) : Surround v.theta C R := by
      cases v
      · exact hu hx (by grind)
      · exact hu hx (by grind)
      · exact hu hz (by grind)
      · exact hu hy (by grind)
   refine ⟨⟨R,hg.one.trans hl.2.2.2.1,fun v i k a b h=>?_,fun v=>(H v).more,
                       hg.lip.raise (by grind),hq.lip.raise (by grind),hr.lip.raise (by grind)⟩⟩
   cases a
   · exact (H v).pre b
   exact (H v).main _ (he v i k h) (fun x hx=> v.wall P k i hx) b

namespace Quest
variable (q:Quest) (s:Scene n)
lemma kept {v:Trio} {C} (ht: TS q.tag.theta C v) (u: Builder.Block n) (p:Paint n)
    (h:∀ w x,in01 (p w x)) :
    Tile (q.plan s) (C^3) (width s.P) ((q.builder s).wrapped u v q.two p) :=
     Tile.extend ((q.builder s).tiling_out u ht (dp.trans_le q.tag.lowp) q.two p h)
         le_rfl (by dsimp only [builder,width]; omega)
lemma canon {M} (h:q.ready s M) (v:Tonic s.P) :
    Tile (q.plan s) v.size (width s.P) (q.need s) :=
     q.kept s (Tonic.fee v h) (q.origin s) (q.guardP s) fun _=>q.dammed s
lemma covered (h:q.tag.narrow=true) (u:Builder.Block n) (p:Paint n) :
    Shelf (width s.P) ((q.builder s).wrapped u (q.trio s) q.two p) := by
   intro t y S
   apply le_trans ((q.builder s).fromshelf u (dp.trans_le q.tag.lowp) h q.two q.two p (fun x hx=> q.wall0 s hx) t y S)
   dsimp only [builder,width]; omega

abbrev axle (q : Quest) (s:Scene n) (x) := (s.stage q.i).gm n (q.steps s) x

lemma form0 {M} (h:q.ready s M) (e:s.SetUp) :
   SB (s.stage q.i).S (s.stage q.i).S (rate q.i) (s.P.T+1:ℝ) (q.question s).G := by
  let p:=s.stage q.i; let f:=rate q.i
  have hp := s.rankok e q.i
  have hh : p.f=f := by unfold Stg.f; rw [s.phase e]
  have hP : p.p=s.P:= s.aligned _
  change Step p.S f p.C at hp
  have hpf : Step p.S p.f p.C:=hh ▸ hp
  have hf := rate_pos q.i
  let T:ℝ:=s.P.T+1
  have hT1 : 1≤T:=by unfold T; simp
  have H (p : Mat) {v} (h : SB (s.stage q.i).S (s.stage q.i).S f v p)
           (he:v≤T): SB (s.stage q.i).S (s.stage q.i).S f T p :=
     ⟨h.nn,fun x y=>(h.key x y).trans (mul_le_mul_of_nonneg_right he hf.le),
      fun i=>(h.row i).trans he,h.loc⟩
  have hk {k} (he:k<s.P.T): SB p.S p.S f T (p.testG n k):=
     H _ (by rw [← hh]; exact p.tbounds n hpf k)
                   (by unfold T; have he1 : (k:ℝ)≤ s.P.T:=by exact_mod_cast he.le
                       linarith)
  unfold question
  obtain ⟨-,-,-,-,-,ht⟩:= h
  cases hu:q.tag
  · exact H _ hp hT1
  · next i=>
    have hp:=p.dbounds n hpf
    constructor
    · exact hp.nn
    · intro x y; change p.D n x y ≤ (s.P.T+1:ℝ)*f; simpa only [Nat.cast_add,Nat.cast_one,one_mul,hP,hh] using hp.key x y
    · intro x; exact (hp.row x).trans hT1
    · exact hp.loc
  · next b k=>
    rw [hu] at ht
    obtain ⟨hv,hh'⟩:=ht
    cases b
    · have he:= data_bounds hpf (p.cbounds n hpf k) (hh.symm ▸ hf)
      unfold Kind.matrix
      exact H _ (hh ▸ he) (by unfold T; have :=Nat.cast_le (α:=ℝ) |>.2 (le_of_lt hh'); linarith)
    · exact hk hh'
  · next k=>
    rw [hu] at ht; exact hk ht.2

set_option maxHeartbeats 800000 in
lemma free_mean {M} (h:q.ready s M) (e:s.SetUp) :
    let a := q.question s
    Ask.Valid a (axle q s) n := by
   have hx := q.form0 s h e
   let t:= s.stage q.i
   obtain ⟨hi,hu,hk,he,hq,hs⟩:=h
   have ht : t.i=q.i :=s.phase e _
   have he':t.p=s.P:=s.aligned _
   have hpf : Step t.S t.f t.C := by
        unfold Stg.f; rw [ht]; exact s.rankok e _
   refine ⟨e.ids _ hi,q.tag.lowp,s.fits e ?_,hk,s.fits e ?_, hx.nn,hx.row,?_⟩
   · change q.u≤_; omega
   · change q.a≤_; omega
   intro hn
   change q.tag.narrow=true at hn
   cases htag:q.tag <;> rw [htag] at hn <;> simp only [Kind.narrow,Bool.false_eq_true] at hn
   next b k=>
   rw [htag] at hs
   obtain ⟨h1,h2⟩:=hs
   unfold question
   simp only [htag]
   refine ⟨rfl,h1 ▸ hu, fun y hy hv=>?_⟩
   change t.gm n (steps q s) y ≠0 at hv
   have hg : 0 < t.gm n (steps q s) y:= lt_of_le_of_ne (gamma_mem ..).1 (Ne.symm hv)
   have hk : steps q s= if b then k+1 else s.P.T := by rw [steps,htag]
   rw [hk] at hg
   have hT: k<t.p.T :=by rw [he']; exact h2
   have hw : 2^t.i≤n:=by rw [ht]; apply s.fits e; omega
   cases b with
   | false=>
     simp only [Bool.false_eq_true,ite_false,← he'] at hg
     have hh:= t.cols n (e.ids _ hi) hpf hw hT hy hg
     change (rowhi t.S _ _ _).card*(rate q.a)≤limitJ s.P.J
     rw [← he',← show t.i=q.a from ht.trans h1]; exact hh
   | true=>
     simp only [ite_true] at hg
     have hh:= t.columns n (e.ids _ hi) hpf hw hT hy hg
     change (rowhi t.S _ _ _).card*(rate q.a)≤limitJ s.P.J
     rw [← he',← show t.i=q.a from ht.trans h1]; exact hh

end Quest
end
end ExactDerandomization.Net

end

section

/-! The estimates as mathematical values by well-founded additive recursion.
There is no salt; the restoring implementation uses deterministic catalytic
endpoint equality. -/
namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset

variable {n : ℕ} [Fact n.Prime]

structure Tick (n : ℕ) where
   outR : Quest→ Pics n
   outV : Peek→ Paint n
abbrev Roll (n) := ℕ→Tick n

def Tick.empty (n : ℕ) : Tick n := ⟨fun _ _ _ _=>0,fun _ _ _=>0⟩
abbrev detector (i u : ℕ) : Peek := ⟨i,i,some u⟩
abbrev prizep (i u : ℕ) : Peek := ⟨i,u,none⟩

def oracle {n} (r: Roll n) (m i : ℕ) (v : ℝ→ℝ) (k) :=
    Leader v k fun j=> (r m).outV (detector i j)
def leaderP (i : ℕ) := if i=0 then (fun (_:ℝ)=>(1:ℝ)) else boost
def carrier (s : Scene n) (r:Roll n) (m l j : ℕ) : Paint n :=
    if j=0 then fun _ _=>1 else oracle r m l boost s.P.T

namespace Quest
variable (s:Scene n) (q : Quest)
def tower (r : Roll n) (M : ℕ) : Paint n :=
   if q.main && q.tag.narrow then oracle r (M-1) q.i gamma (q.steps s) else fun _ _=>1

def tray (l M : ℕ) := (range (q.a+M+1)).filter fun k=> l ≤ k+pad s.P

structure Batch where
   pilot : Bool
   count : ℕ
   trim : Bool
def previous (b : Batch) (v:Stg) : Mat :=
   if b.pilot then (v.pilots n b.count).E else v.corr n b.count

def binReq (q : Quest) (u k : ℕ) : Quest := ⟨q.i,u,k,nar q.a k,.chip,true⟩
def bend (q : Quest) (b : Batch) (t:ℕ) : Quest :=
    ⟨q.i,q.u,q.i,t,.echo b.pilot (b.count-1),true⟩

def binsV (v : Stg) (k x y:ℕ) := bin k (v.C x y)

def localR (r : Roll n) (k : ℕ) : Line n :=
   ⟨fun m=> (q.plan s).carry k ((r m).outR (binReq q q.u k)),
      fun x y=> binsV (s.stage q.i) k x y / rate q.a⟩
def shareR (r:Roll n) (b:Batch) (k : ℕ) : Line n :=
   let a:=q.plan s
   let p:=s.stage q.i
   ⟨fun m=> a.carry k (a.pass q.i ((r m).outR (bend q b q.i))
                                        ((r m).outR (binReq q q.i k))),
    fun x y => mm p.S (previous (n:=n) b p) (binsV p k) x y / rate q.a⟩
def cutR (r:Roll n) (b:Batch) : Line n :=
    ⟨fun m u i j=> -((q.plan s).carry q.i
             ((r m).outR (bend q b (nar q.a q.i))) u i j),
         fun x y=> -(previous (n:=n) b (s.stage q.i) x y / rate q.a)⟩

def company (b : Batch) (M : ℕ) : Finset Ray :=
    q.tray s q.i M ×ˢ range (if b.count=0 then 1 else 2) ∪
                 (if b.trim then {(q.i,2)} else ∅)

def sign (r:Roll n) (b : Batch) (t:Ray) : Line n :=
    if t.2=0 then q.localR s r t.1
    else if t.2=1 then q.shareR s r b t.1
    else q.cutR s r b
def pipe (r:Roll n) (b:Batch) (M:ℕ) : Flame n :=
   ⟨q.company s b M, q.sign s r b,(q.question s).d,fun _ _=>0⟩

def briq (q:Quest) (l j k:ℕ) : Quest := ⟨l,q.u,k,nar q.a k,.slot j,true⟩

def divided (s:Scene n) (l i j k:ℕ) : Mat :=
   let p:=s.stage l
   let D:=p.D n
   fun x y=> p.fac n x i * (bin k (D x y) * share s.P.M j (D x y/rate l))

def fleet (l M:ℕ) := q.tray s l M ×ˢ range (s.P.M*s.P.M)
def inbound (r:Roll n) (l : ℕ) (t:Ray) : Line n :=
   let b:=s.P.M
   let i:=t.2/b
   let j:=t.2%b
   ⟨fun m=> (q.plan s).carry t.1 (pep b i j (honor (carrier s r m l i)
                                                 ((r m).outR (briq q l j t.1)))),
         fun x y=> markM b i j (divided s l i j t.1) x y/rate q.a⟩
def agency (r:Roll n) (l M : ℕ) : Flame n :=
   ⟨q.fleet s l M, q.inbound s r l,(q.question s).d,fun _ _=>0⟩

def blankLine (n:ℕ) : Line n := ⟨fun _ _ _ _=>0,fun _ _=>0⟩
def start (r:Roll n) (M:ℕ) : Flame n :=
   match q.tag with
   | .chip =>
     match q.i with
     | 0=>⟨∅,fun _=>blankLine n,(q.question s).d,(q.question s).d⟩
     | l+1=> q.agency s r l M
   | .echo b k=>q.pipe s r ⟨b,k,false⟩ M
   | .score k=>q.pipe s r ⟨true,k,false⟩ M
   | .slot _=> q.pipe s r ⟨false,s.P.T,true⟩ M

def fore (q : Quest) : Quest:= {q with main:=false}
def companion (r:Roll n) : Flame n :=
    let p:= q.truth_second s
    ⟨if q.two then {(q.a,0)} else ∅,
        fun _=> ⟨fun m u x y=> zeta*(r m).outR q.fore u x y,p⟩,p,fun _ _=>0⟩

def flame (r:Roll n) (M:ℕ) : Spray n 0 :=
    Flame.spill (q.stair s M) (q.plan s) q.t s.P.K (q.start s r M) (q.companion s r)
def rowBlock (r:Roll n) (M : ℕ) : Builder.Block n :=
   let v:=q.flame s r M
   fun u i=>(v.go u i).mid v.L
def activeR (r:Roll n) (M:ℕ) : Pics n:= (q.builder s).wrapped (q.rowBlock s r M)
                                              (q.trio s) q.two (q.tower s r M)
end Quest

namespace Peek
variable (s:Scene n) (v:Peek)

def score (i k:ℕ) : Quest := ⟨i,i,i,i,.score k,true⟩
def di (r:Roll n) (k : ℕ) : Flame n :=
   let p:= v.plan s
   let w:= ridge (v.pursue s)
   ⟨{(v.i,0)},fun _=>⟨fun m=> core (p.spout ((r m).outR (score v.i k)) s.P.J),w⟩,
        w,fun _ _=>0⟩

def bay (s : Scene n) (l u:ℕ) : Quest := ⟨l,u,l,l, .echo false (s.P.T-1),true⟩
def primeQ (r : Roll n) (l i : ℕ) : Line n :=
    let p:=s.frame l
    ⟨fun m=> core (vim s.P.M i (fame (carrier s r m l i)
                    ((r m).outV (prizep l v.u)))), ridge (mint s.P.M i (fun x=>p.P.fac n x i * p.W x))⟩
def syncQ (r:Roll n) (l i : ℕ) : Line n :=
    let p:=s.frame l
    let b:=bay s l v.u
    let d:= b.plan s
    let A:= mv p.P.S (p.P.corr n s.P.T) p.W
    ⟨fun m=> core (vim s.P.M i (fame (carrier s r m l i)
                        (d.passV l ((r m).outR b)
                                   ((r m).outV (prizep l l))))),
       ridge (mint s.P.M i (fun x=>p.P.fac n x i * A x))⟩
def roy (r:Roll n) (l:ℕ) : Flame n :=
    ⟨({v.i} : Finset ℕ) ×ˢ range (2*s.P.M),fun t=> if t.2<s.P.M then v.primeQ s r l t.2 else
                                               v.syncQ s r l (t.2-s.P.M),
       ridge (v.pursue s),fun _ _=>0⟩
def weave (r : Roll n) : Flame n :=
    match v.ask with
    | none =>
      match v.i with
      | 0=> ⟨∅,fun _=>Quest.blankLine n,ridge (v.pursue s), ridge (v.pursue s)⟩
      | l+1=> v.roy s r l
    | some k=>v.di s r k
def activeV (r : Roll n) (M : ℕ) :=
    (v.plan s).color (v.stair s M) (v.weave s r)
end Peek

def onQ (A M : ℕ) (k:StepKey) := decide (2*k.a+2*k.u+A*k.r < M/8)
def current (s : Scene n) (r : Roll n) (M:ℕ) : Tick n :=
   ⟨fun q => if onQ s.gap M (q.key s) then q.activeR s r M else fun _ _ _=>0,
     fun v=> if onQ s.gap M (v.key s) then v.activeV s r M else fun _ _=>0⟩

def rolls (s : Scene n) : ℕ → Roll n
   | 0=> fun _=>Tick.empty n
   | m+1=> fun k=> if k=m then current s (rolls s m) m else rolls s m k
def forecast (s : Scene n) (M) := current s (rolls s M) M

lemma vault {s : Scene n} (j i) (h : i<j) : rolls s j i=forecast s i := by
   induction j with
   | zero=>omega
   | succ j ih=>
     rw [rolls]; dsimp only; split
     · next he=>subst j; rfl
     · exact ih (by omega)

end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset

namespace Tonic
variable {p : Const} (v : Tonic p)
def bank := 4+2*v.size*(width p+1:ℝ)
def ticket := v.bank*Est.box (2*pad p)
def clergy := v.R*p.T*v.ticket
def natural := 4*v.size^3

lemma four : 4 ≤ v.bank := by
   unfold bank; have he:=v.size1; simp; positivity
lemma positiveT : 0<v.ticket := by have he:=v.four; exact mul_pos (by linarith) (box0 _)
lemma positiveC : 0≤v.clergy := by unfold clergy; have :=v.one; have :=v.positiveT; positivity

end Tonic

structure Purse {p : Const} (v:Tonic p) where
    ceil : ℝ
    peak : v.size≤ceil
    peakP : (width p+1:ℝ)*v.size^2 ≤ ceil
    peakD : 1+2*p.T/Hie.A≤ceil
    slip : ℝ
    slips : v.ticket ≤ slip
    slipP : Axis.fare v.size (width p)*(2*v.ticket) ≤ slip
    slipH : v.ticket+v.size*(width p+1:ℝ)*v.clergy≤ slip
    toll : ℝ
    toll1 : 20 ≤ toll
    tollC : 8*(p.M:ℝ)*p.M≤toll
    tollM : 2*(p.M:ℝ)≤toll
    tollD : 4*(p.T+1:ℝ)≤toll
    drives : Axis.paycheck ceil * slip ≤ toll
    baths : zeta*v.natural*v.ticket≤toll
    rankT : v.natural*v.ticket≤toll
    oneT : v.ticket+4*v.clergy ≤toll
    hugeT : 2*width p*v.natural*v.ticket + (width p+1:ℝ)^2*v.size^4*v.ticket+
                      (width p*v.size^4)*4*v.clergy≤ toll

set_option maxHeartbeats 1000000 in
lemma finance {p : Const} (v:Tonic p) : Nonempty (Purse v) := by
   let c:=max v.size (max ((width p+1:ℝ)*v.size^2) (1+2*p.T/Hie.A))
   let s:=max v.ticket (max (Axis.fare v.size (width p)*(2*v.ticket)) (v.ticket+v.size*(width p+1:ℝ)*v.clergy))
   let b:ℝ:=2*width p*v.natural*v.ticket + (width p+1:ℝ)^2*v.size^4*v.ticket+
                      (width p*v.size^4)*4*v.clergy
   let t:=max (max b (Axis.paycheck c*s))
           (max (max (max 20 (8*(p.M:ℝ)*p.M)) (max (2*(p.M:ℝ)) (4*(p.T+1:ℝ))))
            (max (zeta*v.natural*v.ticket) (max (v.natural*v.ticket) (v.ticket+4*v.clergy))))
   refine ⟨⟨c,?_,?_,?_,s,?_,?_,?_,t,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩⟩ <;> simp only [c,s,t,b,le_max_iff, le_refl, true_or, or_true]

namespace Purse
variable {p : Const} {v:Tonic p} (u:Purse v)

def prize := Spray.localP p.K 2 v.R (p.T+1:ℝ)*(2*(4*u.toll^2))
def venture := u.prize+
   v.size*(1+2*clim p:ℝ)*(v.R*v.natural*u.prize+4*v.clergy)
def askFor (A0:ℕ) :=
   u.prize* dry A0 ≤ v.bank ∧ u.venture*dry A0≤v.bank ∧ (24*u.toll^2)*dry A0≤v.bank
lemma one_peak : 1 ≤ u.ceil:=le_trans v.size1 u.peak
lemma toll_ok : 1 ≤ u.toll:=by linarith [u.toll1]
lemma prize_pos : 0 ≤ u.prize := by
   have hu:= Spray.charge_pos _ v.one
   have hp:=Spray.bprice_pos (M:=(p.T+1:ℝ)) (by simp) 2
   unfold prize Spray.localP; positivity

lemma credit : ∃ A0 : ℕ, u.askFor A0 := by

   obtain ⟨x,hx⟩ := exists_nat_ge (max u.prize (max u.venture (24*u.toll^2)))
   have he := box_big x; have hp:= v.four
   have ht (a:ℝ) (ha:a ≤ (x:ℝ)) : a*dry x≤v.bank := by
      refine le_trans ?_ (by linarith : (1:ℝ)≤v.bank)
      calc _ ≤ Est.box x * dry x := mul_le_mul_of_nonneg_right (by linarith) (dry0 x).le
           _ ≤ _:= le_of_eq (unify x)
   refine ⟨x,ht _ ?_,ht _ ?_,ht _ ?_⟩ <;> grind

end Purse

variable {n : ℕ} [Fact n.Prime]

structure Trust {s : Scene n} (T:Tonic s.P) (M : ℕ) (q:Tick n) : Prop where
    r {x:Quest} (hr:x.ready s M) :
       Tile (x.plan s) T.size (width s.P) (q.outR x) ∧
       (x.tag.narrow=true→Shelf (width s.P) (q.outR x)) ∧
       (x.two=true → (x.plan s).pinned x.t (q.outR x)) ∧
       (x.plan s).terr (x.need s) (q.outR x) ≤ T.bank * allowance s.gap M (x.key s)
    v {y:Peek} (hr:y.ready s M) :
       (∀ p i, in01 (q.outV y p i)) ∧
       (y.plan s).von (fun p i=> y.wear s p i-q.outV y p i)≤T.bank*allowance s.gap M (y.key s)

structure Tuned {s : Scene n} (T:Tonic s.P) (M : ℕ) (r: Roll n) : Prop where
    hM : 0<M
    history : ∀ m<M,Trust T m (r m)
    zero : r 0= Tick.empty n

namespace Tuned
variable {s : Scene n} {T:Tonic s.P} {M : ℕ} {r:Roll n}

structure Connection (u : StepKey) (k : ℕ) (p : Const) (v:StepKey) : Prop where
   rank : v.r < u.r
   epoch : v.a ≤ k+pad p
   turn : v.u ≤ u.u
lemma estimate (u:StepKey) {v : StepKey} (m k:ℕ) (hp:Connection u k s.P v)
    {q : ℝ} (h:q ≤ T.bank*allowance s.gap m v) :
       ratioN u.u v.u*q ≤ T.ticket*u.allowanceStep s.gap m k := by
   let B:=ratioN u.u v.u
   change B*q≤_
   have he := u.lower k hp.rank hp.epoch hp.turn s.gap m
   have ht : 0≤ T.bank:=by linarith [T.four]
   have hq:=mul_le_mul_of_nonneg_left h (show 0≤B from (box0 _).le)
   have hl:=mul_le_mul_of_nonneg_left he ht
   unfold Tonic.ticket B ratioN at *; linarith
lemma path (h:Tuned (s:=s) T M r) {m} (hi:m<M) {x : Quest} (he:x.ready s m)
    (u:StepKey) {k} (hk:Connection u k s.P (x.key s)) :
       ratioN u.u x.u*(x.plan s).terr (x.need s) ((r m).outR x) ≤
                           T.ticket*u.allowanceStep s.gap m k :=
  estimate u m k hk ((h.history m hi).r he).2.2.2
lemma route (h:Tuned (s:=s) T M r) {m} (hi:m<M) {x : Peek} (he:x.ready s m)
    (u:StepKey) {k} (hk:Connection u k s.P (x.key s)) :
       ratioN u.u x.u*(x.plan s).von (fun p i=>x.wear s p i-(r m).outV x p i) ≤
                           T.ticket*u.allowanceStep s.gap m k :=
  estimate u m k hk ((h.history m hi).v he).2

set_option synthInstance.maxSize 4096 in
lemma election (h:Tuned (s:=s) T M r) (m) (hi:m<M) (u : StepKey) (k j i)
    (g : ℝ→ℝ) (he : Lip T.R (fun t=>fourth (g t)))
    (hp:i ≤ s.P.T)
    (hr:∀ x< i,(detector j x).ready s m) (hk:∀ x< i,Connection u k s.P ((detector j x).key s)) :
    let p:= s.mode j j j
    ratioN u.u j * p.von (flawV (fun _ y=>g ((s.stage j).probed n i y)) (oracle r m j g i))
        ≤ T.clergy*u.allowanceStep s.gap m k := by
   intro d
   let C:= ratioN u.u j
   let V:=T.ticket*u.allowanceStep s.gap m k
   have hC : 0<C:=box0 _
   have h0 (x) (hi':x< i) :
      d.von (fun p i=> (detector j x).wear s p i - (r m).outV (detector j x) p i) ≤ V/C := by
     rw [le_div_iff₀ hC,mul_comm]
     exact h.route hi (hr x hi') u (hk x hi')
   let f (x:ℕ)(p:Pool n): Vec:=(s.stage j).testU n x
   let a (x:ℕ):=(r m).outV (detector j x)
   have he0 := d.leader_cost f a he (le_trans zero_le_one T.one) (fun i h=> h0 i h)
   have ha : (fun (_:Pool n) y=> g ((s.stage j).probed n i y))=Leader g i f:=by
      ext p y; exact (leaders_mean ..).symm
   change C*_≤_
   rw [ha]
   apply le_trans (mul_le_mul_of_nonneg_left he0 hC.le)
   have h1:0≤V:=by unfold V; exact mul_nonneg T.positiveT.le (StepKey.allow_p ..).le
   have hz : 0≤ T.R:=le_trans zero_le_one T.one
   have hh : (i:ℝ) ≤ (s.P.T:ℝ) := by exact_mod_cast hp
   calc _ = T.R*i*V := by field_simp
        _ ≤ (T.R*s.P.T*V:ℝ) := by gcongr
        _ = _ := by unfold Tonic.clergy V; ring

end Tuned
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset

variable {n : ℕ} [Fact n.Prime]
namespace Quest
variable (q:Quest) (s:Scene n)
abbrev goal := (q.plan s).narrowed q.t
lemma leavable (M) : 0 < (q.stair s M).key.r := by dsimp only [stair,key]; omega
lemma cutaway {M m k} (h:0<M) (he : m≤ M-(q.stair s M).cut k) : m<M := by
   unfold Stair.cut at he; omega
lemma fuelCap {M k l} (h:s.SetUp) (hz:q.ready s M) (he:k∈q.tray s l M) :
   2^nar q.a k≤n := by
   obtain ⟨ha,hb⟩:=mem_filter.mp he
   replace ha:=mem_range.1 ha
   obtain ⟨_,_,_,_,_,_⟩:= hz
   apply s.fits h; unfold nar; omega
lemma trayBudget {M k l m} (hz:q.ready s M) (he:k∈q.tray s l M)
    (hh:m≤ M-(q.stair s M).cut k) :
   nar q.a k+m ≤ s.roof := by
   obtain ⟨ha,hb⟩:=mem_filter.mp he; replace ha:=mem_range.1 ha
   obtain ⟨_,_,_,_,_,_⟩:=hz
   dsimp only [stair,key,Stair.cut,distn] at hh
   unfold nar; omega

lemma security (h:q.two=true) : (q.plan s).pinned q.t (q.need s) := by
   unfold need; rw [h]; exact Builder.bolts (q.builder s)

lemma ownedValid (e:s.SetUp) {M} (h:q.ready s M) (hv:q.two=true) :
     Ask.Valid (q.question s) (q.damp s) n := by
   obtain ⟨hx,hxa,hxb,hxc,hxd,hxe,hxf,hxg⟩:= q.free_mean s h e
   refine ⟨hx,hxa,hxb,hxc,hxd,hxe,hxf,?_⟩
   intro hs
   have he:q.main=true := by unfold two at hv; grind
   change q.tag.narrow=true at hs
   convert hxg hs using 1
   simp only [damp,he,hs,Bool.and_self,ite_true]

lemma amount (e:s.SetUp) {M} (h:q.ready s M) (hv:q.two=true) (x y)
   (hx:x∈(s.stage q.i).S) (hy:y∈(s.stage q.i).S) :
    (q.goal s).fm (q.need s) x y=q.phi s ((q.question s).d x y)*q.damp s y := by
   rw [normal s hv]
   have he : q.main=true := by unfold two at hv; grind
   exact bed.truth s.N (q.ownedValid s e h hv)
       (fun x hx=> by unfold phi; rw [ite_eq_left he]; exact q.tag.wall _ _ _ hx) _ _ hx hy

lemma slug (q:Quest) (s:Scene n) (h:q.two=true) :
   (q.goal s).BothPin (q.need s) := by rw [normal s h]; exact bed.twopin (n:=n) (q.question s) _ _ s.N _

lemma vapor (q:Quest) (s:Scene n) (h:q.two=true) (hz:q.tag.narrow=false) {M} (he:q.ready s M) :
   (q.goal s).SinglePin (q.need s) := by rw [normal s h]; exact bed.onepin (q.question s) _ _ s.N hz he.2.2.1

lemma unscale {M} (h:q.ready s M) (he:s.SetUp) (hm:q.main=true) (hx : q.tag=.chip)
    (x y) (hl:x∈(s.stage q.i).S) (hr:y∈(s.stage q.i).S) :
    rate q.a * (q.goal s).fm (q.need s) x y = binsV (s.stage q.i) q.a x y := by
   have hv:q.two=true:=by simp [two,hx,hm,Kind.paired]
   rw [q.amount s he h hv x y hl hr]
   let C:= (q.question s).G x y
   have ht : C≤ (s.P.T+1:ℝ)*rate q.i := (q.form0 s h he).key x y
   have hP : C=(s.stage q.i).C x y:=by simp [C,question,hx,Kind.matrix]
   have hd : q.damp s y=1:=by simp [damp,hx,Kind.narrow,hm]
   rw [hd,mul_one,phi, ite_eq_left hm,hx,binsV,←hP]
   have hh := bexact s.P q.a q.i none C ht
   rw [dirShare,mul_one] at hh
   exact hh

lemma transit {M} (h:q.ready s M) (he:s.SetUp) (hm:q.main=true) {j} (hx : q.tag=.slot j)
    (x y) (hl:x∈(s.stage q.i).S) (hr:y∈(s.stage q.i).S) :
    let C:=(s.stage q.i).D n x y
    rate q.a * (q.goal s).fm (q.need s) x y = bin q.a C * share s.P.M j (C/rate q.i) := by
   dsimp only
   have hv:q.two=true:=by simp [two,hx,hm,Kind.paired]
   rw [q.amount s he h hv x y hl hr]
   let C:= (q.question s).G x y
   have ht : C≤ (s.P.T+1:ℝ)*rate q.i := (q.form0 s h he).key x y
   have hP : C=(s.stage q.i).D n x y:=by simp [C,question,hx,Kind.matrix]
   have hd : q.damp s y=1:=by simp [damp,hx,Kind.narrow,hm]
   rw [hd,mul_one,phi, ite_eq_left hm,hx,←hP]
   exact bexact s.P q.a q.i (some j) C ht

lemma valid_E {M b k} (h:q.ready s M) (he:s.SetUp) (hm:q.main=true) (hx:q.tag=.echo b k)
    (x y) (hl:x∈(s.stage q.i).S) (hr:y∈(s.stage q.i).S) :
    rate q.i * (q.goal s).fm (q.need s) x y =
      if b=true then ((s.stage q.i).pilots n (k+1)).E x y else (s.stage q.i).corr n (k+1) x y := by
   have hv:q.two=true := by simp [two,hm,hx,Kind.paired]
   rw [q.amount s he h hv x y hl hr]
   let C:= (q.question s).G x y
   have ht : C≤ (s.P.T+1:ℝ)*rate q.i := (q.form0 s h he).key x y
   have hc : 0≤C:=(q.form0 s h he).nn x y
   let p:=s.stage q.i
   have ha : p.i=q.i := s.phase he _
   have ha1 : q.i=q.a:= by
       obtain ⟨-, -,-,-,-,hp⟩:=h; rw [hx] at hp; exact hp.1
   let f:=rate q.i
   have hp1 : p.f=f:=by unfold Stg.f; rw [ha]
   have hh := rate_pos q.i
   have heP : 0≤ C/f ∧ C/f≤ cap s.P := ⟨div_nonneg hc hh.le,le_trans
       ((div_le_iff₀ hh).2 ht) (by unfold cap; linarith)⟩
   have hq : q.phi s ((q.question s).d x y)=Q (C/f) := by
      have hu : (q.question s).d x y=C/f:=by simp only [Ask.d,question,← ha1]; rfl
      rw [hu,phi,ite_eq_left hm,hx,Kind.piece]
      simp only [Qc,clip,max_eq_right heP.1,min_eq_right heP.2]
   rw [hq]
   have hw (g : ℝ) : f*(Q (C/f)*g)= f*Q (C/f)*g := by ring
   change f*(Q (C/f)*_)=_
   rw [hw]; unfold damp steps; rw [hm,hx,Kind.narrow]
   have heh :=s.aligned q.i
   cases b
   · simp only [Bool.false_eq_true, ite_false,Bool.and_self,ite_true]
     have ht : C=p.nextG n k x y := by simp [C,question,hx,Kind.matrix,p]
     change _=correct p.f (p.nextG n k) (p.gm n p.p.T) x y
     rw [correct,hp1, ht,heh]
   · simp only [ite_true,Bool.and_self]
     have ht : C=p.testG n k x y := by simp [C,question,hx,Kind.matrix,p]
     change _=correct p.f (p.testG n k) (p.gm n (k+1)) x y
     rw [correct,hp1,ht]

lemma complete {b : Batch} (hb:0<b.count) {t M} (he:s.SetUp) (h:(q.bend b t).ready s M)
    (x y) (hx:x∈(s.stage q.i).S) (hy:y∈(s.stage q.i).S) :
    rate q.i * ((q.bend b t).goal s).fm ((q.bend b t).need s) x y=
                    previous (n:=n) b (s.stage q.i) x y := by
   have hz:=(q.bend b t).valid_E s (k:=b.count-1) h he rfl rfl x y hx hy
   rw [show b.count-1+1=b.count by omega] at hz
   unfold previous; by_cases em:b.pilot=true
   · rw [ite_eq_left em]; rw [ite_eq_left em] at hz; exact hz
   · rw [ite_eq_right em]; rw [ite_eq_right em] at hz; exact hz

end Quest

lemma peek_U (s:Scene n) (i j x) (h:x∈(s.stage i).S) :
   let p:= Peek.score i j
   let d:=p.plan s
   d.vm (d.spout (p.need s) s.P.J) x=

       U n d.S (p.question s).G i s.P.K s.P.J x := by
   intro p d
   apply d.expect_spout _ _ _ rfl ?_ h
   intro t x hx y hy
   let q:= p.question s
   change p.need s t x y=_
   unfold Quest.need Builder.wrapped Grid.result
   have hp : p.two=false:=by simp [p,Peek.score,Quest.two,Kind.paired]
   rw [hp]
   let u:=p.origin s t
   have hd : u=q.botRow:= funext fun i=>by simp [u,Quest.origin,Quest.truth_second,hp,q,Ask.botRow,Ask.raw]
   simp only [Grid.pre]
   rw [ite_eq_left (show x∈((p.builder s).sess t).src∧ y∈((p.builder s).sess t).dst∧
                                (True ∨ y∈((p.builder s).sess t).narrow) from ⟨hx,hy,Or.inl trivial⟩)]
   change (u x).val _ _ _ y * _ * _= _
   rw [hd]
   have he1 : ((p.builder s).sess t).sp=false := rfl
   have he2 : p.guardP s (crossP t) y=1 := by simp [p,Quest.guardP,Quest.damp,Peek.score,Kind.narrow]
   unfold Grid.incG
   rw [ite_eq_right (by simp only [he1]; decide),he2,mul_one,mul_one]
   unfold Blob.val
   change light _*gate delta _*1= _
   rw [mul_one]; unfold mark; congr 1
   exact q.hth ..

end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned
variable {n : ℕ} [Fact n.Prime]

namespace Quest
variable {s : Scene n} {q : Quest} {b:Batch}

def Befit (s:Scene n) (q : Quest) (b:Batch) :=
    (b.trim=false ∧ (q.tag=.echo b.pilot b.count ∨ q.tag=.score b.count∧ b.pilot=true)) ∨
    (b.trim=true ∧ b.pilot=false ∧ b.count=s.P.T ∧ ∃ j,q.tag=.slot j)

lemma Befit.outer (h:Befit s q b) : 6 < Kind.depth s.P q.tag := by
   obtain ⟨-,he|⟨he,-⟩⟩|⟨-,_,_,j,he⟩ :=h
   · rw [he]; unfold Kind.depth; cases b.pilot <;> simp <;> omega
   · rw [he,Kind.depth]; omega
   · rw [he,Kind.depth]; omega

lemma Befit.count (h:Befit s q b) {M} (he:q.ready s M) : b.count≤ s.P.T := by
   obtain ⟨_,_,_,_,_,hs⟩:=he
   obtain ⟨-,he|⟨he,-⟩⟩|⟨-,_,e1,-⟩ :=h
   · rw [he] at hs; exact hs.2.le
   · rw [he] at hs; exact hs.2.le
   · exact le_of_eq e1
lemma Befit.pos (h:Befit s q b) (ht:b.trim=true) : 0<b.count := by
   rcases h with h|h
   · simp [ht] at h
   rw [h.2.2.1]; exact s.P.tOK.1

lemma Befit.equal (h:Befit s q b) (x y) :
    let p:=s.stage q.i
    let A:=previous (n:=n) b p
    (q.question s).G x y=p.C x y + mm p.S A p.C x y - (if b.trim then A x y else 0) := by
  let p:=s.stage q.i
  have hP:=s.aligned q.i
  unfold question previous
  rcases h with ⟨ht,e|⟨e,hb⟩⟩|⟨ht,hb,hc,j,e⟩
  · cases hs:b.pilot
    · simp only [e,ht,hs,Bool.false_eq_true,ite_false,sub_zero]; rfl
    · simp only [e,ht,hs,Bool.false_eq_true,ite_false,ite_true,sub_zero]; rfl
  · simp only [e,hb,ht,Bool.false_eq_true,ite_true,ite_false,sub_zero]; rfl
  · simp only [e,hb,hc,ht,ite_true,Bool.false_eq_true,ite_false,← hP]; rfl

lemma Befit.ports (_:Befit s q b) {M} (_:q.ready s M) (hp : s.SetUp) :
    let p:=s.stage q.i
    SB p.S p.S (rate q.i) b.count (previous (n:=n) b p) := by
   let p:=s.stage q.i
   have ht : p.f=rate q.i := by unfold Stg.f; rw [s.phase hp]
   have hs : Step p.S p.f p.C := ht.symm ▸ s.rankok hp q.i
   unfold previous; split
   · exact ht ▸ p.pilot_bounds n hs _
   exact ht ▸ p.cbounds n hs _

lemma prev0 (p:Stg) (h:b.count=0) : previous (n:=n) b p= Hie.zero := by
    unfold previous; rw [h]; split <;> rfl

lemma Befit.covering {T : Tonic s.P} (v:Purse T) (h:Befit s q b) (hs:s.SetUp) {M}
    (hv:q.ready s M) (x y) :
    let p:=s.stage q.i
    let E:=previous (n:=n) b p
    p.C x y+mm p.S E p.C x y+(if b.trim then E x y else 0) ≤
                  v.ceil*(q.question s).G x y := by
    let p:=s.stage q.i
    let F:= previous (n:=n) b p
    let g:=(q.question s).G x y
    have ht:g=p.C x y+mm p.S F p.C x y-(if b.trim then F x y else 0):=h.equal x y
    have he : 0≤g:=(q.form0 s hv hs).nn x y
    change p.C x y + mm p.S F p.C x y+(if b.trim then F x y else 0) ≤ v.ceil*g
    by_cases hp: b.trim=true
    · rcases h with h|h
      · simp [hp] at h
      obtain ⟨-,h1,h2,h3⟩:=h
      have ho := s.rankok hs q.i
      have hH : p.f=rate q.i := by unfold Stg.f; rw [s.phase hs]
      have hE : F=p.corr n s.P.T := by unfold F previous; rw [ite_eq_right (by rw [h1]; decide),h2]
      have hu := cover (S:=p.S) (g:=p.gm n p.p.T)
                    (T:=s.P.T) (x:=x) (y:=y) (hH.symm ▸ ho) (rate_pos (p.i))
                          (fun x=>gamma_mem _)
      change p.C x y+ p.corr n s.P.T x y+mm p.S (p.corr n s.P.T) p.C x y ≤
               (1+2*s.P.T/A)*
            (p.C x y+mm p.S (p.corr n s.P.T) p.C x y - p.corr n s.P.T x y) at hu
      rw [ite_eq_left hp] at ht ⊢
      apply le_trans _ (mul_le_mul_of_nonneg_right v.peakD he)
      rw [ht,hE,add_right_comm]
      exact hu
    · have hx:=v.one_peak
      rw [ite_eq_right hp] at ht ⊢
      nlinarith

lemma eddy {M k m u} (he:q.ready s M) (hr:k∈q.tray s q.i M)
   (hp:m≤ M-(q.stair s M).cut k) (hv:q.i≤u) (ha:u≤q.u) :
    (q.binReq u k).ready s m := by
   have hw:= q.trayBudget s he hr hp
   obtain ⟨hi,hu,hk,hz,ht,hs⟩:=he
   have hm : m≤M:= by omega
   exact ⟨hi,hv,le_max_right ..,by dsimp only [binReq]; omega,hw,(mem_filter.1 hr).2⟩
lemma eddy_rank (h:Befit s q b) {u k} (hv : u≤q.u) :
    Connection (q.key s) k s.P ((q.binReq u k).key s) := by
   have he:= h.outer
   refine ⟨?_,?_,hv⟩
   · change 1+coreR s.P q.i+3+(if true=true then 1 else 0)<1+coreR s.P q.i+Kind.depth s.P q.tag+_ ; rw [ite_eq_left (rfl)]; omega
   dsimp only [key,binReq]; omega

lemma BendOK {a m M} (e:Befit s q b) (hp : q.ready s M) (hh:0<b.count)
   (hi:q.i≤a) (hm:a+m≤ s.roof) (hl : m≤M) :
   (q.bend b a).ready s m := by
   have ht:b.count-1< s.P.T:=by have :=e.count hp; omega
   obtain ⟨ha,hb,hc,hd,hs,hj⟩:=hp
   exact ⟨ha,hb,hi,by unfold bend; dsimp only; omega,hm,rfl,ht⟩
lemma BendRank {k a} (e:Befit s q b) (hh:0<b.count)
    (_:b.count≤ s.P.T) (hk : q.i≤k+pad s.P) :
    Connection (q.key s) k s.P ((q.bend b a).key s) := by
   refine ⟨?_,hk,le_refl _⟩
   unfold key bend; dsimp only [ite_true]
   rcases e with ⟨-,he|⟨he,hb⟩⟩|⟨-,hb,hq,j,he⟩
   · rw [he]
     cases b.pilot <;> dsimp [Kind.depth] <;> omega
   · rw [he,hb,Kind.depth,Kind.depth,ite_eq_left (rfl:Bool.true=Bool.true)]; omega
   · rw [he,hb,Kind.depth,Kind.depth,ite_eq_left (rfl:Bool.true=Bool.true)]; omega

end Quest
end
end ExactDerandomization.Net

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned

lemma ratioN_self (k : ℕ) : ratioN k k=1:=by simp [ratioN,Est.box]

variable {n : ℕ} [Fact n.Prime] {s : Scene n} {M : ℕ} {T:Tonic s.P}

namespace Quest
variable {q : Quest}

abbrev ideal (q:Quest) (s : Scene n) := (q.question s).d
abbrev grant (q : Quest) (v:Purse T) (M k : ℕ) :=
    Est.Line.Due (n:=n) (q.stair s M) k (q.plan s) (q.ideal s) true v.toll
lemma hpure (he:s.SetUp) (h:q.ready s M) (x y) : 0≤q.ideal s x y :=
   div_nonneg ((q.form0 s h he).nn x y) (rate_pos _).le

/- standard authorization for first-channel line, in deterministic
unscaled units. -/
set_option maxHeartbeats 700000 in
lemma transact (v:Purse T) (he:s.SetUp) (h:q.ready s M) {L:Line n} {k}
    (P : Mat) (a : ℕ→ Pics n) (g : Pics n) (_:Pics n)
    (hs:L.seq=fun m=> (q.plan s).carry k (a m)) (hA:L.account=fun x y=>P x y/rate q.a)
    (ha:a 0=fun _ _ _=>0)
    (hI:∀ i ∈ (q.plan s).S,∀ j∈(q.plan s).S,
         rate k*((q.plan s).narrowed (nar q.a k)).fm g i j=P i j)
    (hH:∀ i∈(q.plan s).S,∀ j∈(q.plan s).S,P i j ≤ v.ceil * (q.question s).G i j)
    (hK:2^nar q.a k≤n) (hp:RCap v.ceil g) (hr:(q.plan s).pinned (nar q.a k) g)
    (hR:∀ m≤ M-(q.stair s M).cut k,RCap v.ceil (a m) ∧ (q.plan s).pinned (nar q.a k) (a m) ∧
             ((q.plan s).narrowed (nar q.a k)).terr g (a m) ≤ v.slip*(q.stair s M).theta m k) :
    q.grant v M k L := by
   have hV :=le_trans (T.positiveT.le) v.slips
   apply Est.Line.Due.enlarge ?_ v.drives
   refine Est.Line.principal (d:=q.plan s) rfl hs ha (g:=g) ?_ ?_ (fun i _ j _=> hpure he h i j)
             v.one_peak hV hK hp hr hR
   · intro i hi j hj
     let d:= q.plan s
     have hh := d.carry_change k hr i hj
     rw [hh,hA]; dsimp only; rw [← hI i hi j hj]; change rate k / rate q.a * ((q.plan s).narrowed (nar q.a k)).fm g i j=_
     ring
   · intro i hi j hj
     have ht:= hH i hi j hj
     rw [hA]
     apply le_trans (div_le_div_of_nonneg_right ht (rate_pos q.a).le)
     exact le_of_eq (by change _ = v.ceil*((q.question s).G i j/rate q.a); ring)

set_option maxHeartbeats 700000 in
lemma direct (v:Purse T) (he:s.SetUp) (h:q.ready s M) {w : Quest} {r : Roll n}
    (hr:Tuned T M r) (L:Line n) (P:Mat)
    (hi:w.i=q.i) (hu:w.u=q.u) (ht:w.t=nar q.a w.a)
    (hs:L.seq=fun m=> (q.plan s).carry w.a ((r m).outR w))
    (hA:L.account=fun x y=>P x y/rate q.a)
    (hw:w.two=true)
    (hf:∀ m≤M-(q.stair s M).cut w.a,w.ready s m) (hj:Connection (q.key s) w.a s.P (w.key s))
    (hK:∀ i∈(q.plan s).S,∀ j∈ (q.plan s).S,
       rate w.a*(w.goal s).fm (w.need s) i j=P i j)
    (hH:∀ i∈(q.plan s).S,∀ j∈(q.plan s).S,P i j≤ v.ceil*(q.question s).G i j) :
    q.grant v M w.a L := by
   let d:=q.plan s
   have hd:w.plan s=d.narrowed w.a:=by unfold d plan Scene.mode Axis.narrowed; rw [hi,hu]
   have hg:w.goal s=d.narrowed (nar q.a w.a):=by unfold goal; rw [hd,ht]
   have hz : w.ready s 0:=hf _ (by omega)
   have hc := w.canon s hz T
   have hm (f:Pics n) (h : Tile (w.plan s) T.size (width s.P) f) : RCap v.ceil f:=
      (h.extend v.peak (le_refl _)).cap
   have hp (a:Pics n) (hr:(w.plan s).pinned w.t a) : d.pinned (nar q.a w.a) a := by rw [ht,hd] at hr; exact hr
   refine transact v he h P (fun m=> (r m).outR w) (w.need s) (w.need s) hs hA
        (by rw [hr.zero]; rfl) ?_ hH ?_ (hm _ hc) (hp _ (w.security s hw)) ?_
   · exact hg ▸ hK
   · apply s.fits he; rw [← ht]; obtain ⟨_,_,_,_,_,_⟩:=hz; omega
   intro m huM
   have htM := q.cutaway s hr.hM huM
   have hy:=hf _ huM
   obtain ⟨hy1,hy2,hy3,hy4⟩:= (hr.history _ htM).r hy
   refine ⟨hm _ hy1,hp _ (hy3 hw),?_⟩
   have ht:= hr.path htM hy _ hj
   have he : (w.plan s).terr (w.need s) ((r m).outR w) ≤ T.ticket*(q.stair s M).theta m w.a := by
       rw [show (q.key s).u=w.u from hu.symm,ratioN_self,one_mul] at ht; exact ht
   let p:= nar q.a w.a
   change (d.narrowed p).terr _ _≤_
   rw [hd] at he
   apply le_trans ((d.narrowed w.a).tsmall p (le_max_right ..) _)
   exact he.trans (mul_le_mul_of_nonneg_right v.slips ((q.stair s M).theta_nn ..))

namespace Befit

variable {b:Batch}
lemma staying (v:Purse T) (he:s.SetUp) (h:q.ready s M) {r:Roll n} (hr:Tuned T M r)
    (hp:Befit s q b) {k} (hi:k∈q.tray s q.i M) :
    q.grant v M k (q.localR s r k) := by
   let w :=q.binReq q.u k
   let p:=s.stage q.i; let F:=previous (n:=n) b p
   have ha:q.i≤ q.u:= h.2.1
   have H (m) (hm:m≤ M-(q.stair s M).cut k): w.ready s m:= eddy h hi hm ha le_rfl
   refine direct (w:=w) v he h hr (q.localR s r k) (binsV p k) rfl rfl rfl rfl rfl rfl H (eddy_rank hp le_rfl)
         (fun i hi j hj=>w.unscale s (H 0 (by omega)) he rfl rfl i j hi hj) ?_
   intro x hx y hy
   have hc:= hp.covering v he h x y
   have hv := (hp.ports h he).nn
   have hw := (s.rankok he q.i).nn
   have hh : 0≤ mm p.S F p.C x y:=sum_nonneg fun i _=> mul_nonneg (hv ..) (hw ..)
   have ht : 0≤(if b.trim then F x y else 0):=by split; apply hv; rfl
   apply (bin_mem (k:=k) (hw x y)).2.trans
   apply le_trans _ hc; change p.C x y ≤ p.C x y+_+ (if b.trim then F x y else 0)
   linarith

set_option maxHeartbeats 600000 in
lemma negative (v:Purse T) (he:s.SetUp) (h:q.ready s M) {r:Roll n} (hr:Tuned T M r)
    (hp:Befit s q b) (hn:b.trim=true) :
    q.grant v M q.i (q.cutR s r b) := by
   let w:=bend q b (nar q.a q.i)
   let p:=s.stage q.i
   let F:=previous (n:=n) b p
   let L:Line n:=⟨fun m=> (q.plan s).carry q.i ((r m).outR w),fun x y=>F x y/rate q.a⟩
   have hz:= hp.pos hn
   have H (m) (hm:m≤M-(q.stair s M).cut q.i) : w.ready s m := by
      have hm1 : m≤M:=by omega
      apply BendOK hp h hz (le_max_right ..) ?_ hm1
      obtain ⟨_,_,_,_,_,_⟩:=h
      omega
   have ha : q.grant v M q.i L := direct (w:=w) v he h hr L F rfl rfl rfl rfl rfl rfl H
         (BendRank hp hz (hp.count h) (by change q.i ≤ q.i+_; omega)) (fun i hi j hj=>q.complete s (t:=nar q.a q.i) hz he (H 0 (by omega)) i j hi hj) (by
          intro x hx y hy
          have hc:= hp.covering v he h x y
          have hv := (hp.ports h he).nn
          have hw:= (s.rankok he q.i).nn
          have hp : 0≤p.C x y:=hw x y
          have hh : 0≤ mm p.S F p.C x y:=sum_nonneg fun i _=> mul_nonneg (hv ..) (hw ..)
          dsimp only at hc; rw [ite_eq_left hn] at hc
          apply le_trans _ hc; change F x y ≤ p.C x y + _ + F x y; linarith)
   exact ha.negR

end Befit
end Quest
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned
variable {n : ℕ} [Fact n.Prime]
namespace Quest
namespace Befit
variable {M : ℕ} {s:Scene n} {T:Tonic s.P} {q : Quest} {b : Batch}

set_option maxHeartbeats 1200000 in
lemma pooled (v:Purse T) (he:s.SetUp) (h:q.ready s M) {r:Roll n} (hr:Tuned T M r)
    (hp:Befit s q b) {k} (hi:k∈q.tray s q.i M) (ht:0<b.count) :
    q.grant v M k (q.shareR s r b k) := by
   let p:=s.stage q.i; let d:=q.plan s; let t:=nar q.a k
   let f:= q.bend b q.i; let g:= q.binReq q.i k
   let a:=d.narrowed t
   have hi1:q.i≤q.u:= h.2.1
   have H (m) (hm:m≤ M-(q.stair s M).cut k) : f.ready s m ∧ g.ready s m := by
      refine ⟨BendOK hp h ht le_rfl ?_ (by omega), eddy h hi hm le_rfl hi1⟩
      have he := h.2.2.2.1
      omega
   let F:=f.need s; let G:=g.need s
   have hd1:f.plan s=a.deckX q.i:=rfl
   have hd2:g.plan s=a.deckY q.i k:=rfl
   have hz:= H 0 (by omega)
   have hz1:=f.canon s hz.1 T
   have hz2:=g.canon s hz.2 T
   let act:=d.pass q.i F G
   let w:=previous (n:=n) b p
   let account:=mm p.S w (binsV p k)
   have hk:2^q.i≤n:= s.fits he (by obtain ⟨_,_,_,_,_,_⟩:=h; omega)
   have hcap (p q':Pics n) (hp:Tile (f.plan s) T.size (width s.P) p)
       (hq:Tile (g.plan s) T.size (width s.P) q') :
                 RCap v.ceil (d.pass q.i p q') := by

      have ht:= a.pass_range (f:=p) (l:=k) hk T.size1 (hd1 ▸ hp) (hd2 ▸ hq)
      intro s' i j; obtain ⟨h1,h2⟩:=ht s' i j; exact ⟨h1,h2.trans v.peakP⟩
   have loc (p q':Pics n) (h:(g.plan s).pinned g.t q') :
                              d.pinned t (d.pass q.i p q') := by
      change a.pinned a.a (a.pass q.i p q')
      exact a.pass_pin (l:=k) h
   let approximate (m) := d.pass q.i ((r m).outR f) ((r m).outR g)
   refine transact v he h account approximate act act rfl rfl
     ?_ ?_ ?_ (q.fuelCap s he h hi) (hcap F G hz1 hz2) (loc F G (g.security s rfl)) ?_
   · unfold approximate; rw [hr.zero]; ext; simp [Tick.empty,Axis.pass]
   · intro x hx y hy
     change rate k*a.fm (a.pass q.i F G) x y=_
     have hpL:= slug f s rfl
     change (a.deckX q.i).BothPin F at hpL
     have hpR:= vapor g s rfl rfl hz.2
     change (a.startd q.i).SinglePin G at hpR
     rw [a.pass_id q.i F G hpL hpR hx hy]
     unfold account mm
     rw [mul_sum,mul_sum]
     apply sum_congr rfl
     intro i hk
     have hh:= g.unscale s hz.2 he rfl rfl i y hk hy
     have hp:= q.complete s ht he hz.1 x i hx hk
     change rate k * (a.startd q.i).fm G i y=binsV p k i y at hh
     change rate q.i*(a.deckX q.i).fm F x i=w x i at hp
     rw [←hh,←hp]; ring
   · intro x hx y hy
     have hp' := hp.covering v he h x y
     have hc := (s.rankok he q.i).nn
     have hw := (hp.ports h he).nn
     have hx1 : 0 ≤ p.C x y:= hc x y
     have hx2 : 0 ≤ if b.trim=true then w x y else 0:=by split; apply hw; rfl
     apply le_trans (b:=mm p.S w p.C x y) ?_
     · apply le_trans ?_ hp'
       change _ ≤ p.C x y+mm p.S w p.C x y+(if _ then w x y else 0); linarith
     · unfold account mm
       exact sum_le_sum fun i _=>mul_le_mul_of_nonneg_left (bin_mem (hc i y)).2 (hw x i)
   intro m hm
   have hF:=H m hm; have hW := q.cutaway s hr.hM hm
   obtain ⟨hF1,hF2,hF3,hF4⟩:= (hr.history m hW).r hF.1
   obtain ⟨hG1,hG2,hG3,hG4⟩:= (hr.history m hW).r hF.2
   refine ⟨hcap _ _ hF1 hG1, loc _ _ (hG3 rfl),?_⟩
   let F':=(r m).outR f; let G':=(r m).outR g
   have ht' := a.cost_pass (k:=q.i) (l:=k) (f:=F) (g:=G) (p:=F') (q:=G')
          hk (le_max_right ..) hi1 hz1.cap (hd2 ▸ hz2) hF1.cap (hF2 rfl) hG1.cap T.size1
   have hC:b.count≤ s.P.T:=hp.count h
   have hU:= hr.path hW hF.1 _ (BendRank (a:=q.i) hp ht hC (mem_filter.1 hi).2)
   have hV:= hr.path hW hF.2 _ (eddy_rank hp hi1)
   let c:=(q.stair s M).theta m k
   change ratioN q.u q.u* (a.deckX q.i).terr F F' ≤ T.ticket*c at hU
   rw [ratioN_self,one_mul] at hU
   change ratioN a.u q.i* (a.deckY q.i k).terr G G' ≤ T.ticket*c at hV
   change a.terr (a.pass q.i F G) (a.pass q.i F' G') ≤ v.slip*c
   have hw : 0≤ Axis.fare T.size (width s.P):= by unfold Axis.fare; have hh:=T.size1; positivity
   apply ht'.trans
   have hh:=mul_le_mul_of_nonneg_left (add_le_add hU hV) hw
   apply hh.trans
   have he:= v.slipP
   have hg:0≤c:= Stair.theta_nn ..
   linarith [mul_le_mul_of_nonneg_right he hg]

end Befit
end Quest
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned

variable {n : ℕ} [Fact n.Prime] {M:ℕ}
namespace Quest
variable {s : Scene n} {T : Tonic s.P} {q : Quest} {b:Batch} {r:Roll n}

def scrap (S : Domain) (x:ℝ) := x-∑ j∈S,bin j x

lemma trayDust (s:Scene n) (q:Quest) (i) (M) (x) (h:0≤x) (he:x≤ (s.P.T+1:ℝ)*rate i) :
   let v:=scrap (q.tray s i M) x
   0≤v ∧ v ≤rate (q.a+M) ∧ v≤ x := by
   have hu : ∑ j∈ q.tray s i M,bin j x=∑ j∈range (q.a+M+1),bin j x := by
      apply sum_subset (filter_subset ..)
      intro j hj hh
      have he1 : j+pad s.P< i:= lt_of_not_ge fun h=>hh (mem_filter.mpr ⟨hj,h⟩)
      exact beyond _ he1 he
   simp only [scrap,hu]; exact discarded h

lemma massCover (v:Purse T) (e:s.SetUp) (h:q.ready s M) (D:Mat) (p:Flame n)
    (hh : ∀ i j,p.tail i j= D i j / rate q.a)
    (he : ∀ i j,0 ≤ D i j ∧ D i j ≤ (s.P.T+1:ℝ)*rate (q.a+M))
    (hs : ∀ i∈(q.plan s).S,∑ j∈(q.plan s).S,D i j≤ s.P.T+1) :
   (q.plan s).ton (n:=n) (w:=0) (fun _=>p.tail) ≤ v.toll*(q.stair s M).wide := by
   obtain ⟨ha,hu,h1,h2,h3,h4⟩:=h
   let C:ℝ := s.P.T+1
   have he1:q.a≤ s.roof:=by omega
   have he2:q.u≤ s.roof:=by omega
   have hc:1 ≤ C:=by dsimp only [C]; simp
   have hv := (q.plan s).fine_tail (m:=M) hc (s.fits e he1) (s.fits e he2)
                              (e.count _ ha) (fun i _ j _=> he i j) hs
   rw [show p.tail=(fun x y=> D x y/rate q.a) from funext (fun i=>funext (hh i))]
   apply hv.trans
   refine le_trans (mul_le_mul_of_nonneg_left (StepKey.unbias (q.key s) s.gap M (q.leavable s M))
                         (show 0≤4*C by positivity)) ?_
   exact mul_le_mul_of_nonneg_right v.tollD (Stair.wide_nn (q.stair s M))

lemma pipeDust (v:Purse T) (e:s.SetUp) (h:q.ready s M) (hw:Befit s q b) :
   (q.plan s).ton (n:=n) (w:=0) (fun _=> (q.pipe s r b M).tail) ≤ v.toll*(q.stair s M).wide := by
   let p:= s.stage q.i; let F:= previous (n:=n) b p
   let A:= q.tray s q.i M
   let x:Mat:=fun i j=> scrap A (p.C i j)
   let G:= x + mm p.S F x
   have hf := s.rankok e q.i
   have hr:= hw.ports h e
   have hn i j: 0≤F i j := hr.nn i j
   have hc i j : p.C i j ≤ (s.P.T+1:ℝ)*rate q.i := calc
      _ ≤ _ := hf.key i j
      _ ≤ _ := mul_le_mul_of_nonneg_right (by simp) (rate_pos _).le
   have hz (i j) := q.trayDust s q.i M (p.C i j) (hf.nn i j) (hc i j)
   let Q:= rate (q.a+M)
   have hz' (i j) : 0≤x i j∧x i j≤Q∧x i j≤p.C i j:=hz i j
   have ha (i) : wt p.S x i≤1 :=
      le_trans (sum_le_sum (fun j _=> (hz' i j).2.2)) (hf.row i)
   have ht (i) : wt p.S F i ≤ s.P.T :=
              le_trans (hr.row i) (Nat.cast_le.2 (hw.count h))
   apply massCover v e h G _ ?_ ?_ ?_
   · intro i j
     let a:= rate q.a
     have hc := hw.equal i j
     let K:= A ×ˢ range (if b.count=0 then 1 else 2)
     let E: Ray:= (q.i,2)
     have hl (f: Ray→ℝ) :
        ∑ k∈ q.company s b M,f k=(∑ k∈K,f k)+(if b.trim then f E else 0) := by
        have hs:E∉K:=by dsimp [K,E]; by_cases e:b.count=0<;> simp [e]
        change ∑ k∈(K∪if b.trim then {E} else ∅),_=_ ; by_cases e:b.trim=true
        · rw [ite_eq_left e,ite_eq_left e,sum_union (disjoint_singleton_right.2 hs),sum_singleton]
        simp [e]
     let g (t:Ray):=(q.sign s r b t).account i j
     unfold Flame.tail
     change (q.question s).d i j-0- (∑ k∈ q.company s b M, g k)=G i j/a
     have hg (k) :
          (∑ j∈range (if b.count=0 then 1 else 2),g (k,j)) =
               bin k (p.C i j)/a + mm p.S F (binsV p k) i j/a := by
        by_cases e:b.count=0
        · simp only [e, ite_true, sum_range_succ, sum_range_zero,zero_add]
          have hf:F=Hie.zero:=prev0 p e
          rw [hf]; simp [mm,Hie.zero,g,sign,localR,p,binsV,a]
        · rw [ite_eq_right e,sum_range_succ,sum_range_succ,sum_range_zero,zero_add]
          rfl
     have hE:g E= -(F i j/a):=rfl
     let V:=∑ k∈ A, bin k (p.C i j)
     let R:=∑ k∈ A, mm p.S F (binsV p k) i j
     rw [sub_zero, hl,sum_product]
     rw [show (∑ k∈ A,∑ j∈range (if b.count=0 then 1 else 2),g (k,j))=V/a + R/a from
         (by simp_rw [hg]; simp only [sum_add_distrib,← sum_div,V,R]),hE,Ask.d]
     have hv : G i j=p.C i j-V + (mm p.S F p.C i j-R) := by
        dsimp only [G,Pi.add_apply,V,R,x,scrap,mm,binsV]
        simp_rw [mul_sub,sum_sub_distrib,Finset.mul_sum]
        congr 2
        apply sum_comm
     change (q.question s).G i j /a- (V/a+R/a+_) =_
     rw [hc,hv]
     change (_ + mm p.S _ _ _ _-(if _ then _ else 0)) / a- _ = _
     cases b.trim<;> simp only [ite_true,Bool.false_eq_true,ite_false,F,p] <;> ring
   · intro i j
     have hp:=rate_pos (q.a+M); change 0<Q at hp
     have he:0≤ mm p.S F x i j:=sum_nonneg fun i' _=>mul_nonneg (hn ..) (hz' ..).1
     have hs : mm p.S F x i j ≤ s.P.T*Q := calc
          _ ≤ ∑ k∈p.S,F i k*Q := sum_le_sum fun i' _=>mul_le_mul_of_nonneg_left (hz' ..).2.1 (hn ..)
          _ ≤ _ := by rw [← sum_mul]; exact mul_le_mul_of_nonneg_right (ht ..) hp.le
     exact ⟨add_nonneg (hz' ..).1 he, show x i j+mm p.S F x i j≤(s.P.T+1:ℝ)*Q by linarith [(hz' i j).2.1]⟩
   · intro i hi
     have hh : wt p.S (mm p.S F x) i ≤ s.P.T := by
        rw [wt_mm]
        exact le_trans (sum_le_sum (fun j _=>by simpa using mul_le_mul_of_nonneg_left (ha j) (hn i j))) (ht i)
     change wt p.S G i ≤ _
     have hs : wt p.S G i= wt p.S x i+wt p.S (mm p.S F x) i:=sum_add_distrib
     rw [hs]; linarith [ha i]

lemma cap_heat (v:Purse T) (_:s.SetUp) (_:q.ready s M) :
    ∑ t∈ q.company s b M,lull (q.stair s M).key.a t.1 ≤ v.toll := by
   unfold company
   let A := q.tray s q.i M; let I:= range (if b.count=0 then 1 else 2)
   let B: Finset Ray:=if b.trim then {(q.i,2)} else ∅
   have hb: ∑ t∈B,lull q.a t.1≤1:= by
      unfold B; split
      · simp only [sum_singleton]; exact dry_one _
      simp
   have hh:=scale_total A q.a
   have he: ∑ t∈A ×ˢ I,lull q.a t.1 ≤16 := by
      unfold I; rw [sum_product]
      split
      · simpa only [sum_const,nsmul_eq_mul,card_range,Nat.cast_one,one_mul] using le_trans hh
                                          (show (8:ℝ)≤16 by norm_num)
      · simp only [sum_const,nsmul_eq_mul,card_range,Nat.cast_ofNat,← mul_sum]; linarith
   have hs : Disjoint (A ×ˢ I) B := by
     unfold B; split
     · apply disjoint_singleton_right.2
       by_cases he:b.count=0 <;> simp [I,he]
     simp
   change ∑ t∈A ×ˢ I ∪ B,lull q.a t.1≤_
   rw [sum_union hs]; linarith [v.toll1]

set_option maxHeartbeats 500000 in
lemma wellPiped (v:Purse T) (e:s.SetUp) (h:q.ready s M) (hr:Tuned T M r) (hw:Befit s q b) :
    Flame.Owes (q.stair s M) (q.plan s) true v.toll (q.pipe s r b M) := by
   refine ⟨q.leavable s M,e.wind,v.toll_ok,fun t ht=>?_,pipeDust v e h hw,
                  cap_heat v e h,fun i _ j _=> hpure e h i j⟩
   change q.grant v M t.1 (q.sign s r b t)
   change t∈q.company s b M at ht
   unfold company at ht
   rcases mem_union.1 ht with he|he
   · obtain ⟨hx,hp⟩:=mem_product.mp he
     by_cases he:t.2=0
     · rw [sign,ite_eq_left he]; exact hw.staying v e h hr hx
     have hh := mem_range.mp hp
     split at hh
     · omega
     next hd=>
     rw [sign,ite_eq_right he,ite_eq_left (by omega : t.2=1)]
     exact hw.pooled v e h hr hx (Nat.pos_of_ne_zero hd)
   split at he
   · next hz=>
     rw [mem_singleton] at he; subst t
     have hE :=hw.negative v e h hr hz
     exact hE
   · simp at he

end Quest
end
end ExactDerandomization.Net

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned
variable {n : ℕ} [Fact n.Prime] {s:Scene n} {M:ℕ} {r:Roll n} {T:Tonic s.P}

def candidate (s:Scene n) (i j:ℕ) : Paint n := fun _ x=>(s.stage i).fac n x j

lemma castVote (h:Tuned T M r) {m} (hz:m<M) (q : StepKey) (k l i)
    (hr:∀ x< s.P.T,(detector l x).ready s m)
    (hk:∀ x< s.P.T, Connection q k s.P ((detector l x).key s)) :
    ratioN q.u l*(s.mode l l l).von
        (flawV (candidate s l i) (carrier s r m l i)) ≤ T.clergy*q.allowanceStep s.gap m k := by
   by_cases hp:i=0
   · have he : (candidate s l i)=carrier s r m l i:= by
        ext; simp only [carrier,hp,ite_true,candidate,Stg.fac]
     rw [he]
     have ht : (s.mode l l l).von (flawV (carrier s r m l i) (carrier s r m l i))=0 := by
         simp only [flawV,sub_self,Axis.von]; exact Meter.Lzero ..
     rw [ht,mul_zero]; exact mul_nonneg T.positiveC (StepKey.allow_p ..).le
   have he:=h.election m hz q k l s.P.T boost T.boostR le_rfl hr hk
   have hc : (candidate s l i)= fun (_:Pool n) y=> boost ((s.stage l).probed n s.P.T y):= by
      ext; unfold candidate Stg.fac; rw [ite_eq_right hp,s.aligned]
   rw [hc,carrier,ite_eq_right hp]
   exact he

lemma candid (s : Scene n) (j i p x) : in01 (candidate s j i p x):= Stg.fac_mem ..
lemma bounder (s : Scene n) (r : Roll n) (m i j p x) : in01 (carrier s r m i j p x) := by
   unfold carrier; split
   · norm_num [in01]
   · exact rising_mem ..

namespace Scene
variable (s:Scene n)
lemma mature (i) : s.stage (i+1)=(s.stage i).next n := rfl
lemma reset (i u a) : s.mode (i+1) u a=(s.mode i u a).nextd s.P.M := by
   unfold mode; rw [mature]
   simp [Axis.nextd,Stg.next,s.aligned]
lemma org (h:s.SetUp) (l i j : ℕ) :
    let p:=s.stage l
    let K:=s.P.M
    let x:=i/K; let y:=j/K
    let v:=p.D n x y
    (s.stage (l+1)).C i j=p.fac n x (i%K)*v*share K (j%K) (v/rate l) := by
    rw [mature]; simp [Stg.next,Stg.newMat, s.aligned,Stg.f,s.phase h]
lemma resid_mem (h:s.SetUp) (l i j):
    let p:=s.stage l
    0≤p.D n i j∧p.D n i j≤(s.P.T+1:ℝ)*rate l := by
   let p:= s.stage l
   have he:=s.rankok h l
   have hp:p.f=rate l:=by unfold Stg.f; rw [s.phase h]
   have hz:=p.dbounds n (hp.symm ▸ he)
   refine ⟨hz.nn ..,?_⟩
   have hh:=hz.key i j
   rw [hp] at hh
   simpa only [Nat.cast_add,Nat.cast_one,one_mul,p,s.aligned] using hh

end Scene
namespace Quest
variable {q:Quest}

set_option maxHeartbeats 1300000 in
lemma precinct {l} (v:Purse T) (e:s.SetUp) (h:q.ready s M) (hv:q.i=l+1) (ht:q.tag=.chip)
   (hr:Tuned T M r) {t : Ray} (hx:t∈q.fleet s l M) :
    q.grant v M t.1 (q.inbound s r l t) := by
   let S:=s.stage l; let K:=s.P.M
   have hm:0<K := by have :=s.P.mOK; unfold K; omega
   have hs:K<n:=e.radix_small
   obtain ⟨ha,hb⟩:=mem_product.1 hx
   let i:=t.2/K; let j:=t.2%K
   have hi:i<K:=(Nat.div_lt_iff_lt_mul hm).2 (mem_range.1 hb)
   have hj:j<K:=Nat.mod_lt _ hm
   let k:=t.1; let u:= q.briq l j k
   let d:= u.plan s; let Y:= nar q.a k
   let nd:=u.goal s
   let D:=q.plan s
   have he:(D.narrowed Y) = nd.nextd K:=by
       have hp:= s.reset l q.u q.a; unfold D plan; rw [hv,hp]; rfl
   have hq : q.i ≤ q.u := h.2.1
   have hk : l ≤ k+pad s.P:= (mem_filter.1 ha).2
   have hU (m) (hz : m ≤ M-(q.stair s M).cut k) : u.ready s m := by
      have hb:= q.trayBudget s h ha hz
      obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h; have hm:m≤M:=by omega
      exact ⟨show l≤ s.height by omega,show l≤q.u by omega,
             le_max_right ..,show q.u+m ≤ s.roof by omega,hb,hk,hj⟩
   have hR :=hU 0 (by omega)
   let w:=candidate s l i
   let f:= u.need s
   let g:= honor w f
   let W:= pep K i j g
   let P:= markM K i j (divided s l i j k)
   have hI := u.canon s hR T
   have hmP (x:Pics n) (y:Paint n) (hx:Tile d T.size (width s.P) x)
       (hy:∀ s i,in01 (y s i)): RCap v.ceil (pep K i j (honor y x)) :=
      Axis.pep_cap (Axis.root_cap_hon (hx.extend v.peak le_rfl).cap hy)
                            (le_trans zero_le_one v.one_peak)
   have hPin (x:Pics n) (y : Paint n) (hz : d.pinned Y x) : D.pinned Y (pep K i j (honor y x)):= by
       change (D.narrowed Y).pinned Y _
       rw [he]
       exact Axis.pep_pin _ hi hs (Axis.pinned_hon d hz)
   let a (m):=pep K i j (honor (carrier s r m l i) ((r m).outR u))
   refine transact v e h P a W W (k:=t.1) rfl rfl ?_ ?_ ?_ (q.fuelCap s e h ha)
          (hmP _ _ hI (candid s l i)) (hPin _ _ (u.security s rfl)) ?_
   · unfold a; rw [hr.zero]; ext; unfold honor Tick.empty pep markM
     split <;> simp
   · intro x hx y hy
     change rate k*(D.narrowed Y).fm W x y=P x y
     rw [he]; unfold W P; rw [nd.pep_mean hm hs]
     unfold markM; split
     · next hz=>
       let a:=x/K; let b:=y/K
       have hA : a∈S.S := (member_copy hm).1 (show x∈copyZone K S.S from by
          rw [← show (q.plan s).S = copyZone K S.S from congrArg Axis.S he]; exact hx)
       have hB : b∈S.S := (member_copy hm).1 (show y∈copyZone K S.S from by
          rw [← show (q.plan s).S = copyZone K S.S from congrArg Axis.S he]; exact hy)
       have hZ:= u.transit s hR e rfl rfl a b hA hB
       let V:=S.fac n a i
       have hx:nd.fm g a b=V*nd.fm f a b:= by
           unfold Axis.fm g honor Env.cond
           unfold w candidate; rw [av_mulc]; ring
       change rate k*nd.fm g a b=V*_
       rw [hx,mul_left_comm]
       exact congrArg (V*·) hZ
     · ring
   · intro x hx y hy
     have hp := (q.form0 s h e).nn x y
     let X:= (q.question s).G x y
     have hP:= v.one_peak
     change P x y ≤ v.ceil*X
     apply le_trans (b:=X) _ (by change 0≤X at hp; nlinarith)
     unfold P markM; split
     · next hz=>
       have hz' : X=(s.stage (l+1)).C x y:=by unfold X question; rw [hv,ht]; rfl
       let H:= S.D n (x/K) (y/K)
       have hh : bin k H≤H:=(bin_mem (s.resid_mem e l _ _).1).2
       rw [hz',s.org e]
       obtain ⟨h1,h2⟩:=hz
       dsimp only [divided]; rw [← h1,← h2, mul_assoc]
       apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hh (share_nn ..))
                                               (Stg.fac_mem ..).1
     · exact hp
   intro m hh
   have hM:=q.cutaway s hr.hM hh
   obtain ⟨h1,h2,h3,h4⟩:= (hr.history m hM).r (hU m hh)
   let f':=(r m).outR u
   let w':=carrier s r m l i
   let c:=(q.stair s M).theta m k
   refine ⟨hmP _ _ h1 (bounder s r m l i), hPin _ _ (h3 rfl),?_⟩
   change (D.narrowed Y).terr (pep K i j g) (pep K i j (honor w' f'))≤ _
   rw [he,nd.pep_terr hi hj hs]
   have hu:=nd.honors_fee (k:=l) (show l ≤ nd.u by change l≤q.u; omega) (p:=f)
         (q:=f') (a:=k) (le_max_right ..) hI.cap T.size1 h1 (candid s l i) (bounder s r m l i)
   apply hu.trans
   have hcon : Connection (q.key s) k s.P (u.key s) := by
      refine ⟨?_,?_,le_refl _⟩
      · unfold key u briq; dsimp
        rw [ht,hv]
        simp only [coreR,Nat.mul_add,Nat.mul_one,Kind.depth]
        unfold lag; omega
      · unfold key; change k≤k+_; omega
   have hr0 := hr.path hM (hU m hh) (q.key s) hcon
   have he : (nd.narrowed k).terr f f' ≤ T.ticket*c := by
       rw [show (q.key s).u=u.u from rfl,ratioN_self,one_mul] at hr0
       exact hr0
   have hV : ratioN nd.u l * (nd.startd l).von (flawV w w') ≤T.clergy*c := by
       have hgo (x) (hx:x< s.P.T) : (detector l x).ready s m := by
           obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h
           exact ⟨show l≤ s.height by omega,le_rfl,show l+m≤ s.roof by omega,rfl,hx⟩
       have hgc (x) (hx:x< s.P.T):Connection (q.key s) k s.P ((detector l x).key s):= by
           refine ⟨?_,hk,show l≤q.u by omega⟩
           · unfold key detector Peek.key
             rw [ht,hv]; dsimp [Kind.depth,coreR,lag]; simp only [Nat.mul_add,Nat.mul_one]
             omega
       exact castVote hr hM (q.key s) k l i hgo hgc
   change _≤v.slip*c
   let Z:=T.size
   have hz0 :=mul_le_mul_of_nonneg_left hV
                       (show 0≤T.size*(width s.P+1:ℝ) from mul_nonneg (le_trans zero_le_one T.size1)
                                                           (by positivity))
   have h0:0≤c:= Stair.theta_nn ..
   linarith [mul_le_mul_of_nonneg_right v.slipH h0]

end Quest
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned
set_option synthInstance.maxSize 4096
variable {n:ℕ} [Fact n.Prime] {s:Scene n} {q:Peek} {M:ℕ} {r: Roll n} {T:Tonic s.P}
namespace Peek

abbrev envtarget (s :Scene n) (q:Peek) := ridge (q.pursue s)

lemma gaze (h:s.SetUp) (q:Peek) (x) : in01 (q.pursue s x) := by
   unfold pursue; cases q.ask
   · exact (s.rights h q.i).win x
   · exact U_mem ..
lemma clear (h:s.SetUp) (q:Peek) (x y) : 0≤envtarget s q x y := by unfold envtarget ridge; split; exact (q.gaze h x).1; rfl

lemma shape (q : Peek) (s:Scene n) (M) : 0< (q.stair s M).key.r := by dsimp only [stair,key]; omega

abbrev owed (s:Scene n) (q : Peek) (c : ℝ) M := Est.Line.Due (n:=n) (q.stair s M) q.i
               ((q.plan s).narrowed 0) (envtarget s q) false c

lemma lensDue {c : ℝ} (h:s.SetUp) (hc:0≤c) (u: Paint n) (p:Vec) (g:ℕ→Paint n)
    (hu:g 0=fun _ _=>0)
    (he:∀ x∈(q.plan s).S,(q.plan s).vm u x=p x)
    (hs:∀ m≤M-(q.stair s M).cut q.i,
           (q.plan s).von (fun s i=> u s i-g m s i) ≤ c*(q.stair s M).theta m q.i) :
    owed s q c M ⟨fun m=>core (g m),ridge p⟩ := by
   let d:=q.plan s
   let L:Line n:=⟨fun m=>core (g m),ridge p⟩
   change L.Due (q.stair s M) (q.stair s M).key.a (d.narrowed 0) _ false _
   apply Est.Line.plain hc (g:=core u)
   · intro i _ j _; exact clear h q i j
   · ext; dsimp only [L]; unfold core ridge; rw [hu]; split <;> rfl
   · intro x hx y hy
     change (d.narrowed 0).fm _ x y = ridge p x y
     rw [d.diagh]; unfold ridge; rw [show d.vm u x=p x from he x hx]
   intro m hm
   have hx :
      (fun s i j=>core u s i j-core (g m) s i j)=core (fun s i=>u s i-g m s i):= by
       ext; unfold core ridge; split; rfl; ring
   change (d.narrowed 0).ton (fun s i j=>core u s i j-core (g m) s i j) ≤ _
   rw [hx,d.diagonal]; exact hs m hm

lemma stance {q:Peek} (v:Purse T) (h:s.SetUp) (L:Flame n)
    (he:L.lamp=envtarget s q)
    (hp:L.tail=fun _ _=>0)
    (hs:∀ t∈L.rays,t.1=q.i∧owed s q v.toll M (L.lines t))
    (hm:(L.rays.card:ℝ)≤v.toll) :
   L.Owes (q.stair s M) ((q.plan s).narrowed 0) false v.toll := by
   refine ⟨q.shape s M,h.wind,v.toll_ok,fun t ht=> ?_,?_,?_,?_⟩
   · rw [(hs t ht).1,he]; exact (hs t ht).2
   · rw [hp]
     exact le_trans (le_of_eq (Meter.Lzero _))
            (mul_nonneg (le_trans zero_le_one v.toll_ok) (Stair.wide_nn ..))
   · apply le_trans (sum_le_sum (g:=fun _=>1) (fun i hi=>dry_one _))
     simpa using hm
   · intros; rw [he]; exact clear h ..

lemma dueProbe (v:Purse T) (h:s.SetUp) (hr:Tuned T M r)
    (hq:q.ready s M) {k} (he:q.ask=some k):
    (q.di s r k).Owes (q.stair s M) ((q.plan s).narrowed 0) false v.toll := by
   let a:= Peek.score q.i k
   let d:= q.plan s
   obtain ⟨hi,hl,hH,hL⟩:=hq
   rw [he] at hL; obtain ⟨hh,hv⟩:=hL
   have hz : d=a.plan s:=by unfold d plan a Peek.score Quest.plan; rw [hh]
   apply stance v h _ (by rfl) (by ext; simp [di,Flame.tail]) _ (by simpa [di] using v.toll_ok)
   intro t ht; simp only [di,mem_singleton] at ht; subst t
   refine ⟨rfl,?_⟩
   let u:=d.spout (a.need s) s.P.J
   let g:ℕ→Paint n:=fun m=> d.spout ((r m).outR a) s.P.J
   have hGo m (hp:m<M) : a.ready s m :=
     ⟨hi,by rfl,le_refl _,show q.i+m≤ s.roof by omega,show q.i+m≤ s.roof by omega, rfl, hv⟩
   have ha : a.ready s 0:= hGo 0 hr.hM
   have hk:= a.canon s ha T
   let c:= T.natural*T.ticket
   apply Est.Line.Due.enlarge ?_ v.rankT
   have hc:0≤T.natural:=by unfold Tonic.natural; have hh:=T.size1; positivity
   refine lensDue (c:=c) h (mul_nonneg hc T.positiveT.le) u (q.pursue s) g ?_ ?_ ?_
   · ext; unfold g; rw [hr.zero]; unfold Axis.spout
     apply le_antisymm (rank_le (le_refl _) (fun x _=>le_refl 0)) (rank_nn ..)
   · intro x hx
     unfold u; rw [hz]
     have heI:=peek_U s q.i k x hx
     unfold pursue; rw [he]; change _=(s.stage q.i).testU n k x
     rw [show q.plan s=a.plan s from hz]
     apply heI.trans
     unfold Stg.testU
     rw [s.phase h,s.aligned]
     rfl
   intro m hm
   have he1:m<M:=by
      have ht:= Stair.cut (q.stair s M) q.i
      have hg:0<(q.stair s M).cut q.i:=by unfold Stair.cut; omega
      have hh:=hr.hM; omega
   have hc:= hGo m he1
   have hR:= hr.path he1 hc (q.key s) (k:=q.i) (show Connection _ _ _ _ from by
     refine ⟨?_,show q.i≤q.i+pad s.P by omega,hl⟩
     unfold Peek.key a Peek.score Quest.key; rw [he]
     simp [Kind.depth]; omega)
   have hzv : (q.key s).u=a.u:=hh.symm
   rw [hzv, ratioN_self,one_mul] at hR
   let z:=(r m).outR a
   change d.von (fun s i=> u s i-g m s i)≤_
   unfold u g; rw [hz]
   have ht := (a.plan s).root_fee hk.cap ((hr.history m he1).r hc).1.cap T.size1
   have hu:=(a.plan s).rank_fee (a.need s) z s.P.J (show a.a≤a.u from le_rfl)
   rw [show ratioN (a.plan s).u (a.plan s).a=1 from ratioN_self _,one_mul] at hu
   apply le_trans hu
   apply ht.trans
   have hs:=mul_le_mul_of_nonneg_left hR (show 0≤ T.natural by unfold Tonic.natural; have ht:=T.size1; positivity)
   change T.natural*_ ≤ _
   apply hs.trans
   exact le_of_eq (by unfold c; rw [mul_assoc]; rfl)

end Peek
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned
set_option synthInstance.maxSize 4096
variable {n:ℕ} [Fact n.Prime] {s:Scene n} {q:Peek} {M:ℕ} {r: Roll n} {T:Tonic s.P}

namespace Peek
lemma climb (q:Peek) (s:Scene n) {m M} (h:0<M) (he:m≤M-(q.stair s M).cut q.i): m<M:= by
   have hh : 0 < (q.stair s M).cut q.i := by unfold Stair.cut; omega
   omega

lemma dueStage {l m} (_:Purse T) (_:s.SetUp) (hr:Tuned T M r) (hp:q.ready s M)
   (he:q.i=l+1) (ha:m<M) (j : ℕ) :
    ratioN q.u l * (s.mode l l l).von
             (flawV (candidate s l j) (carrier s r m l j)) ≤
                T.clergy*(q.stair s M).theta m q.i := by
   obtain ⟨hx,hk,hb,_⟩:=hp
   refine castVote hr ha (q.key s) q.i l j ?_ ?_
   · intro i hi; exact ⟨show l≤ s.height by omega,le_rfl,
                               show l+m ≤ s.roof by omega,rfl,hi⟩
   intro i hi; refine ⟨?_,show l≤q.i+_ by omega,show l≤ q.u by omega⟩
   unfold key detector; rw [he]; dsimp [coreR]
   simp only [Nat.mul_add,Nat.mul_one,lag]; omega

/- generic minting case of direct W and passV -/
set_option maxHeartbeats 900000 in
lemma partners (v:Purse T) (h:s.SetUp) (hr:Tuned T M r) (hp:q.ready s M)
    {l i : ℕ} (he:q.i=l+1) (hi:i< s.P.M) (u:Paint n) (p : Vec) (g:ℕ→Paint n)
    (h0:g 0=fun _ _=>0)
    (hd:∀ x∈(s.stage l).S,(s.mode l q.u l).vm u x=p x)
    {c a : ℝ} (ha:0≤a)
    (hb:∀ m≤M-(q.stair s M).cut q.i,∀ s i,|g m s i|≤a)
    (hh:∀ m≤M-(q.stair s M).cut q.i,(s.mode l q.u l).von (fun s i=>u s i-g m s i) ≤
                       c*(q.stair s M).theta m q.i)
    (hz:c+a*4*T.clergy≤ v.toll) :
   let F:=fun m=> vim s.P.M i (fame (carrier s r m l i) (g m))
   let H:= mint s.P.M i (fun x=> (s.stage l).fac n x i*p x)
   owed s q v.toll M ⟨fun m=> core (F m),ridge H⟩ := by
   let X:=s.P.M
   have hX:0<X:= Nat.pos_of_ne_zero (by unfold X; omega)
   let d:=s.mode l q.u l
   let b:=candidate s l i
   let f:=vim X i (fame b u)
   have hc : (q.plan s).S=copyZone X (s.stage l).S:=by
      unfold plan; rw [he,s.reset]; rfl
   intro F H
   refine lensDue h (le_trans zero_le_one v.toll_ok) f H F ?_ ?_ ?_
   · ext; unfold F vim mint fame; split <;> simp_all
   · intro x hx
     have hs : (q.plan s).vm f = (d.nextd X).vm f:= rfl
     rw [hs]
     unfold f; rw [d.vim_mean hX h.radix_small]
     unfold H mint; split
     · rw [hc] at hx
       have hu: x/X∈(s.stage l).S:=(member_copy hX).1 hx
       have hp:= hd _ hu
       change d.vm u (x/X)=_ at hp; change _=_*p (x/X); rw [← hp]
       unfold Axis.vm Env.cond fame b candidate
       rw [av_cmul]
     · rfl
   intro m hm
   have ho: q.u ≥ l := by have :=hp.2.1; omega
   let x:= carrier s r m l i
   let p:Paint n:= fun t i=>fame b u t i-fame x (g m) t i
   have hN (f:Paint n) : (q.plan s).von f=(d.nextd X).von f := by
       have h : q.plan s=(s.mode l q.u q.i).nextd X:=by
           unfold plan; nth_rw 1 [he]; exact s.reset ..
       rw [h]; rfl
   rw [hN]; unfold f F
   rw [d.vim_cost hi h.radix_small]
   change d.von p ≤_
   have hg := d.fame_fee ha (candid s l i) (bounder s r m l i)
                                (hb m hm) (show l≤d.u from ho) (p:=u)
   apply hg.trans
   let z:=(q.stair s M).theta m q.i
   have ht:=dueStage v h hr hp he (q.climb s hr.hM hm) i
   change ratioN d.u l*(d.startd l).von (flawV b x)≤ _ at ht
   have he1:=hh m hm
   change d.von _≤c*z at he1
   have h1: 0≤z:= Stair.theta_nn ..
   change ratioN d.u l*_≤T.clergy*z at ht
   change _+_*(d.startd l).von (flawV b x)≤ v.toll*z
   linarith [mul_le_mul_of_nonneg_left ht (show 0≤a*4 by linarith),mul_le_mul_of_nonneg_right hz h1]

lemma prior {l m u} (hp:q.ready s M) (he:q.i=l+1) (hh:m<M) (hl:l≤u) (hs:u≤q.u) :
   (prizep l u).ready s m ∧ Connection (q.key s) q.i s.P ((prizep l u).key s) := by
   obtain ⟨ha,hb,hc,hv⟩:=hp
   refine ⟨⟨show l≤ s.height by omega,hl,show u+m≤ s.roof by omega,trivial⟩,
            ?_, show l≤q.i+_ by omega,hs⟩
   unfold key prizep; rw [he]; simp only [coreR,lag,Nat.mul_add,Nat.mul_one]; omega

lemma ownsPrime (v:Purse T) (h:s.SetUp) (hr:Tuned T M r) (hp:q.ready s M)
   {l i} (he:q.i=l+1) (hi:i< s.P.M) :
   owed s q v.toll M (q.primeQ s r l i) := by
   let p:= prizep l q.u
   let w:= (s.frame l).W
   let a m:= (r m).outV p
   have hl:l≤q.u:= by have :=hp.2.1; omega
   refine partners v h hr hp he hi (fun _=>w) w a ?_ (by intro x hx; rw [Axis.vdet])
                     (by norm_num : (0:ℝ)≤1) ?_ (c:=T.ticket) ?_ (by simpa using v.oneT)
   · unfold a; rw [hr.zero]; rfl
   · intro m hm s' j
     have hh:=q.climb s hr.hM hm
     have hf:= (hr.history _ hh).v (prior hp he hh hl le_rfl).1 |>.1 s' j
     exact (abs_of_nonneg hf.1).le.trans hf.2
   intro m hm
   have hh:= q.climb s hr.hM hm
   obtain ⟨hs,he⟩:= prior hp he hh hl le_rfl
   have hp:= hr.route hh hs _ he
   rw [show (q.key s).u=p.u from rfl,ratioN_self,one_mul] at hp
   exact hp

end Peek
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned
set_option synthInstance.maxSize 4096

variable {n:ℕ} [Fact n.Prime] {s:Scene n} {q:Peek} {M:ℕ} {r: Roll n} {T:Tonic s.P}
namespace Peek

set_option maxHeartbeats 1100000 in
lemma ownsMix (v:Purse T) (h:s.SetUp) (hr:Tuned T M r) (hp:q.ready s M)
   {l i} (he:q.i=l+1) (hi:i< s.P.M) :
   owed s q v.toll M (q.syncQ s r l i) := by
   let p:=s.frame l
   let A:= s.P.T; let d:=s.mode l q.u l
   let F:=p.P.corr n A; let w:= p.W
   let b:=bay s l q.u
   let p1:Paint n := fun _=>w
   let u:=d.passV l (b.need s) p1
   let U:=mv p.P.S F w
   let vV:=prizep l l
   let g m:=d.passV l ((r m).outR b) ((r m).outV vV)
   let C:= T.size; let D:=width s.P
   let a:ℝ:= D*C^4
   let c:= 2*D*T.natural*T.ticket+(D+1:ℝ)^2*T.size^4*T.ticket
   have hh: l ≤ q.u:= by have :=hp.2.1; omega
   have hA:0< s.P.T:=s.P.tOK.1
   have hb (m) (hm:m<M) : b.ready s m := by
      obtain ⟨ha,hb,hc,_⟩:=hp
      exact ⟨show l≤ s.height by omega,hh,le_refl l,show q.u+m≤ s.roof by omega,
               show l+m≤ s.roof by omega,rfl,show A-1< s.P.T by unfold A; omega⟩
   have hC := hb 0 hr.hM
   have hl:= s.fits h (show l≤ s.roof from by obtain ⟨ha,hb,hc,_⟩:=hp; omega)
   have hc := b.canon s hC T
   refine partners v h hr hp he hi u U g ?_ ?_ (show 0≤a by unfold a; positivity) ?_ (c:=c) ?_ v.hugeT
   · unfold g; rw [hr.zero]; ext; simp [Axis.passV, Tick.empty]
   · intro x hx
     change d.vm u x=U x
     rw [show u=d.passV l (b.need s) (fun _=>w) from rfl,
          d.passV_id l (b.need s) w (Quest.slug b s rfl) hx]
     unfold U mv; rw [mul_sum]
     apply sum_congr rfl; intro j hj
     have HH:= b.valid_E s (k:=A-1) hC h rfl rfl x j hx hj
     have ha : A-1+1=A:=by unfold A; omega
     change rate l * (b.goal s).fm _ x j= if false=true then _ else p.P.corr n (A-1+1) x j at HH
     rw [ite_eq_right (by decide),ha] at HH
     rw [← mul_assoc]; exact congrArg (fun v=> v*w j) HH
   · intro m hm x j
     have hx:= q.climb s hr.hM hm
     have he1:= (hr.history _ hx).r (hb m hx)
     have hZ:= (hr.history _ hx).v (prior hp he hx le_rfl hh).1
     have hs:0≤g m x j∧g m x j≤a:= d.pastbound hl he1.1 hZ.1 x j
     exact (abs_of_nonneg hs.1).le.trans hs.2
   intro m hm
   have hx:=q.climb s hr.hM hm; let y:=(q.stair s M).theta m q.i
   have h1:= (hr.history _ hx).r (hb m hx)
   have h3 (i) : in01 (w i):=(s.rights h l).win i
   let z:=(r m).outV vV
   let f:=(r m).outR b
   have hp1:= d.pastime (k:= l) (x:=p1) (y:=z) hl hh T.size1 hc h1.1 (h1.2.1 rfl) (fun _=>h3)
   have hz : Connection (q.key s) q.i s.P (b.key s):= by
      refine ⟨?_, show l≤q.i+pad s.P by omega,le_refl _⟩
      unfold key b Quest.key bay; rw [he]; dsimp [Kind.depth]
      simp only [coreR,lag,Nat.mul_add,Nat.mul_one]
      omega
   have hP := hr.path hx (hb m hx) _ hz
   rw [show (q.key s).u=b.u from rfl, ratioN_self,one_mul] at hP
   obtain ⟨hR,hR1⟩:= prior hp he hx le_rfl hh
   have hV:=hr.route hx hR _ hR1
   change ratioN d.u l*(d.startd l).von (fun s i=> p1 s i-z s i)≤ T.ticket*y at hV
   change (d.deckX l).terr (b.need s) f≤ T.ticket*y at hP
   apply hp1.trans
   let C := T.natural
   have hu:0≤ 2*(D:ℝ)*C := by unfold C Tonic.natural; have :=T.size1; positivity
   have hs:0≤(D+1:ℝ)^2*T.size^4:=by positivity
   have ht:=mul_le_mul_of_nonneg_left hP hu
   have hv:=mul_le_mul_of_nonneg_left hV hs
   change 2*D*C*_+(D+1:ℝ)^2*T.size^4* _ * (d.startd l).von (fun s i=>p1 s i-z s i) ≤ c*y
   change 2*D*C*(d.deckX l).terr (b.need s) f+ (D+1:ℝ)^2*T.size^4*ratioN d.u l* _ ≤ _
   unfold c; unfold C at *; linarith

lemma home {l} (he:q.i=l+1) (hw:q.ask=none) :
   (q.roy s r l).tail=fun _ _=>0 := by
  let p:=s.frame l; let K:=s.P.M; let A:=s.P.T
  have hK := s.aligned l
  change p.P.p=s.P at hK
  have hM:0<K:=by unfold K; have :=s.P.mOK; omega
  ext x y
  unfold Flame.tail; dsimp only [roy]; rw [sub_zero,sum_product,sum_singleton]
  let v:=mv p.P.S (p.P.corr n A) p.W
  have hs : q.pursue s x =
       p.P.fac n (x/K) (x%K)*(p.W (x/K)+v (x/K)) := by
     unfold pursue; rw [hw,he]; change (p.P.project n _) x=_
     change p.P.project n (p.W+mv p.P.S (p.P.corr n p.P.p.T) p.W) _=_
     simp only [Stg.project,hK]; rfl
  let f (i:ℕ) := (if i<K then q.primeQ s r l i else q.syncQ s r l (i-K)).account x y
  change ridge (q.pursue s) x y - ∑ i∈range (2*K), f i=0
  rw [show 2*K=K+K by omega,sum_range_add]
  let j : ℕ := x%K
  let f' (i:ℕ):= f i+f (K+i)
  have hv (i) (hi:i<K) :
      f' i= if x=y ∧ x%K=i then
       p.P.fac n (x/K) i*(p.W (x/K)+v (x/K)) else 0 := by
    have h1 : ¬K+i<K:=by omega
    have h2 : K+i-K=i:=by omega
    unfold f' f; rw [ite_eq_left hi, ite_eq_right h1,h2]
    dsimp only [primeQ,syncQ,ridge,mint]
    by_cases he:x=y
    · subst y; by_cases hk:x%s.P.M=i <;>
        simp [hk,p,v,A,K,mul_add]
    · simp [he]
  rw [← sum_add_distrib]
  change _ - ∑ i∈range K,f' i=0
  have hj:j<K:=Nat.mod_lt _ hM
  rw [sum_eq_single j,hv j hj]
  · unfold ridge; split
    · next h=> rw [ite_eq_left ⟨h,rfl⟩,hs]; ring
    · next h=> rw [ite_eq_right (fun e=> h e.1)]; ring
  · intro i hi hk; rw [hv i (mem_range.mp hi), ite_eq_right (fun e=>hk (Eq.symm e.2))]
  · simp [hj]

end Peek
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned
variable {n:ℕ} [Fact n.Prime] {s:Scene n} {M:ℕ} {r:Roll n} {T:Tonic s.P}
namespace Quest
variable {q:Quest}

set_option maxHeartbeats 800000 in
lemma residual_copies {l} (v:Purse T) (h:q.ready s M) (he:s.SetUp)
    (hl:q.i=l+1) (hz:q.tag=.chip) :
    (q.plan s).ton (n:=n) (w:=0) (fun _=> (q.agency s r l M).tail) ≤
                              v.toll*(q.stair s M).wide := by
   let p:=s.stage l; let D:= p.D n; let K:=s.P.M
   let E:=q.tray s l M
   have hk:0<K:=by have :=s.P.mOK; unfold K; omega
   let B:Mat:=fun i j=> D (i/K) (j/K)
   let C:Vec:=fun i=> p.fac n (i/K) (i%K)
   let A:Mat:=fun i j=> share K (j%K) (B i j/rate l)
   let V:Mat:=fun i j=> C i* A i j*scrap E (B i j)
   have h1 i j := q.trayDust s l M (B i j) (s.resid_mem he l .. |>.1) (s.resid_mem he l .. |>.2)
   have hA (i j) : C i*A i j ≤1 ∧ 0≤C i*A i j := by
      have hh:in01 (C i):=Stg.fac_mem ..
      have ht : in01 (A i j) := ⟨share_nn ..,share_le (Nat.mod_lt j hk) _⟩
      exact ⟨le_trans (mul_le_mul hh.2 ht.2 ht.1 zero_le_one) (le_of_eq (one_mul _)),
               mul_nonneg hh.1 ht.1⟩
   have heQ (x y) :
        (q.question s).G x y=(s.stage q.i).C x y:=by rw [question,hz]; rfl
   have hC (x y) : (s.stage q.i).C x y=C x*B x y*A x y:=by
      rw [hl]; exact s.org he l x y
   apply massCover v he h V _ ?_ ?_ ?_
   · intro x y
     let i:=x%K; let j:=y%K
     have hh (k) :
       ∑ z∈range (K*K),(q.inbound s r l (k,z)).account x y =
                         C x*A x y*bin k (B x y)/rate q.a := by
         have ht:=fromrad K i j (Nat.mod_lt y hk)
         rw [sum_eq_single (radix K i j)]
         · dsimp only [inbound]; change markM K ((radix K i j)/K) ((radix K i j)%K) _ x y/_=_
           rw [ht.1,ht.2,markM,ite_eq_left ⟨rfl,rfl⟩]
           change C x*(_*A x y)/_=_
           change C x*(bin k (B x y)*A x y)/_=_
           ring
         · intro t hi hne
           have hu : ¬(x%K=t/K∧y%K=t%K) := by
             rintro ⟨hp,hq⟩
             unfold radix i j at hne
             rw [hp,hq,Nat.mod_add_div] at hne
             exact hne rfl
           unfold inbound; dsimp only
           unfold markM
           change (if x%K=t/K ∧ y%K=t%K then _ else 0) /_=_
           rw [ite_eq_right hu,zero_div]
         intro he
         have hl:i<K:=Nat.mod_lt _ hk
         have hh:=Nat.mod_lt y hk
         have hu : radix K i j < K*K :=
             (Nat.div_lt_iff_lt_mul hk).1 (lt_of_le_of_lt (le_of_eq ht.1) hl)
         exact (he (mem_range.2 hu)).elim
     unfold Flame.tail
     change (q.question s).d x y-0-∑ k∈E ×ˢ range (K*K),(q.inbound s r l k).account x y=_
     rw [sub_zero,sum_product]; simp_rw [hh]
     rw [←sum_div, ← mul_sum]
     unfold Ask.d; rw [heQ,hC]
     change _ / rate q.a-C x*A x y*(∑ i∈E,bin i (B x y))/rate q.a = _
     unfold V scrap; ring
   · intro i j
     obtain ⟨ht,hx,-⟩:= h1 i j
     obtain ⟨ha,hb⟩:= hA i j
     refine ⟨mul_nonneg hb ht,?_⟩
     have hh : C i * A i j*scrap (q.tray s l M) (B i j) ≤ 1*rate (q.a+M) := mul_le_mul ha hx ht zero_le_one
     exact le_trans hh (mul_le_mul_of_nonneg_right (by simp) (rate_pos _).le)
   · intro i hi
     have ht := (q.form0 s h he).row i
     apply le_trans (sum_le_sum (s:=(q.plan s).S) _) ht
     intro j hj
     have hp:=mul_le_mul_of_nonneg_left (h1 i j).2.2 (hA i j).2
     rw [heQ,hC]; unfold V; unfold E; linarith

lemma dues_in {l} (v:Purse T) (h:q.ready s M) (he:s.SetUp)
    (hl:q.i=l+1) (hz:q.tag=.chip) (hr:Tuned T M r):
    (q.agency s r l M).Owes (q.stair s M) (q.plan s) true v.toll := by
   refine ⟨q.leavable s M,he.wind,v.toll_ok,fun t ht=> precinct v he h hl hz hr ht,
         residual_copies v h he hl hz,?_,fun i _ j _=> hpure he h i j⟩
   let K:=s.P.M; let E:=q.tray s l M
   change ∑ t∈ E ×ˢ range (K*K), lull q.a t.1 ≤ v.toll
   rw [sum_product]
   simp only [sum_const,nsmul_eq_mul,card_range,Nat.cast_mul,← mul_sum]
   apply le_trans (mul_le_mul_of_nonneg_left (scale_total E q.a) (show 0≤(K:ℝ)*K by positivity))
   have hx:=v.tollC; unfold K; linarith

lemma owesFirst (v:Purse T) (he:s.SetUp) (h:q.ready s M) (hr:Tuned T M r) :
   (q.start s r M).Owes (q.stair s M) (q.plan s) true v.toll := by
   cases ht:q.tag with
   | chip =>
     rw [start,ht]
     cases hq:q.i with
     | zero=>
       refine ⟨q.leavable s M,he.wind,v.toll_ok,by intros _ e; simp at e,?_,?_,
                            fun i _ j _=>hpure he h i j⟩
       · change (q.plan s).ton (n:=n) (w:=0) (fun _ i j=> (q.question s).d i j-(q.question s).d i j-∑ t∈ (∅:Finset Ray), _) ≤ _
         simp only [sum_empty,sub_self]
         apply le_trans (le_of_eq (Meter.Lzero _))
                   (mul_nonneg (le_trans zero_le_one v.toll_ok) (Stair.wide_nn ..))
       · simp only [sum_empty]; linarith [v.toll1]
     | succ i=>exact dues_in v h he hq ht hr
   | echo b k=>
     rw [start,ht]; apply wellPiped v he h hr
     exact Or.inl ⟨rfl,Or.inl ht⟩
   | score k=>
     rw [start,ht]; apply wellPiped v he h hr; exact Or.inl ⟨rfl,Or.inr ⟨ht,rfl⟩⟩
   | slot j=>
     rw [start,ht]; apply wellPiped v he h hr; exact Or.inr ⟨rfl,rfl,rfl,j,ht⟩

lemma lit (s:Scene n) (q:Quest) (r M) : (q.start s r M).lamp=(q.question s).d := by
   unfold start; cases q.tag <;> try rfl
   cases q.i <;> rfl

end Quest
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned

variable {n:ℕ} [Fact n.Prime] {s:Scene n} {M:ℕ} {r:Roll n} {T:Tonic s.P}
namespace Quest
variable {q:Quest}

lemma toothway (q:Quest) (s:Scene n) (x y) : 0≤q.truth_second s x y∧q.truth_second s x y≤ zeta := by
   unfold truth_second
   split
   · next h=>
     have ht := (q.question s).tooth_mem (n:=n) x y
     exact ⟨mul_nonneg zp.le ht.1,le_trans (mul_le_mul_of_nonneg_left ht.2 zp.le)
                            (le_of_eq (mul_one _))⟩
   exact ⟨le_rfl,zp.le⟩

lemma forerunner {m} (h:q.ready s M) (he:m≤M) : q.fore.ready s m := by
   obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h
   exact ⟨h1,h2,h3,le_trans (Nat.add_le_add_left he _) h4,le_trans (Nat.add_le_add_left he _) h5,h6⟩
lemma foreground (h : q.two=true) (s:Scene n) : Connection (q.key s) q.a s.P (q.fore.key s) := by
   have he:q.main=true:=by unfold two at h; grind
   refine ⟨?_,?_,le_rfl⟩
   · unfold key fore; simp [he]
   change q.a≤_; omega

set_option maxHeartbeats 900000 in
lemma owesBath (v:Purse T) (he:s.SetUp) (h:q.ready s M) (hr:Tuned T M r) :
    (q.companion s r).Owes (q.stair s M) (q.goal s) false v.toll := by
   let p:=q.companion s r
   have hez : p.tail=fun _ _=>0:= by
       by_cases ht:q.two=true
       · ext; simp [p,Flame.tail,companion,ht]
       · ext; simp [p,companion,truth_second,Flame.tail,ht]
   have hs : ∀ x y,0≤p.lamp x y:=fun x y=> (q.toothway s x y).1
   let t:=q.stair s M; let d:=q.goal s
   change p.Owes t d false v.toll
   have hZ : d.ton (n:=n) (w:=0) (fun _=>p.tail)≤ v.toll*t.wide := by
      rw [hez]; exact le_trans (le_of_eq (Meter.Lzero _)) (mul_nonneg (le_trans zero_le_one v.toll_ok) t.wide_nn)
   refine ⟨q.leavable s M,he.wind,v.toll_ok,?_, hZ, ?_,fun i _ j _=>hs i j⟩
   · intro i hi
     change i∈if _ then _ else _ at hi
     split at hi
     · next ht=>
       rw [mem_singleton] at hi; subst i
       let L:=p.lines (q.a,0); let g:= q.fore.need s
       change L.Due t t.key.a d p.lamp false v.toll
       have hx := forerunner h (show 0≤M from Nat.zero_le _)
       have hc : Tile (q.plan s) T.size (width s.P) g:= q.fore.canon s hx T
       let c:= zeta*T.natural*T.ticket
       have he0 : 0 ≤ 4*T.size^3 := by have hx:=T.size1; positivity
       have hc':0≤c := mul_nonneg (mul_nonneg zp.le he0) T.positiveT.le
       apply Est.Line.Due.enlarge ?_ v.baths
       refine Est.Line.plain hc' (g:=fun u i j=> zeta*g u i j) (fun i _ j _=>hs i j)
                           ?_ (fun i hi j hj=>?_) ?_
       · change (fun u i j=> zeta*(r 0).outR q.fore u i j)=_
         rw [hr.zero]; ext; simp only [Tick.empty,mul_zero]
       · have hf: g=bed.bath (q.question s):= prepared s rfl
         rw [d.fscalar,hf]
         change zeta*d.fm _ i j=q.truth_second s i j
         unfold truth_second; simp only [ht,ite_true]
         congr 1
         exact bed.tooth (n:=n) (q:=q.question s) s.N i j
       intro m hm
       have hW:q.fore.ready s m:= forerunner h (Nat.le_trans hm (Nat.sub_le _ _))
       have hm1:m<M:= q.cutaway s hr.hM hm
       have hh:= hr.history m hm1
       have hl:= hr.path hm1 hW _ (q.foreground ht s)
       rw [show (q.key s).u= q.fore.u from rfl,ratioN_self,one_mul] at hl
       let u:= (r m).outR q.fore; let K:=t.theta m q.a
       have hx' := (q.plan s).root_fee hc.cap (hh.r hW).1.cap T.size1
       have hs1 : d.ton (fun s i j=>g s i j-u s i j) ≤ T.natural*(T.ticket*K) :=
         le_trans ((q.plan s).tsmall _ h.2.2.1 _) (hx'.trans
           (mul_le_mul_of_nonneg_left hl (show 0≤ 4*T.size^3 by have hu:=T.size1; positivity)))
       change d.ton (fun s i j=> zeta*g s i j-zeta*u s i j)≤ c*K
       simp_rw [←mul_sub]
       rw [d.tscale,abs_of_pos zp]
       have hu:=mul_le_mul_of_nonneg_left hs1 zp.le
       apply hu.trans; exact le_of_eq (by unfold c; ring)
     · simp at hi
   · change (∑ t∈(if _ then _ else _),_) ≤ _
     split
     · simp only [sum_singleton]; exact le_trans (dry_one _) v.toll_ok
     · simp only [sum_empty]; linarith [v.toll1]

lemma tepid {i j} (h : (q.question s).d i j ≤ small) :
    q.truth_second s i j=0 := by
   have he:(q.question s).z=q.tag.theta:=rfl
   have ht:=q.tag.lowp
   unfold truth_second; split
   · dsimp only; rw [Ask.tooth0 (q.question s) (dp.trans_le ht),mul_zero]
     apply le_trans h; rw [he]; unfold small delta A at *; linarith
   · rfl

lemma exhaust (v:Purse T) (he:s.SetUp) (h:q.ready s M) (hr:Tuned T M r) :
     (q.flame s r M).Works (2* Flame.contract (q.stair s M) v.toll) (s.P.T+1) := by
    unfold flame
    have hs:=s.rankok he q.i
    have heT:= q.form0 s h he
    refine Flame.ready (owesFirst v he h hr) (owesBath v he h hr) (by simp)
               (he.ids q.i h.1) h.2.2.1 (s.fits he ?_) ?_ ?_
    · obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h
      change q.a≤_; omega
    · intro i hi j hj; obtain ⟨ha,hb⟩:=q.toothway s i j
      rw [q.lit]
      exact ⟨(le_of_eq (abs_of_nonneg ha)).trans hb,tepid⟩
    · intro i hi
      rw [q.lit]; unfold Ask.d; simp only [←sum_div]
      let t := ∑ j∈(q.plan s).S, (q.question s).G i j
      change t/rate q.a*rate q.a ≤_
      rw [div_mul_cancel₀ _ (rate_pos _).ne']; exact heT.row i

lemma rootBills (v:Purse T) (he:s.SetUp) (h:q.ready s M) (hr:Tuned T M r)
    {o : Trio} (ho:TS q.tag.theta T.R o) (b : Bool) :
    (q.plan s).terr ((q.builder s).coins (q.origin s) o b)
                ((q.builder s).coins (q.rowBlock s r M) o b) ≤ v.prize*(q.stair s M).wide := by
   let p:=q.flame s r M
   let H:= q.builder s
   have he1 (u i): q.origin s u i=(p.go u i).origin := by
      unfold p flame Flame.spill Spray.go origin; rw [q.lit]; rfl
   have he2 : q.origin s=(fun u i=>(p.go u i).origin):= funext (fun i=>funext (he1 i))
   have hb:= H.rated p (C:=T.R) rfl rfl ho (exhaust v he h hr) q.tag.lowp q.tag.highp b
   rw [he2]
   unfold Axis.terr; rw [opposing]
   let S:=q.stair s M
   apply hb.trans
   change Spray.localP s.P.K 2 T.R (s.P.T+1)*(2*(Flame.contract S v.toll)) ≤ v.prize*S.wide
   exact le_of_eq (by unfold Purse.prize Flame.contract; ring)

end Quest
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned
set_option synthInstance.maxSize 4096
variable {n:ℕ} [Fact n.Prime] {s:Scene n} {M:ℕ} {r:Roll n} {T:Tonic s.P}
namespace Quest
variable {q:Quest}

lemma wallClock (s : Scene n) (q:Quest) (i u M) (r:Roll n) : in01 (q.tower s r M u i):=by
   unfold tower; split; apply gamma_mem
   norm_num [in01]

set_option maxHeartbeats 700000 in
lemma threshold {p k} (h:q.ready s M) (ht:q.tag=.echo p k) (hr:Tuned T M r):
    ratioN q.u q.a * ((q.plan s).startd q.a).von (flawV (q.guardP s) (q.tower s r M)) ≤
              4*T.clergy * (q.stair s M).wide := by
   let A := (q.stair s M).wide
   rcases em : q.main
   · have H : q.guardP s = q.tower s r M := by ext; simp [em,guardP,tower,damp]
     rw [H]
     simp only [flawV,sub_self,Axis.von,Meter.Lzero,mul_zero]
     exact mul_nonneg (mul_nonneg (by positivity) T.positiveC) (Stair.wide_nn ..)
   obtain ⟨hi,hU,hA,h1,h2,h3⟩:=h
   rw [ht] at h3
   obtain ⟨hb,hk⟩:=h3
   let t:=q.steps s
   have hu : t=if p then k+1 else s.P.T := by unfold t steps; rw [ht]
   have hT : t≤ s.P.T:=by rw [hu]; split <;> omega
   have H : q.tower s r M=oracle r (M-1) q.i gamma t := by
       unfold tower; rw [em,ht]; rfl
   have H' : q.guardP s=fun (_:Pool n) i=>gamma ((s.stage q.i).probed n t i):=by
       unfold guardP damp; rw [em,ht]; rfl
   have hg:M-1<M:=by have:=hr.hM; omega
   have ha j (h:j<t) : (detector q.i j).ready s (M-1):=by
       exact ⟨hi,le_rfl,show q.i+(M-1)≤ s.roof by omega,rfl,show j< s.P.T by omega⟩
   have hz j (h:j<t) : Connection (q.key s) q.a s.P ((detector q.i j).key s) := by
       refine ⟨?_, show q.i ≤ q.a+pad s.P by omega,hU⟩
       unfold key detector Peek.key; rw [ht,em]; rw [hu] at h
       cases p <;> simp only [Kind.depth,Bool.false_eq_true,ite_true,ite_false] at * <;> omega
   have he := hr.election (M-1) hg (q.key s) q.a q.i _ _ T.gammaR hT ha hz
   have hs := StepKey.divide (q.key s) (Nat.sub_le M 1)
               (show M-(M-1)≤1+distn q.a q.a+1 by unfold distn; omega) le_rfl
                    (q.leavable s M) (A:=s.gap)
   have hv : (q.key s).allowanceStep s.gap (M-1) q.a ≤ 4*A:=by
      change salary q.a q.a*_≤ A* _* dry (distn q.a q.a/2) at hs

      simp only [salary,le_refl,ite_true,Nat.sub_self,distn,Nat.zero_add,Nat.zero_div] at hs
      norm_num [Est.box,dry] at hs
      simpa only [mul_comm] using hs
   rw [H,H']
   have hh : (q.plan s).startd q.a=s.mode q.i q.i q.i:=by unfold plan Scene.mode Axis.startd; rw [hb]
   rw [hh]
   change ratioN q.u q.a * _ ≤ _
   conv_lhs=>lhs; rw [← hb]
   apply he.trans
   apply le_trans (mul_le_mul_of_nonneg_left hv T.positiveC)
   exact le_of_eq (by unfold A; ring)

set_option maxHeartbeats 1100000 in
lemma lively (v:Purse T) (he:s.SetUp) (h:q.ready s M) (hp:Tuned T M r)
    (hm:v.askFor s.gap) :
     (q.plan s).terr (q.need s) (q.activeR s r M)≤T.bank*allowance s.gap M (q.key s) := by
    let V:=allowance s.gap M (q.key s)
    let c:=(q.stair s M).wide
    have hc0 : 0≤V:= (StepKey.allow_p ..).le
    have hr (a : ℝ) (hh:a*dry s.gap≤T.bank) : a*c≤ T.bank*V := by
       change a*(V*dry s.gap)≤_
       linarith [mul_le_mul_of_nonneg_right hh hc0]
    let K:=q.builder s
    let i:=q.origin s; let j:=q.rowBlock s r M
    let u:=q.guardP s; let w:=q.tower s r M
    let z:= q.trio s
    have h0:=T.one
    have hh:TS K.tau T.R z:=Tonic.fee T h
    have he1 := rootBills v he h hp hh q.two
    change (q.plan s).terr (K.wrapped i z q.two u) (K.wrapped j z q.two w)≤T.bank*V
    by_cases hx:q.tag.narrow=true
    · have hC:∃ b k,q.tag=.echo b k := by
          cases he:q.tag <;> rw [he] at hx <;> simp [Kind.narrow] at *
      obtain ⟨b,k,hg⟩:=hC
      have hZ := threshold h hg hp
      have hu := T.support q.tag
      have heT : 0<q.tag.theta:= dp.trans_le q.tag.lowp
      have hm1:q.i=q.a:= by obtain ⟨_,_,_,_,_,hp⟩:=h; rw [hg] at hp; exact hp.1
      have hv0:q.a≤q.u:=hm1 ▸ h.2.1
      have hf (o:Builder.Block n) (u:Paint n):
          Shelf (clim K.p) (K.wrapped o z q.two u):= K.fromshelf o heT hx q.two q.two u
                                    (fun x hx=>q.wall0 s hx)
      have ha:= Builder.sealed K i j (mul_nonneg v.prize_pos (show 0≤c from Stair.wide_nn ..))
                        u w z q.two hh hu heT hx hv0 (fun _=>q.dammed s)
                        (fun u i=>q.wallClock s i u M r) T.shutR (by linarith : 0≤T.R)
                        (hf i u) (hf j w) he1 (rootBills v he h hp hu false)
      apply ha.trans
      apply le_trans _ (hr v.venture hm.2.1)
      unfold Purse.venture
      let X:ℝ:= T.R^3*(1+2*clim s.P)
      have htX:0≤ X := by unfold X; positivity
      have hQ:=mul_le_mul_of_nonneg_left hZ htX
      change v.prize*c+X*(_*(v.prize*c)+_)≤_
      simp only [Tonic.natural,Tonic.size,u,w,X,plan,Scene.mode,c] at *; linarith
    · have H (u : Paint n) (h:u=fun _ _=>1) (f : Builder.Block n) :
            K.wrapped f z q.two u=K.coins f z q.two := by
         ext s' x y
         unfold Builder.wrapped Builder.coins Grid.result Grid.incG
         simp [h, K,Builder.sess,builder,hx]
      have hu': u=fun _ _=>1 := by unfold u guardP damp; simp [show q.tag.narrow=false from Bool.eq_false_iff.mpr hx]
      have hw': w=fun _ _=>1 := by unfold w tower; simp [show q.tag.narrow=false from Bool.eq_false_iff.mpr hx]
      rw [H _ hu',H _ hw']
      exact he1.trans (hr _ hm.1)

lemma contents (v:Purse T) (he:s.SetUp) (h:q.ready s M) (hp:0<M→Tuned T M r)
    (hm:v.askFor s.gap) :
    let f:=(current s r M).outR q
    Tile (q.plan s) T.size (width s.P) f ∧
       (q.tag.narrow=true→Shelf (width s.P) f) ∧
       (q.two=true → (q.plan s).pinned q.t f) ∧
       (q.plan s).terr (q.need s) f ≤ T.bank * allowance s.gap M (q.key s) := by
   dsimp only [current]
   split
   · next hi=>
     have hx:0<M:=by by_contra! ht; simp [onQ,Nat.eq_zero_of_le_zero ht] at hi
     refine ⟨q.kept s (Tonic.fee T h) _ _ (fun u i=>q.wallClock s i u M r),
          fun he=> q.covered s he _ _,?_,lively v he h (hp hx) hm⟩
     intro ht; rw [activeR,ht]; exact Builder.bolts (q.builder s)
   next hi=>
   have ht:= T.size1
   refine ⟨tile_zero _ (by linarith) _,fun _=>shelf_zero _,fun _=>?_,?_⟩
   · unfold Axis.pinned Axis.wmask; ext; split<;>rfl
   · have hZ : 1≤allowance s.gap M (q.key s) := StepKey.inactive (q.key s)
                 (by unfold onQ at hi; unfold Est.active; simpa using hi)
     have hc:=q.canon s h T
     obtain ⟨h1,h2,h3,h4,h5,h6⟩:=h
     have hh:= (q.plan s).zero_root (D:=width s.P) (s.fits he (show q.u≤ s.roof by omega))
                           (he.count _ h1) hc T.size1
     apply hh.trans
     have hx:=T.four
     have hh1 : T.bank ≤ T.bank*allowance s.gap M (q.key s) := by nlinarith
     unfold Tonic.bank at *; linarith

end Quest
end
end ExactDerandomization.Net

end

section

namespace ExactDerandomization.Net
noncomputable section
open Est Hie At Analysis Buf Finset Tuned

set_option synthInstance.maxSize 4096
variable {n:ℕ} [Fact n.Prime] {s:Scene n} {q:Peek} {M:ℕ} {r: Roll n} {T:Tonic s.P}
namespace Peek

lemma owedPeek (v:Purse T) (h:s.SetUp) (hr:Tuned T M r) (hp:q.ready s M) :
   (q.weave s r).Owes (q.stair s M) ((q.plan s).narrowed 0) false v.toll := by
   unfold weave
   cases he:q.ask
   · cases hc:q.i
     · refine stance v h _ rfl ?_ ?_ ?_
       · ext; simp [Flame.tail]
       · simp
       · simp; linarith [v.toll_ok]
     · next l=>
       apply stance v h _ rfl (home hc he)
       · intro t ht
         unfold roy at ht
         obtain ⟨ha,hb⟩:= mem_product.mp ht
         refine ⟨mem_singleton.1 ha,?_⟩
         unfold roy; dsimp only
         split
         · next hz=>exact ownsPrime v h hr hp hc hz
         next hz=>
         replace hb:=mem_range.1 hb
         exact ownsMix v h hr hp hc (by omega)
       · simp only [roy,card_product,card_singleton,one_mul,card_range,Nat.cast_mul,Nat.cast_ofNat]
         exact v.tollM
   · next k=>exact dueProbe v h hr hp he

lemma objective : (q.weave s r).lamp=ridge (q.pursue s) := by
    unfold weave; cases q.ask <;> try rfl
    cases q.i<;>rfl

lemma contentsPeek (v:Purse T) (h:s.SetUp) (hM:0<M→Tuned T M r)
   (hp:q.ready s M) (hw:v.askFor s.gap):
    let u:=(current s r M).outV q
    (∀ p i,in01 (u p i)) ∧ (q.plan s).von (fun p i=>q.wear s p i-u p i)≤ T.bank*allowance s.gap M (q.key s) := by
    let d:=q.plan s
    dsimp only [current]; split
    · next hi=>
      let a:=q.activeV s r M; let p:= q.wear s
      have h0:0<M:= by by_contra! he; simp [onQ,Nat.eq_zero_of_le_zero he] at hi
      have ht:= Axis.drawn d (owedPeek v h (hM h0) hp) (f:=q.pursue s)
                          (fun x _=> q.gaze h x) (fun x hx=> by rw [objective]; simp [ridge])
      refine ⟨Axis.boundsC _ _ _,?_⟩
      let f:Paint n:=fun s i=> p s i-a s i
      have he : d.von f=d.von (fun s i=> a s i-p s i) := by
         have he: (fun s i=> a s i-p s i)=fun s i=> -f s i:=by unfold f; ext; ring
         rw [he]; exact (Meter.Lneg ..).symm
      change d.von f≤_
      rw [he]
      apply ht.trans
      let A:=allowance s.gap M (q.key s)
      change 6*((4*v.toll^2)*(A*dry s.gap)) ≤ _
      have hc:0≤A:=(StepKey.allow_p ..).le
      have he:= mul_le_mul_of_nonneg_right hw.2.2 hc
      change _ ≤ T.bank*A
      linarith
    next hi=>
    refine ⟨fun i _=>by norm_num [in01],?_⟩
    have he := h.count q.i hp.1
    have h0 := d.tvh (p:= q.wear s) (s.fits h (show q.u≤ s.roof by obtain ⟨_,_,_,_⟩:=hp; omega)) he (fun i x=> q.gaze h x)
    simp only [sub_zero]
    apply h0.trans
    have hv : 1≤allowance s.gap M (q.key s) := StepKey.inactive (q.key s)
                 (by unfold onQ at hi; unfold Est.active; simpa using hi)
    nlinarith [T.four]

end Peek

lemma origin0 (s:Scene n) : forecast s 0 = Tick.empty n := by
   unfold forecast current
   simp only [Tick.empty, onQ,Nat.zero_div,Nat.not_lt_zero,decide_false, Bool.false_eq_true,ite_false]

/-- Error and finite-index bounds of the actual (no fingerprint)
estimates by statistical budget recursion. -/
lemma error_estimate (v:Purse T) (h:s.SetUp) (hw:v.askFor s.gap) (M) :
    Trust T M (forecast s M) := by
    induction M using Nat.strong_induction_on with
    | h M ih=>
      have hp (hr:0<M) : Tuned T M (rolls s M) := by
          refine ⟨hr,?_,by rw [vault _ _ hr,origin0]⟩
          intro m hm; rw [vault _ _ hm]; exact ih m hm
      exact ⟨fun {q} hr=> Quest.contents v h hr hp hw,fun {q} hr=> Peek.contentsPeek v h hp hr hw⟩

end
end ExactDerandomization.Net

end

end OAI
