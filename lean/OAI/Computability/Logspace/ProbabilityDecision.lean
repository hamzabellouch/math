import OAI.Computability.Logspace.ConfigurationGraph
import OAI.Computability.Logspace.HierarchicalEstimator

namespace OAI

/-!
Conditioning at the initial configuration and deterministic separation of acceptance probabilities.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

namespace ExactDerandomization.Stage
noncomputable section
open Hie Est At Analysis Buf Net Finset

/-- constants chosen once for the analytic part of the algorithm. -/
structure Wares where
    p : Const
    A0 : ℕ
    ell : ℕ

namespace Wares

def density (w:Wares) (B : ℕ) := (1+w.p.M)*B
def levels (w:Wares) (B:ℕ):=2^w.density B
def tolls (w:Wares) (B : ℕ):=4*B+w.A0*(1+coreR w.p B)
def top (w:Wares) (B : ℕ):=8*(w.tolls B+w.density B+2*B)
def ceiling (w:Wares) (B : ℕ):= w.top B+B + w.density B+1
structure Proof (w:Wares) where
   T : Tonic w.p
   v : Purse T
   credit : v.askFor w.A0
   wind : Wind 18 w.ell

lemma choose : ∃ w:Wares,Nonempty w.Proof := by
   obtain ⟨p⟩:= Hie.exists_const
   obtain ⟨t⟩:= tonic_up p
   obtain ⟨v⟩:= finance t
   obtain ⟨a,h⟩:= v.credit
   obtain ⟨l,hl⟩:= find_lam 18
   exact ⟨⟨p,a,l⟩,⟨⟨t,v,h,hl⟩⟩⟩

end Wares

namespace Raw
variable {q w h : ℕ} (P : Base.Source q w h) (x : Word) (u : Wares)
def H : Hie.Prize := ⟨⟨u.p,0,P.dom x,fun i j=>↑(P.S x i j)⟩,
                      fun i=>↑(P.reward x i),fun i=>↑(P.pr x i)⟩

lemma honestly : (H P x u).Correct := by
   let Q:=H P x u
   change Q.Correct; refine ⟨?_,fun i=>?_,fun i=>?_,?_⟩
   · constructor
     · intro i j; change 0≤(P.S x i j:ℝ); exact_mod_cast (P.S_nonneg x i j)
     · intro i j; change (P.S x i j:ℝ) ≤1*rate 0; rw [rate0,one_mul]; exact_mod_cast P.S_le x i j
     · intro i; change ∑ j∈P.dom x,(P.S x i j:ℝ)≤ 1
       exact_mod_cast P.S_sub x i
     intro i j hi
     change 0< (P.S x i j:ℝ) at hi
     have he:=(P.S_pos (x:=x) (n:=i) (j:=j)).1 (by exact_mod_cast hi)
     have ht b (e : P.next x i b=some j): i∈P.dom x ∧ j∈P.dom x∧i<j :=
       ⟨P.mem (P.steps_to e).1,P.mem (P.steps_to e).2.2.1,P.forward e⟩
     rcases he with h|h <;> exact ht _ h
   · change 0≤(P.reward x i:ℝ); unfold Base.Source.reward; split <;> norm_num
   · have hp:=P.bounded x (P.clock x) i
     change (0:ℝ)≤ (P.pr x i:ℝ) ∧ (P.pr x i:ℝ)≤1
     unfold Base.Source.pr; exact_mod_cast hp
   ext i
   have ht:=P.pr_eq x i
   rw [P.avg_S] at ht
   change (P.pr x i:ℝ)= (P.reward x i:ℝ)+∑ j∈P.dom x,(P.S x i j:ℝ)*(P.pr x j:ℝ)
   exact_mod_cast ht

lemma fits (e : P.Space) : P.first x∈ (H P x u).P.S := P.mem_first e x
lemma answer (e : P.Space) :
    (H P x u).v (P.first x) = (P.mach.acceptanceProbability x (P.clock x):ℝ) :=
    congrArg (fun t:ℚ=>(t:ℝ)) (P.fair e x)

end Raw

variable {q w h n : ℕ} [Fact n.Prime]
structure Matter (q w h n :ℕ) [Fact n.Prime] where
    P : Base.Source q w h
    w0 : Wares
    x : Word
    B : ℕ

namespace Matter
variable (m : Matter q w h n)
def s : Scene n :=
   ⟨Raw.H m.P m.x m.w0,m.w0.levels m.B, m.B,m.w0.ceiling m.B, m.w0.A0,m.w0.ell⟩
def x0 := m.P.first m.x
def i := m.s.H.child m.x0 m.B
def view := prizep m.B m.B
def top := m.w0.top m.B
def d := m.view.plan m.s

def ready (e:m.w0.Proof) :=
   6 ≤ m.B ∧ m.P.size m.x≤ 2^m.B∧ e.T.bank ≤ Est.box m.B ∧
               m.w0.p.M<n ∧ 2^m.s.roof≤n
lemma cseq {p:m.w0.Proof} (he:m.ready p) {k : ℕ} (h:k≤ m.B) :
      (m.s.stage k).S ⊆ range (m.w0.levels m.B) := by
   have hk (j : ℕ) : (m.s.stage j).S ⊆ range (2^m.B*m.w0.p.M^j) := by
      induction j with
      | zero=>
        change range (m.P.size m.x) ⊆ range _
        simpa using range_mono he.2.1
      | succ j ih=>
        intro x hx
        rw [m.s.mature,Stg.next] at hx
        obtain ⟨y,hv,i,hu,rfl⟩:=repr_copy hx
        have hl:=mem_range.1 (ih hv)
        let M:=m.w0.p.M
        have hM:(m.s.stage j).p.M=M:=by rw [m.s.aligned]; rfl
        apply mem_range.2
        rw [hM]; rw [hM] at hu
        unfold radix; rw [pow_succ]
        change i+M*y<2^m.B*(M^j*M)
        nlinarith
   apply (hk k).trans (range_mono ?_)
   let M:=m.w0.p.M
   have he:M≤2^M:= le_trans (by omega) (exp_big M)
   change 2^m.B*M^k ≤ 2^((1+M)*m.B)
   rw [add_mul,pow_add,pow_mul,pow_mul]
   gcongr <;> first | omega | positivity | exact Nat.one_le_pow M 2 (by omega)
lemma lineup {p:m.w0.Proof} (he:m.ready p) : m.s.SetUp := by
   refine ⟨Raw.honestly ..,rfl,he.2.2.2.1,he.2.2.2.2,
        fun i hi=> le_trans (card_le_card (m.cseq he hi)) (by simp [s]),fun i hi=>?_,p.wind⟩
   apply (m.cseq he hi).trans (range_mono ?_)
   apply le_trans _ he.2.2.2.2
   change 2^m.w0.density m.B ≤ 2^(m.w0.top m.B+m.B+m.w0.density m.B+1)
   exact Nat.pow_le_pow_right (by omega) (by omega)

lemma identity {p:m.w0.Proof} (he:m.ready p) :
    |m.s.H.v m.x0-m.view.pursue m.s m.i| ≤ 1/32 := by
   let C:=m.s.H
   let c:=m.B
   have hh : C.P.i=0:= rfl
   have hs := m.lineup he
   have hk:C.Correct:=hs.correct
   have hp : 2^(C.P.i+c) ≤ n := by
       rw [hh,zero_add]
       apply m.s.fits hs
       change c≤ m.w0.ceiling m.B; unfold c Wares.ceiling; omega
   have hx:= C.finish n hk c hp m.x0
   change |C.v _-(C.iterate n c).W (C.child m.x0 c)| ≤ _
   rw [abs_of_nonneg hx.1]; apply hx.2.trans; rw [hh,zero_add]
   have hZ : C.P.S.card ≤ 2^m.B := by
       change (range _).card≤_
       rw [card_range]; exact he.2.1
   apply le_trans (b:=(Est.box c)^2*rate c)
   · apply mul_le_mul_of_nonneg_right _ (rate_pos _).le
     push_cast
     have hR : (C.P.S.card:ℝ)≤2^c:=by exact_mod_cast hZ
     unfold Est.box
     nlinarith [show 0≤(2:ℝ)^c by positivity]
   rw [rr,show (Est.box c)^2*dry c^4=dry c^2 from ?_]
   · have he1 : 0≤dry c:= (dry0 _).le
     have ht:= dry_mono (show 6≤c from he.1)
     norm_num [dry,Est.box] at ht
     unfold dry Est.box at *
     nlinarith
   have he:= unify c
   linear_combination (norm := ring_nf) ((Est.box c*dry c)+1) * dry c^2 * he

lemma rank_allow :
    allowance m.s.gap m.top (m.view.key m.s) =
       dry (m.w0.density m.B) * dry m.B ^2 := by
   let w:=m.w0; let B:=m.B
   change dry (8*(w.tolls B+w.density B+2*B)/8) *
           Est.box (2*B+2*B+w.A0*(1+coreR w.p B+ 0))= _
   have ht : 2*B+2*B+w.A0*(1+coreR w.p B+0)=w.tolls B:=by unfold Wares.tolls; ring
   rw [ht,Nat.mul_div_cancel_left _ (by omega),dryP,dryP,Nat.mul_comm 2,dryM]
   change (dry (w.tolls B)*_ * _)*Est.box (w.tolls B)=dry _*_
   rw [show ∀ x y z v:ℝ,(x*y*z)*v=x*v*y*z by intros; ring,reunite,one_mul]

end Matter
end
end ExactDerandomization.Stage

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Stage
noncomputable section
open Hie Est At Analysis Buf Net Finset

variable {q w h n : ℕ} [Fact n.Prime]
namespace Matter
variable (m : Matter q w h n) {p : m.w0.Proof}
abbrev oracleV : Paint n :=
   (Net.forecast m.s m.top).outV m.view
abbrev polls (u : Pool n) := hit m.B (↑m.i:ZMod n) u.1

lemma reachesB : m.view.ready m.s m.top := by
   unfold view Peek.ready prizep
   refine ⟨le_rfl, le_rfl, ?_, trivial⟩
   unfold s Wares.ceiling top
   dsimp only
   omega

lemma origin (h:m.P.Space) : m.i∈m.d.S :=
   Prize.reach n m.s.H m.B (m.P.mem_first h m.x)
lemma designate {f:Paint n} (h:m.P.Space) (hr:m.ready p) :
    |m.d.vm f m.i| ≤ (m.s.N:ℝ)*m.d.von f := by
   let d:=m.d
   let P:=pct n d.u
   let a : ℝ:=d.N
   let x:=m.i
   let k:= d.vm f x
   have hu : d.u=m.B :=rfl
   have heB : 2^d.u≤n:= by
       rw [hu]
       have he:= m.lineup hr
       apply m.s.fits he

       change m.B ≤ m.w0.ceiling _; unfold Wares.ceiling; omega
   have hx := m.origin h
   have hF: k^4 ≤ d.vm (fun s i=> f s i^4) x := by apply av_four_le
   have hA:a≥1:=by
       change (1:ℝ) ≤ (2^(m.w0.density m.B):ℕ)
       exact_mod_cast (show 0< (2^(m.w0.density m.B):ℕ) by positivity)
   have ht i : 0≤ d.vm (fun s i=>f s i^4) i := av_nonneg _ (by intros; positivity)
   have hR : 0< rate d.u:=rate_pos _
   have hp : rate d.u ≤ P:=(pct_bounds heB).1
   let u:=scaleM d.N d.u
   have hs :
      u*P*k^4 ≤d.von f^4 := calc
      _ ≤ u*(P*(d.vm (fun s i=>f s i^4) x)):=by
            have hv := mul_le_mul_of_nonneg_left hF
               (mul_nonneg (scaleM_nn d.N d.u) (hR.le.trans hp))
            dsimp only [u]; linarith
      _ ≤ _:= by
         rw [d.von_four,d.vpivot]
         apply mul_le_mul_of_nonneg_left _ (scaleM_nn ..)
         exact single_le_sum (f:=fun i=>P*(d.vm (fun s i=>f s i^4) i))
                    (fun i _=>mul_nonneg (hR.le.trans hp) (ht i)) hx
   have ha : 0<a*rate d.u:=mul_pos (by linarith) hR
   have he : a*(u*P*k^4) ≥ k^4 := by
      have hN:0<(d.N:ℝ) := by change 0<a; linarith
      unfold u scaleM a
      field_simp
      nlinarith [mul_le_mul_of_nonneg_right hp (show 0≤k^4 by positivity)]
   change |k| ≤ a*d.von f
   have hu0 :=d.vn0 f
   conv_lhs=>rw [← four_fourth (abs_nonneg _)]
   conv_rhs=> rw [← four_fourth (show 0≤a*d.von f by positivity)]
   rw [Meter.abs4,mul_pow]
   apply fourth_mono
   have he0:a≤a^4:=by simpa using pow_le_pow_right₀ hA (show 1≤(4:ℕ) by omega)
   exact le_trans he ((mul_le_mul_of_nonneg_left hs (by linarith :0≤a)).trans
         (mul_le_mul_of_nonneg_right he0 (by positivity)))

set_option maxHeartbeats 500000 in
lemma designate_est (h:m.P.Space) (hr:m.ready p) :
    |m.view.pursue m.s m.i-m.d.vm m.oracleV m.i| ≤ 1/32 := by
   have he:=m.lineup hr
   have hs : Trust (s:=m.s) p.T m.top (Net.forecast m.s m.top) := error_estimate (s:=m.s) p.v he p.credit _
   have hv := hs.v m.reachesB
   let u:=m.view.wear m.s
   let F:= fun (s:Pool n) (i:ℕ)=> u s i-m.oracleV s i
   have hx := m.designate (f:=F) h hr
   unfold F at hx; rw [Axis.vmean_sub] at hx
   have hh:m.d.vm u=m.view.pursue m.s:=Axis.vdet ..
   rw [hh] at hx
   apply hx.trans
   have hT :=mul_le_mul_of_nonneg_left hv.2 (show (0:ℝ)≤ m.s.N by positivity)
   apply hT.trans
   rw [m.rank_allow]
   let d:=m.w0.density m.B
   have hd : (m.s.N:ℝ)=Est.box d := by change ((2^d:ℕ):ℝ)=_; simp [Est.box]
   rw [hd]
   have hu : Est.box d * (p.T.bank * (dry d * dry m.B^2))=p.T.bank*dry m.B^2 := by
      have hh:= unify d
      linear_combination (norm := ring_nf) p.T.bank*dry m.B^2*hh
   change Est.box d * (p.T.bank*(dry d*dry m.B^2)) ≤ _
   rw [hu]
   calc p.T.bank * dry m.B^2 ≤ Est.box m.B*dry m.B^2 := by gcongr; exact hr.2.2.1
        _ = dry m.B := by rw [pow_two,← mul_assoc,unify,one_mul]
        _ ≤ _:= (dry_mono hr.1).trans (by norm_num [dry,Est.box])

lemma place (f:Pool n→ℝ) :
    av (fun s:Pool n=> if m.polls s then f s else 0)=
        pct n m.B *m.d.vm (fun s _=>f s) m.i := by
   let P (u : Pool n) := hit m.B (↑m.i:ZMod n) u.1
   have ht:= @Env.two_cond n 0 _ m.B 0 (m.i:ZMod n) 0 f
   simp only [Env.mask,allhit,and_true,pct_c0,mul_one] at ht
   exact ht

def jury (f:Pool n→ℝ) := m.d.vm (fun s _=>f s) m.i
lemma yard (f:Pool n→ℝ)
    (h : ∀ s,m.polls s → |f s-m.oracleV s m.i| ≤ 1/32) :
    |m.jury f-m.d.vm m.oracleV m.i| ≤ 1/32 := by
   unfold jury Axis.vm Env.cond
   let o:Env.Slice n m.B 0 0→Pool n :=
                  Env.outward m.B 0 (m.i:ZMod n) 0
   have hh (u : Env.Slice n m.B 0 0) := h (o u) (Env.hits ..).1
   let v u:=f (o u)-m.oracleV (o u) m.i
   have he : -(1/32:ℝ) ≤ av v ∧ av v≤1/32 := by
      refine ⟨?_,?_⟩
      · refine le_trans ?_ (av_mono (g:=v) (f:=fun _=> -(1/32:ℝ)) (fun i=>(abs_le.1 (hh i)).1))
        rw [av_const]
      refine le_trans (av_mono (f:=v) (g:=fun _=> (1/32:ℝ)) (fun i=>(abs_le.1 (hh i)).2)) ?_
      rw [av_const]
   unfold v at he; rw [av_sub] at he; rw [abs_le]; exact he

def evidence (f: Pool n → ℝ) := m.jury f
lemma probes (h:m.P.Space) (hr:m.ready p) (f:Pool n→ℝ)
    (he: ∀ s,m.polls s → |f s - m.oracleV s m.i|≤1/32) :
    |(m.P.mach.acceptanceProbability m.x (m.P.clock m.x):ℝ)-m.evidence f| < 1/8 := by
   rw [← Raw.answer _ _ m.w0 h]
   have h1:= m.identity hr; have h2:= m.designate_est h hr
   have h3 := m.yard f he
   change |m.s.H.v m.x0-m.jury f| < 1/8
   rw [abs_le] at *; rw [abs_lt]
   constructor <;> linarith [h3.1,h3.2,h1.1,h1.2,h2.1,h2.2]

/-- Compare arithmetic rather than doing probability tests. -/
lemma tally_eq (f:Pool n→ℝ) :
    (∑ s∈ univ.filter (fun s:Pool n=>m.polls s),f s) =
        ((univ.filter (fun s:Pool n=>m.polls s)).card:ℝ) * m.evidence f := by
   let S:=univ.filter fun s:Pool n=>m.polls s
   have he (f: Pool n→ ℝ) : ∑ s∈S,f s=
          (Fintype.card (Pool n):ℝ)*(pct n m.B * m.jury f) := by
      rw [show m.jury f=m.d.vm (fun s _ => f s) _ from rfl,← m.place f,av_card]; exact sum_filter ..
   have hi := he (fun _=>1)
   simp only [sum_const,nsmul_eq_mul,mul_one] at hi
   have hx : m.jury (fun _=>1)=1:= congrFun (m.d.vdet (n:=n) (fun _=>1)) m.i
   rw [hx,mul_one] at hi
   change _=(S.card:ℝ)*_
   rw [he,hi,mul_assoc]; rfl
lemma quorum :
    0<(univ.filter fun s:Pool n=>m.polls s).card := by
   apply card_pos.mpr
   let P:=Env.Slice n m.B 0 0
   have hp:Nonempty P:=by unfold P; infer_instance
   obtain ⟨x⟩:=hp
   exact ⟨Env.outward _ _ (↑m.i:ZMod n) 0 x,mem_filter.mpr ⟨mem_univ _,
                          (Env.hits ..).1⟩⟩
end Matter

end
end ExactDerandomization.Stage

end

end OAI
