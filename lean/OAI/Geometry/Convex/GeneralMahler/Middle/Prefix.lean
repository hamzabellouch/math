import OAI.Geometry.Convex.GeneralMahler.Middle.Trap
import OAI.Geometry.Convex.GeneralMahler.Middle.Identity

namespace OAI
/-! Vertex checking via prefix integrals. -/
open Set Filter MeasureTheory Real
namespace GeneralMahler.SCal.Mid
open Grid Nodes Tag Profile Segment SE Jet Cert Cert.IV
def ptF (n:Nat):Ft→IV
  | Ft.K=>GB (A n).k-bd 100
  | Ft.C=>GB (A n).c-bd (-4200)
  | Ft.Q=>GB (A n).q-bd 1600
  | Ft.J=>GB (A n).u
  | Ft.V=>GB (A n).v
  | Ft.M=>IV.sq (GB (A n).q-bd 1600)
def pz (n:ℕ):IV:=GB (A n).x
lemma pv (h:NG)(n:Nat)(he:n ≤ 720): zn n∈ pz n∧∀ i:Ft,i.f (zn n)∈ ptF n i := by
  obtain ⟨ha,hc,hv,hq,hu,ht⟩:= (h.good n he).1
  have hj : k0∈ bd 100 := by convert mbd 100; norm_num [k0]
  have hp:c0∈ bd (-4200):= by convert mbd (-4200);norm_num [c0]
  have hb:q0 ∈ bd 1600:=by convert mbd 1600; norm_num [q0]
  refine ⟨ha,fun i=>?_⟩; cases i
  · exact msub hc hj
  · exact msub hv hp
  · exact msub hq hb
  · exact hu
  · exact ht
  exact msq (msub hq hb)
def aStep (n:ℕ)(p:Ft):IV:= (pz (n+1) - pz n)*((ptF n p+ptF (n+1) p)/(2:IV))
abbrev PrefixC:= ℕ→Ft→IV
def Works (B:PrefixC):Prop:=
   (∀ p, SubB 0 (B 0 p)=true) ∧ ∀ n:Nat,n<720→∀ p,SubB (B n p+aStep n p) (B (n+1) p)=true
lemma stays (h:NG)(B:PrefixC)(g:Works B) (n:Nat)(hn:n ≤720)(p:Ft): accum p n∈B n p:=by
  induction n with
  | zero=> exact subB mz (g.1 _)
  | succ n ih=>
    have hx:= pv h n (by omega);have hy:= pv h _ hn
    have hi:rectA p n∈aStep n p:= mmul (msub hy.1 hx.1) (mdiv (madd (hx.2 _) (hy.2 _)) mtwo)
    exact subB (madd (ih (by omega)) hi) (g.2 _ (by omega) _)
def signF {α} [Neg α](b:Bool)(x:α):α:= if b then -x else x
def fo (p:Ft):Bool:=match p with|.V=>true|_=>false
def sFt {α} [Neg α](b:Bool)(p:Ft)(x:α):α:= signF (b && fo p) x
def sP {α} [Neg α](b:Bool)(p:Ft)(x:α):α:= signF (b && !fo p) x

lemma fFlip (b:Bool)(p:Ft)(x:ℝ): p.f (signF b x) = sFt b p (p.f x) := by
  cases b
  · simp [signF,sFt]
  cases p <;> simp only [signF,sFt,fo,Bool.and_self,Bool.true_and,ite_true,ite_false,Bool.false_eq_true]
  · simp only [Ft.f]; rw [Keven]
  · simp only [Ft.f]; rw [Ceven]
  · simp only [Ft.f]; rw [Qeven]
  · apply uc_ref
  · apply us_ref
  simp only [Ft.f];rw [Qeven]
lemma integralFneg (p:Ft)(x:ℝ): areaP p (-x)=sP true p (areaP p x):=by
  have hi(t:ℝ) : p.f (-t)= sFt true p (p.f t):=fFlip true p t
  have he:=intervalIntegral.integral_comp_neg p.f (a:=0) (b:=x)
  unfold areaP
  rw [intervalIntegral.integral_symm]
  simp only [neg_zero] at he
  rw [← he]; simp_rw [hi]
  unfold sFt sP signF
  cases fo p <;> simp

lemma sumNeg (h:NG)(p:Ft) (n m:ℕ):
    |areaP p (zn m)-areaP p (-zn n)-(accum p m-sP true p (accum p n))| ≤
      (zn m- -(zn n))*perE := by
  have ht(k:Nat) : |areaP p (zn k)-accum p k|≤ zn k *perE := by
    have he:=sum_pair h p 0 k (by omega)
    simpa [accum,areaP,zN0] using he
  have h0:=ht n; have h1:=ht m
  rw [integralFneg]
  unfold sP signF
  cases fo p
  · simp only [Bool.not_false,Bool.and_self,↓reduceIte]
    rw [abs_le] at h0 h1 ⊢
    constructor<;> linarith [h0.1,h0.2,h1.1,h1.2]
  simp only [Bool.not_true,Bool.true_and,↓reduceIte,Bool.false_eq_true]
  rw [abs_le] at h0 h1 ⊢
  constructor<;>linarith [h0.1,h0.2,h1.1,h1.2]

def EB:IV:= 1/(IV.c 40000)
def mj (b:Bool)(i j:Nat)(B:PrefixC)(p:Ft):IV:=
  (B j p - sP b p (B i p))/(pz j-signF b (pz i)) + IV.span (-EB) EB

lemma mj_ok (h:NG)(b:Bool)(p:Ft)(B:PrefixC)(g:Works B){i j:Nat}(ha:i ≤720)(hb:j ≤720)
    (he: signF b (zn i)<zn j): bav p.f (signF b (zn i),zn j)∈mj b i j B p:=by
  let d:= zn j-signF b (zn i);let c:=accum p j-sP b p (accum p i)
  let f:=bav p.f (signF b (zn i),zn j)
  have hp:0<d:=sub_pos.mpr he
  have hv: |d*f-c| ≤ d*perE:=by
    unfold d f c
    rw [← area_pair h]
    cases b
    · exact sum_pair h p i j ((zNm.lt_iff_lt.mp he).le)
    exact sumNeg h p i j
  have eh: |f-c/d|≤perE:=by
    rw [abs_le] at hv ⊢
    field_simp
    obtain ⟨ht,he⟩:=hv;constructor <;> nlinarith
  have hs (a:Bool) (x:ℝ)(u:IV)(hx:x∈u): signF a x∈signF a u:= by
    cases a;exact hx; exact mneg hx
  have hl:c/d∈(B j p - sP b p (B i p))/(pz j-signF b (pz i)):=
    mdiv (msub (stays h B g j hb p) (hs _ _ _ (stays h B g i ha p)))
      (msub (pv h _ hb).1 (hs b _ _ (pv h _ ha).1))
  have he: perE∈EB:=mdiv mo (show (40000:ℝ)∈IV.c 40000 from mc 40000)
  apply (show c/d+(f-c/d)=f by ring) ▸ madd hl (span_conv (mneg he) he (abs_le.mp eh).1 (abs_le.mp eh).2)

def ins (B:PrefixC)(b:Bool)(i j:ℕ):Fin 3→Ft→IV:=fun n p=>
  if n=0 then sFt b p (ptF i p) else if n=1 then ptF j p else mj b i j B p
def dotE (B:PrefixC)(b:Bool)(i j:ℕ):IV:=Op.boxE (ins B b i j) Op.E
lemma dot_ok(h:NG)(B:PrefixC)(g:Works B)(b:Bool)(i j:ℕ)(hi:i ≤720)(hj:j ≤720)
    (h':signF b (nd i)<nd j):
    Fval (signF b (nd i)) (nd j) ∈ dotE B b i j:= by
  have he: xs (signF b (nd i))=signF b (zn i):=by cases b;rfl;exact x_neg _
  have hx := x_mono h'
  rw [he] at hx
  apply Op.bval (k:=inp _ _) _ _
  intro n p
  unfold inp ins
  split_ifs with hf hg
  · unfold Ft.g liftF
    rw [he,fFlip]
    have hi:= (pv h _ hi).2 p
    unfold sFt signF
    split
    exact mneg hi
    exact hi
  · exact (pv h _ hj).2 p
  rw [forB h,he]
  exact mj_ok h b p B g hi hj hx
end GeneralMahler.SCal.Mid

end OAI
