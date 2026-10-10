import OAI.Computability.Logspace.AffineSampling
import OAI.Computability.Logspace.CompressionBounds
import OAI.Computability.Logspace.ProbabilityAtoms

namespace OAI

/-!
Fourth-root norms and integrated error estimates for the compressed estimator.

From OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*.
-/

set_option autoImplicit true

section

/-! Dyadic estimates, with nonnegative integer exponents only. -/
namespace ExactDerandomization.Est
noncomputable section
open Analysis At Hie Buf Finset

def box (i : ℕ) : ℝ := 2^i
def dry (i : ℕ) : ℝ := (box i)⁻¹
lemma box0 (i) : 0<box i := by unfold box; positivity
lemma dry0 (i) : 0<dry i := by unfold dry; have := box0 i; positivity
lemma box_one (i) : 1≤box i := by unfold box; exact one_le_pow₀ (by norm_num)
lemma dry_one (i) : dry i ≤ 1 := by unfold dry; exact inv_le_one_of_one_le₀ (box_one i)
lemma boxP (i j : ℕ) : box (i+j)=box i*box j := pow_add ..
lemma dryP (i j : ℕ) : dry (i+j)=dry i*dry j := by simp only [dry,boxP,mul_inv]
lemma boxM (i j) : box (i*j)=(box i)^j := pow_mul ..
lemma dryM (i j) : dry (i*j)=(dry i)^j := by simp only [dry,boxM,inv_pow]
lemma unify (i) : box i * dry i=1 := by unfold dry; rw [mul_inv_cancel₀ (box0 i).ne']
lemma reunite (i) : dry i*box i=1 := by rw [mul_comm,unify]
lemma box_mono : Monotone box := by
   intro a b e; unfold box; gcongr; linarith
lemma dry_mono : Antitone dry := by
   intro a b e; unfold dry; exact inv_anti₀ (box0 a) (box_mono e)

lemma exp_big (n : ℕ) : n+1≤2^n := by
   induction n with
   | zero=>simp
   | succ n ih=> rw [pow_succ]; omega
lemma box_big (n : ℕ) : (n:ℝ)+1≤box n := by unfold box; exact_mod_cast exp_big n

lemma invsum (n : ℕ) : ∑ i∈ range n,dry i = 2-2*dry n := by
   induction n with
   | zero=> norm_num [dry,box]
   | succ n ih=> rw [sum_range_succ,ih,dryP]
                 norm_num [dry,box]; ring
lemma thinSum (F : Domain) : ∑ i∈F,dry i ≤2 := by
   let n:=1+∑ i∈F,i
   have he : F⊆range n := by
      intro i hi; have hs:i ≤ ∑ i∈F,i:=single_le_sum (f:=fun i=>i) (fun _ _=> Nat.zero_le _) hi
      apply mem_range.mpr; dsimp only [n]; omega
   apply le_trans (sum_le_sum_of_subset_of_nonneg he (fun i hi _=>(dry0 i).le))
   rw [invsum]; linarith [dry0 n]

/-- d-index of slack group number i, descending. -/
def gapD (L i : ℕ) := 2^(L-1-i)
lemma gap_end (L : ℕ) : gapD L (L-1)=1 := by simp [gapD]
lemma gapD_pos (L i) : 1≤gapD L i :=  show 0<gapD L i from pow_pos (by omega) _
lemma gapD_succ {L i} (hi : i+1<L) : gapD L i=gapD L (i+1)*2 := by
   unfold gapD
   rw [show L-1-i=L-1-(i+1)+1 by omega,pow_succ]
lemma gapD_mono {L} : Antitone (gapD L) := by
   intro i j h; unfold gapD
   exact Nat.pow_le_pow_right (by omega) (by omega)
lemma gapD_tail {L i} (hi : i<L) : L-i ≤ gapD L i := by
   apply le_trans _ (exp_big (L-1-i)); omega

lemma binsum (L : ℕ) : ∑ i ∈ range L, dry (gapD L i) ≤2 := by
   rw [← sum_image (f:=dry)]
   · apply thinSum
   · intro i hi j hj e; replace hi:=mem_range.1 hi; replace hj:=mem_range.1 hj
     rcases lt_trichotomy i j with hs|hs|hs
     · have h := gapD_succ (L:=L) (i:=i) (by omega)
       have h1 : gapD L j ≤gapD L (i+1) := gapD_mono (by omega)
       have hh:=gapD_pos L i; omega
     · exact hs
     · have h := gapD_succ (L:=L) (i:=j) (by omega)
       have h1 : gapD L i ≤gapD L (j+1) := gapD_mono (by omega)
       have hh:=gapD_pos L j; omega
lemma cyclo {L i} (hi:i<L) : (32:ℝ)^(L-i) ≤ box (5*gapD L i) := by
   have hs:=gapD_tail hi
   unfold box; rw [pow_mul]
   norm_num; gcongr; norm_num

/-- Abstract compression exponent packet with abundant room for both
masked mean and false positives charges. -/
def fexpo (b : ℕ) := b+100
def cexpo (b K : ℕ) := fexpo b+b+10+K

def floorR (b L i : ℕ) := dry (fexpo b*gapD L i)
def capacity (b K L i : ℕ) := 2^(cexpo b K*gapD L i*4)
def liftB (b L i : ℕ) := box (b*gapD L i)
def decay (L i : ℕ) := dry (8*gapD L i)
def firm (b _ L i : ℕ) := dry ((b+10)*gapD L i)

lemma floor_pos (b L i) : 0<floorR b L i := dry0 _
lemma lift_one (b L i) : 1≤liftB b L i := box_one _
lemma decay_le (b L i) : decay L i≤ liftB b L i := le_trans (dry_one _) (lift_one ..)
lemma cap_pos (b K L i) : 0<capacity b K L i := pow_pos (by omega) _
lemma cap_K (b K L i) : K ≤ capacity b K L i := by
   apply le_trans _ (exp_big (cexpo b K*gapD L i*4))
   have he := gapD_pos L i; have ht : K≤ cexpo b K := by unfold cexpo; omega
   nlinarith
lemma cap_box (b K L i) : (capacity b K L i:ℝ)=box (cexpo b K*gapD L i)^4 := by
   simp only [capacity,box,Nat.cast_pow,Nat.cast_ofNat,pow_mul]

lemma forfeit (b K L i) :
   1≤ (capacity b K L i:ℝ)*(floorR b L i)^4*(firm b K L i)^4 := by
   rw [cap_box,← mul_pow,← mul_pow]
   apply one_le_pow₀
   let d:=gapD L i
   let s:=fexpo b*d+(b+10)*d
   have h : s ≤ cexpo b K*d:=by unfold s cexpo; grind
   unfold floorR firm
   rw [mul_assoc,← dryP]; change 1≤box _*dry s
   conv_lhs=> rw [← unify s]
   exact mul_le_mul_of_nonneg_right (box_mono h) (dry0 _).le
lemma feed_power (b K L i) :
   1 ≤ (capacity b K L i:ℝ)*floorR b L i*(firm b K L i)^4 := by
   have hs:= forfeit b K L i; apply le_trans hs
   gcongr
   exact le_trans (pow_le_pow_of_le_one (floor_pos ..).le (dry_one _)
                         (show 1≤ (4:ℕ) by omega)) (by rw [pow_one])

lemma floor_lift (b L i) : floorR b L i*liftB b L i ≤ dry (gapD L i) := by
   let d:=gapD L i
   unfold floorR liftB; rw [fexpo,add_mul,dryP,mul_right_comm, reunite, one_mul]
   apply dry_mono; omega
lemma firm_plain (b K L i) : firm b K L i*liftB b L i≤dry (gapD L i) := by
   unfold firm liftB; rw [add_mul,dryP,mul_right_comm,reunite,one_mul]
   apply dry_mono; omega
lemma firm_big (b K L i) : firm b K L i*box ((b+6)*gapD L i) ≤ dry (gapD L i) := by
   unfold firm; rw [show b+10=b+6+4 by omega, add_mul (b+6),dryP,mul_right_comm,reunite,one_mul]
   apply dry_mono; omega
lemma cyclone {L i} (hi : i<L) : (32:ℝ)^(L-i)*decay L i≤dry (gapD L i) := by
   apply le_trans (mul_le_mul_of_nonneg_right (cyclo hi) (dry0 _).le)
   change box _*dry (8*gapD L i)≤_
   let d:=gapD L i
   rw [show 8*gapD L i=5*gapD L i+3*gapD L i by omega,dryP,← mul_assoc,unify,one_mul]
   apply dry_mono; omega
lemma firm_tail (b K L i) (hi:i<L) :
    firm b K L i * ∑ j∈ Ico i L, (32:ℝ)^(L-j)*liftB b L j ≤ dry (gapD L i) := by
   let d := gapD L i; let C:=box ((b+5)*d)
   apply le_trans _ (firm_big b K L i)
   apply mul_le_mul_of_nonneg_left _ (dry0 _).le
   have he : ∀ j∈Ico i L,(32:ℝ)^(L-j)*liftB b L j ≤ C := by
      intro j hj
      obtain ⟨he,hj⟩:=mem_Ico.mp hj
      have hz : gapD L j ≤ d := gapD_mono he
      unfold C liftB; rw [add_mul,boxP,mul_comm (box (b*d))]
      exact mul_le_mul ((cyclo hj).trans (box_mono (by gcongr))) (box_mono (by gcongr))
             (box0 _).le (box0 _).le
   have hz : (L-i:ℕ) ≤ d:=gapD_tail hi
   have hn : ((L-i:ℕ):ℝ)≤box d :=
      le_trans (b:=(d:ℝ)) (by exact_mod_cast hz) (by linarith [box_big d])
   calc _ ≤ _ := sum_le_sum he
        _ = ((L-i:ℕ):ℝ)*C := by simp
        _ ≤ box d*C := mul_le_mul_of_nonneg_right hn (box0 _).le
        _ = _ := by unfold C; rw [← boxP]; dsimp [d]; congr 1; ring

lemma min_chill (b L i) : floorR b L i ≤dry (gapD L i)* dry 80 := by
   rw [← dryP]; apply dry_mono
   have hv := gapD_pos L i
   unfold fexpo; nlinarith
lemma first_bound (b L i) : floorR b L i ≤ 1/1024 := by
   have hg:= le_trans (min_chill b L i) (mul_le_mul_of_nonneg_right (dry_one _) (dry0 _).le)
   norm_num [dry,box] at hg; linarith
lemma totaldust (b L) : ∑ i∈range L,6*floorR b L i≤ At.small := by
   apply le_trans (b:=6*(∑ i∈range L,dry (gapD L i))*dry 80)
   · rw [mul_sum,sum_mul]; exact sum_le_sum fun i hi=>by rw [mul_assoc]; gcongr; apply min_chill
   have h := mul_le_mul_of_nonneg_right (binsum L) (dry0 80).le
   norm_num [dry,box,small,delta,A] at *; linarith

lemma freezeD (b L i : ℕ) (h : i+1<L) :
   floorR b L i=floorR b L (i+1)*floorR b L (i+1) := by
   simp only [floorR,gapD_succ h]
   rw [← dryP]; congr 1; ring

lemma lead_dust (b L i : ℕ) (hi:i<L) :
   ∑ j∈ range i,6*floorR b L j ≤floorR b L i/100 := by
   induction i with
   | zero=>simp; linarith [floor_pos b L 0]
   | succ i ih=>
     have hs := ih (by omega)
     rw [sum_range_succ]
     apply le_trans (add_le_add_left hs _)
     rw [freezeD b L i hi]
     nlinarith [first_bound b L (i+1),floor_pos b L (i+1)]

end
end ExactDerandomization.Est

end

section

/-! Measures used in the uncompressed and compressed comparisons. -/
set_option synthInstance.maxSize 2048
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Finset

variable {n w : ℕ} [Fact n.Prime]

abbrev X (n w : ℕ) := Env n w
abbrev src (S : Domain) (u : ℕ) (s : X n w) := retain u S s.1
abbrev dst (S : Domain) (a : ℕ) (s : X n w) := retain a S s.2.1

abbrev Vertex (n w : ℕ) := X n w → Vec
abbrev TableF (n w : ℕ) := X n w → Mat

def scaleM (N u : ℕ) := (N*rate u)⁻¹
lemma scaleM_nn (N u) : 0 ≤ scaleM N u := by unfold scaleM; have := rate_pos u; positivity

structure Axis where
   S : Domain
   N : ℕ
   u : ℕ
   a : ℕ

namespace Axis
variable (d : Axis)

def VM : Meter (X n w × ℕ) :=
   Meter.Scale (Meter.Along Meter.Avg (fun s=>Meter.Sum (src d.S d.u s)))
       (scaleM d.N d.u) (scaleM_nn ..)
def TM : Meter ((X n w × ℕ) × ℕ) :=
   d.VM.Along (fun (s,_)=>Meter.Sum (dst d.S d.a s))

def vi (f : Vertex n w) := d.VM.I fun (s,x)=> f s x
def ti (f : TableF n w) := d.TM.I fun ((s,x),y)=> f s x y
def von (f : Vertex n w) := d.VM.L fun (s,x)=> f s x
def ton (f : TableF n w) := d.TM.L fun ((s,x),y)=>f s x y
def terr (f g : TableF n w) :=
   d.ton (fun s i j=>fourth (f s i j)-fourth (g s i j))

lemma vi_apply (f : Vertex n w) :
    d.vi f=scaleM d.N d.u * av (fun s=>∑ i∈src d.S d.u s,f s i) := rfl
lemma ti_apply (f : TableF n w) :
    d.ti f=scaleM d.N d.u * av (fun s=>∑ i∈src d.S d.u s,
        ∑ j∈dst d.S d.a s,f s i j) := rfl
lemma collapse (f : TableF n w) :
    d.ti f = d.vi (fun s i => ∑ j∈dst d.S d.a s,f s i j) := rfl

lemma vi_mono {f g : Vertex n w} (e : ∀ s i, i∈src d.S d.u s → f s i≤g s i) :
    d.vi f≤d.vi g := by
  rw [vi_apply,vi_apply]
  exact mul_le_mul_of_nonneg_left (av_mono (fun i=>sum_le_sum (e i))) (scaleM_nn ..)
lemma ti_mono {f g : TableF n w} (e : ∀ s i j, i∈src d.S d.u s → j∈dst d.S d.a s →
                                     f s i j≤ g s i j) : d.ti f≤ d.ti g :=
   d.vi_mono fun s i hi=>sum_le_sum fun j hj=>e s i j hi hj

lemma conditional (f : TableF n w) :
    d.ti f=
      scaleM d.N d.u*∑ i∈d.S,∑ j∈d.S,
            pct n d.u*pct n d.a*Env.cond d.u d.a (↑i:ZMod n) (↑j:ZMod n)
                                   (fun s=>f s i j) := by
  have he (s:X n w) :
      ∑ i∈src d.S d.u s,∑ j∈dst d.S d.a s,f s i j=∑ i∈d.S,∑ j∈d.S,
       (if Env.mask d.u d.a (↑i:ZMod n) (↑j:ZMod n) s then f s i j else 0) := by
    unfold src dst retain Env.mask
    rw [sum_filter]
    apply sum_congr rfl; intro i hi
    rw [sum_filter]; split
    · next e=>simp [e]
    · next e=>simp [e]
  rw [ti_apply]; simp_rw [he, av_sum]
  congr! 2
  apply sum_congr rfl; intro j _
  apply Env.two_cond

lemma vi_const {S : Domain} (l : ℕ) :
    av (fun s:X n w=> (#(src S l s) : ℝ)) = #S*pct n l := by
  rw [av_prod]
  simp_rw [src,av_const]
  exact tally_av ..
lemma vi_one (hl:2^d.u ≤ n) (hc : d.S.card≤d.N) :
    d.vi (fun (_:X n w) _=> (1:ℝ)) ≤ 16 := by
  rw [vi_apply]
  simp only [sum_const,nsmul_eq_mul,mul_one,vi_const]
  obtain e|e:=Nat.eq_zero_or_pos d.N
  · simp [scaleM,e]
  have he:= (pct_bounds hl).2
  have hz : (0:ℝ)<d.N := by exact_mod_cast e
  have hv : (d.S.card:ℝ)≤d.N := by exact_mod_cast hc
  unfold scaleM
  rw [← div_eq_inv_mul, div_le_iff₀ (mul_pos hz (rate_pos _))]
  have hp := pct_pos (NeZero.pos n) d.u
  nlinarith [mul_le_mul_of_nonneg_left he (show 0≤(d.N:ℝ) by linarith)]

lemma von_four (f : Vertex n w) : d.von f^4=d.vi (fun i j=>f i j^4) := by rw [von,Meter.L4]; rfl
lemma ton_four (f : TableF n w) : d.ton f^4=d.ti (fun i j k=>f i j k^4) := by rw [ton,Meter.L4]; rfl

end Axis

lemma panel_const (k l) (x y : ℕ) (f : Analysis.Channel n→Analysis.Channel n→ℝ) :
  @Env.cond n w _ k l (↑x:ZMod n) (↑y:ZMod n) (fun s=> f s.1 s.2.1) =
    atP k (↑x:ZMod n) (fun i=>atP l (↑y:ZMod n) (fun j=>f i j)) := by
  unfold Env.cond atP; simp only [av_prod,Env.outward,av_const]

end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 2048
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Finset

variable {n w : ℕ} [Fact n.Prime]

namespace Axis
variable (d : Axis)
lemma tn0 (f : TableF n w) : 0 ≤ d.ton f := Meter.Lnn ..
lemma vn0 (f : Vertex n w) : 0 ≤ d.von f := Meter.Lnn ..
lemma tscale (f : TableF n w) (c) :
    d.ton (fun i j x=>c*f i j x) = |c| *d.ton f := Meter.Lmul ..
lemma vscale (f : Vertex n w) (c) :
    d.von (fun i j=>c*f i j) = |c| *d.von f := Meter.Lmul ..
lemma tplus (f g : TableF n w) :
    d.ton (fun i j x=>f i j x+g i j x) ≤ d.ton f+d.ton g := Meter.mink ..
lemma vplus (f g : Vertex n w) :
    d.von (fun i j=>f i j+g i j) ≤d.von f+d.von g := Meter.mink ..
lemma tseries {A : Type} (f : A → TableF n w) (S : Finset A) :
    d.ton (fun i j x=>∑ s∈S,f s i j x) ≤∑ s∈S,d.ton (f s) := by
    classical
    induction S using Finset.induction_on with
    | empty=>simp [ton,Meter.L,Meter.m4,Meter.I0,fourth]
    | @insert a S ha h=>
      simp only [sum_insert ha]
      exact le_trans (d.tplus (f a) _) (add_le_add_right h _)
lemma vseries {A : Type} (f : A → Vertex n w) (S : Finset A) :
    d.von (fun i j=>∑ s∈S,f s i j) ≤∑ s∈S,d.von (f s) := by
    classical
    induction S using Finset.induction_on with
    | empty=>simp [von,Meter.L,Meter.m4,Meter.I0,fourth]
    | @insert a S ha h=>
      simp only [sum_insert ha]
      exact le_trans (d.vplus (f a) _) (add_le_add_right h _)

lemma tm_le {f : TableF n w} {c} (h:0≤c) :
    d.ton f ≤ c ↔ d.ti (fun i j x=> f i j x^4) ≤ c^4 := Meter.LP _ h
lemma vm_le {f : Vertex n w} {c} (h:0≤c) :
    d.von f≤c↔ d.vi (fun i j=> f i j^4)≤c^4 := Meter.LP _ h

lemma torder {f g : TableF n w}
    (h:∀ s i j,i∈src d.S d.u s→ j∈dst d.S d.a s→ |f s i j| ≤ g s i j) :
    d.ton f ≤ d.ton g := by
  apply (d.tm_le (d.tn0 g)).2
  rw [d.ton_four]
  exact d.ti_mono fun s i j he hh=>by
    rw [← Meter.abs4 (f s i j)]; exact pow_le_pow_left₀ (abs_nonneg _) (h s i j he hh) 4
lemma vorder {f g : Vertex n w} (h:∀ s i,i∈src d.S d.u s→|f s i| ≤ g s i) :
    d.von f≤ d.von g := by
  apply (d.vm_le (d.vn0 g)).2
  rw [d.von_four]
  exact d.vi_mono fun s i he=>by rw [← Meter.abs4 (f s i)]; exact pow_le_pow_left₀ (abs_nonneg _) (h s i he) 4
lemma vi_nn {f : Vertex n w} (h:∀ s i,i∈src d.S d.u s → 0≤ f s i) : 0≤ d.vi f := by
  rw [d.vi_apply]
  exact mul_nonneg (scaleM_nn ..) (av_nonneg _ fun s=>sum_nonneg (h s))
lemma ti_nn {f : TableF n w} (h: ∀ s i j,i∈src d.S d.u s → j∈dst d.S d.a s →
                                 0≤f s i j) : 0≤d.ti f :=
    d.vi_nn (f:=fun s i=> ∑ j∈dst d.S d.a s,f s i j)
                         fun s i hi=>sum_nonneg fun j hj=>h s i j hi hj
lemma tmul (f : TableF n w) (c:ℝ) : d.ti (fun i j k=>c*f i j k)=c*d.ti f := Meter.scl ..
lemma vmul (f : Vertex n w) (c:ℝ) : d.vi (fun i j=>c*f i j)=c*d.vi f := Meter.scl ..

/-- Evaluate head of a row (L4 sum over columns), a convenient
alternative to suprema that still bounds them. -/
def head (f : TableF n w) : Vertex n w :=
   fun s i=> (Meter.Sum (dst d.S d.a s)).L (f s i)
lemma head_nn (f : TableF n w) s i : 0≤ d.head f s i := Meter.Lnn ..
lemma head_ge (f : TableF n w) s i {y} (hy:y∈dst d.S d.a s) :
    |f s i y| ≤d.head f s i := by
   have hs : (f s i y)^4≤∑ k∈dst d.S d.a s,(f s i k)^4 :=
      single_le_sum (f:=fun k=>f s i k^4) (fun k _=>by positivity) hy
   unfold head Meter.L Meter.m4
   conv_lhs=>rw [← four_fourth (abs_nonneg (f s i y))]
   rw [Meter.abs4]
   exact fourth_mono hs
lemma head_e (f : TableF n w) : d.von (d.head f)=d.ton f := by
   unfold von ton Meter.L Meter.m4
   unfold Meter.I VM TM Meter.Along Meter.Sum Meter.Scale Meter.Avg
   simp_rw [head, Meter.L4]
   rfl
lemma head_mask (P : X n w → ℕ→Prop) [∀ s i, Decidable (P s i)] (f : TableF n w) s i :
    d.head (fun s i j=>if P s i then f s i j else 0) s i =
    (if P s i then d.head f s i else 0) := by
   by_cases he:P s i <;> simp [head,he,Meter.Lzero]

/-- mask a deterministic array to possibly narrower terminal slices. -/
abbrev narrowed (a : ℕ) : Axis := {d with a:=a}
def wmask (a : ℕ) (f : TableF n w) : TableF n w :=
   fun s i j=> if j∈ dst d.S a s then f s i j else 0
lemma ti_mask (a : ℕ) (h:d.a≤a) (f : TableF n w) :
    d.ti (d.wmask a f)=(d.narrowed a).ti f := by
   unfold ti
   have hg (s:X n w) (j) : j∈dst d.S a s→ j∈dst d.S d.a s :=
      fun e=> mem_filter.2 ⟨(mem_filter.1 e).1,contained a d.a h (mem_filter.1 e).2⟩
   have he (s:X n w) (i) :
     ∑ j∈dst d.S d.a s,d.wmask a f s i j=∑ j∈dst d.S a s,f s i j := by
      unfold wmask
      rw [← sum_filter]
      congr 1; ext j; simp only [mem_filter]; exact ⟨fun e=>e.2,fun e=>⟨hg s j e,e⟩⟩
   change scaleM _ _ * av (fun s=>∑ i∈src d.S d.u s,∑ j∈dst d.S d.a s,_) =
          scaleM _ _ * av (fun s=>∑ i∈src d.S d.u s,∑ j∈dst d.S a s,_)
   simp_rw [he]

lemma tmask_power (a : ℕ) (h:d.a≤a) (f : TableF n w) :
    d.ton (d.wmask a f)^4=(d.narrowed a).ton f^4 := by
   rw [d.ton_four,ton_four]
   have he : (fun s i j=> d.wmask a f s i j^4)=d.wmask a (fun s i j=> f s i j^4) := by
      ext s i j; unfold wmask; split <;> simp_all
   rw [he,ti_mask d a h]

lemma tmask (a : ℕ) (h:d.a≤a) (f : TableF n w) :
    d.ton (d.wmask a f)=(d.narrowed a).ton f := by
   conv_lhs=>rw [← four_fourth (d.tn0 _)]
   rw [tmask_power d a h,four_fourth ((d.narrowed a).tn0 _)]

end Axis
end
end ExactDerandomization.Est

end

section

/-! Averaging on the rate conditions, without any frozen bits.
In this calculation w=0. The outer variant uses deterministic exact
endpoint equality. -/
set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Finset

variable {n : ℕ} [Fact n.Prime]
abbrev Pool (n : ℕ) := Env n 0
abbrev Pics (n) := TableF n 0
abbrev Paint (n) := Vertex n 0

/-- index-based probability scale factoring -/
lemma pct_c0 (n : ℕ) [Fact n.Prime] : pct n 0=1 := by
   rw [pct, side_zero (NeZero.pos n),div_self]; norm_num
   exact Nat.cast_ne_zero.mpr (NeZero.ne n)
lemma rr (i) : rate i = dry i^4 := rfl

namespace Axis
variable (d : Axis)

def fm (f : Pics n) : Mat :=
   fun i j=> Env.cond d.u d.a (↑i:ZMod n) (↑j:ZMod n) (fun s=>f s i j)
def vm (f : Paint n) : Vec :=
   fun i=> Env.cond d.u 0 (↑i:ZMod n) 0 (fun s=>f s i)

def fw (l : ℕ) (f : Pics n) : Pics n :=
   fun s i j=> Env.sampling d.u d.a (↑i:ZMod n) (↑j:ZMod n) (d:=0) (w:=0) le_rfl l
                          (fun s'=>f s' i j) s
def vw (l : ℕ) (f : Paint n) : Paint n :=
   fun s i=> Env.sampling d.u 0 (↑i:ZMod n) 0 (d:=0) (w:=0) le_rfl l (fun s'=>f s' i) s

lemma fdet (f : Mat) : d.fm (n:=n) (fun _=>f)=f := by ext; simp [fm,Env.cond,av_const]
lemma vdet (f : Vec) : d.vm (n:=n) (fun _=>f)=f := by ext; simp [vm,Env.cond,av_const]
lemma fscalar (c : ℝ) (f : Pics n) i j :
    d.fm (fun s i j=> c*f s i j) i j = c*d.fm f i j := by rw [fm,fm,Env.cond,Env.cond]; rw [av_cmul]
lemma fmean_sub (f g : Pics n) i j :
    d.fm (fun s i j=> f s i j-g s i j) i j=d.fm f i j-d.fm g i j := by
   rw [fm,fm,fm,Env.cond,Env.cond,Env.cond,av_sub]
lemma vmean_sub (f g : Paint n) i :
    d.vm (fun s i=> f s i-g s i) i=d.vm f i-d.vm g i := by
   rw [vm,vm,vm,Env.cond,Env.cond,Env.cond,av_sub]
lemma goodfm {f : Pics n} {i j:ℕ} {c:ℝ} (h1:∀ s,
    hit d.u (↑i:ZMod n) s.1 → hit d.a (↑j:ZMod n) s.2.1 → 0≤f s i j∧ f s i j≤c) :
    0≤d.fm f i j ∧ d.fm f i j≤c := by
   unfold fm Env.cond
   let g (x:Env.Slice n d.u d.a 0) :=
      f (Env.outward d.u d.a (i:ZMod n) (j:ZMod n) x) i j
   have he (x) : 0≤g x∧g x≤c:= h1 _ (Env.hits ..).1 (Env.hits ..).2
   refine ⟨av_nonneg g (fun i=>(he i).1),le_trans ?_ (le_of_eq (@av_const (Env.Slice n d.u d.a 0) _ _ _))⟩
   exact av_mono (g:=fun _=>c) fun i=>(he i).2

lemma eqfm {f g : Pics n} {i j:ℕ} (h:∀ s,
    hit d.u (↑i:ZMod n) s.1 → hit d.a (↑j:ZMod n) s.2.1 → f s i j=g s i j) :
    d.fm f i j=d.fm g i j := by
   unfold fm Env.cond
   apply congrArg av; ext x
   exact h _ (Env.hits ..).1 (Env.hits ..).2

lemma eqvm {f g : Paint n} {i:ℕ} (h:∀ s,hit d.u (↑i:ZMod n) s.1 → f s i=g s i) :
    d.vm f i=d.vm g i := by
   unfold vm Env.cond
   apply congrArg av; ext x
   exact h _ (Env.hits ..).1

lemma ite_wmask {a} {i j} (h:d.a≤a) (f : Pics n) (he:j∈d.S) :
    pct n d.a*d.fm (d.wmask a f) i j = pct n a * (d.narrowed a).fm f i j := by
   apply mul_left_cancel₀ (pct_pos (NeZero.pos n) d.u).ne'
   rw [← mul_assoc,← mul_assoc]; unfold fm narrowed
   rw [← Env.two_cond,← Env.two_cond]; congr 1; ext s
   unfold wmask dst retain Env.mask
   simp only [mem_filter,he,true_and]
   by_cases hz:hit d.u (↑i:ZMod n) s.1
   · by_cases hs : hit a (↑j:ZMod n) s.2.1
     · simp [hs,contained a d.a h hs,hz]
     simp [hs,hz]
   simp [hz]

lemma fpivot (f : Pics n) :
    d.ti f=scaleM d.N d.u*∑ i∈d.S,∑ j∈d.S, pct n d.u*pct n d.a*d.fm f i j :=
    d.conditional f
lemma vpivot (f : Paint n) :
    d.vi f=scaleM d.N d.u*∑ i∈d.S,pct n d.u*d.vm f i := by
   rw [vi_apply]; congr 1
   have he (s:Pool n) :
       ∑ i∈src d.S d.u s,f s i=∑ i∈d.S,if Env.mask d.u 0 (↑i:ZMod n) 0 s then f s i else 0 := by
      unfold src retain; rw [sum_filter]; simp [Env.mask,allhit]
   simp_rw [he,av_sum]
   refine sum_congr rfl fun i hi=>?_
   unfold vm; rw [Env.two_cond,pct_c0,mul_one]

lemma ftest {f g : Pics n} (h:∀ i∈d.S,∀ j∈d.S,d.fm f i j≤ d.fm g i j) :
    d.ti f ≤ d.ti g := by
   rw [d.fpivot,d.fpivot]
   refine mul_le_mul_of_nonneg_left ?_ (scaleM_nn ..)
   exact sum_le_sum fun i hi=>sum_le_sum fun j hj=>mul_le_mul_of_nonneg_left (h i hi j hj)
                         (mul_nonneg (pct_pos (NeZero.pos _) _).le (pct_pos (NeZero.pos _) _).le)
lemma vtest {f g : Paint n} (h:∀ i∈d.S,d.vm f i ≤ d.vm g i) : d.vi f≤d.vi g := by
   rw [d.vpivot,d.vpivot]; refine mul_le_mul_of_nonneg_left ?_ (scaleM_nn ..)
   exact sum_le_sum fun i hi=>mul_le_mul_of_nonneg_left (h i hi) (pct_pos (NeZero.pos _) _).le

lemma fnorm (f : Pics n) : d.ton (n:=n) (w:=0) (fun _=> d.fm f) ≤ d.ton f := by
   apply (d.tm_le (d.tn0 _)).mpr
   rw [d.ton_four]
   apply d.ftest; intro i hi j hj
   unfold fm Env.cond
   rw [av_const]; apply av_four_le
lemma vnorm (f : Paint n) : d.von (n:=n) (w:=0) (fun _=> d.vm f) ≤ d.von f := by
   apply (d.vm_le (d.vn0 _)).2
   rw [d.von_four]
   apply d.vtest; intro i hi
   unfold vm Env.cond; rw [av_const]; apply av_four_le

lemma froot {f g : Pics n} (hf:∀ s i j,0≤f s i j) (hg:∀ s i j,0≤g s i j) :
    d.terr (n:=n) (w:=0) (fun _=>d.fm f) (fun _=>d.fm g) ≤ d.terr f g := by
   unfold Axis.terr
   apply (d.tm_le (d.tn0 _)).2
   rw [d.ton_four]; apply d.ftest; intro i hi j hj
   unfold fm Env.cond
   rw [av_const]
   exact mixtures Meter.Avg _ _ (fun _=>hf ..) (fun _=>hg ..)

lemma fswap_det (f : Mat) (a : ℕ) :
    pct n a * d.ti (n:=n) (w:=0) (fun _=>f) = pct n d.a *
                         (d.narrowed a).ti (n:=n) (w:=0) (fun _=>f) := by
   rw [d.fpivot,fpivot,d.fdet,fdet]
   dsimp only [narrowed]
   rw [mul_left_comm (pct n a),mul_left_comm (pct n d.a)]
   congr 1
   rw [mul_sum,mul_sum]
   apply sum_congr rfl; intro i hi
   rw [mul_sum,mul_sum]; apply sum_congr rfl; intro j hj; ring

end Axis

end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Finset

variable {n : ℕ} [Fact n.Prime]

lemma shrink {a b} (h:a≤b) : rate b/rate a=dry (b-a)^4 := by
   have he : rate b=dry (b-a)^4*rate a := by
      calc rate b=dry (b-a+a)^4 := by rw [Nat.sub_add_cancel h,rr]
           _ = _ := by rw [dryP,rr,mul_pow]
   rw [he,mul_div_cancel_right₀ _ (rate_pos _).ne']
lemma swell {a b} (h:a≤b) : rate a/rate b=box (b-a)^4 := by
   rw [← inv_div (rate b),shrink h,dry,inv_pow]
   simp
lemma odds {a b n} (hp: 2^b≤n) (h:a≤b) :
    pct n a / pct n b ≤ (2*box (b-a))^4 := by
   have he:= (pct_bounds hp).1
   have ha:= (pct_bounds (k:=a) (le_trans (Nat.pow_le_pow_right (by omega) h) hp)).2
   calc _ ≤ (16*rate a)/rate b := by
             gcongr
             · have hh:= rate_pos a
               positivity
             · exact rate_pos _
        _ = _:= by rw [mul_div_assoc,swell h]; ring

abbrev nar (a k : ℕ) := max a k
def salary (a k : ℕ) := if k≤a then box (a-k) else dry (k-a)^3
def loaded (n a k : ℕ) := rate k/rate a*(pct n a/pct n (nar a k))
def distn (a b : ℕ) := (a-b)+(b-a)
lemma paypos (a k) : 0<salary a k := by
   unfold salary; split
   · exact box0 _
   exact pow_pos (dry0 _) _
lemma coarse_pay {a k} (h:k≤a) :
    loaded n a k=box (a-k)^4 := by
   unfold loaded nar; rw [max_eq_left h,swell h,div_self (pct_pos (NeZero.pos _) _).ne',mul_one]
lemma cost_pos (n : ℕ) [Fact n.Prime] (a k) : 0<loaded n a k :=
   mul_pos (div_pos (rate_pos _) (rate_pos _))
           (div_pos (pct_pos (NeZero.pos _) _) (pct_pos (NeZero.pos _) _))

lemma burden {k a} (hp: 2^(nar a k)≤n) :
    loaded n a k ≤ 16 * box (4*distn a k) := by
   let l:=nar a k
   rcases le_total k a with h|h
   · rw [coarse_pay h,distn, Nat.sub_eq_zero_of_le h,Nat.add_zero,Nat.mul_comm,boxM]
     have := box_one (a-k)
     nlinarith [show 0≤box (a-k)^4 by positivity]
   unfold loaded
   rw [show nar a k=k from max_eq_right h,shrink h]
   have hh : 2^k≤n:= by rwa [nar,max_eq_right h] at hp
   refine le_trans (mul_le_mul_of_nonneg_left (odds hh h) (by positivity)) ?_
   have hu:=box_one (4*distn a k)
   rw [← mul_pow,show dry (k-a)*(2*box (k-a))=2 from ?_]
   · linarith
   rw [mul_left_comm,reunite,mul_one]

/-- uniformly bounded, in roots -/
def RCap (K : ℝ) (f : Pics n) := ∀ s i j,0≤ f s i j ∧ fourth (f s i j) ≤ K

omit [Fact (Nat.Prime n)] in
lemma from_cap {K : ℝ} {f : Pics n} (h:RCap K f) s i j :
    0≤f s i j ∧ f s i j≤K^4 := by
   obtain ⟨hh,he⟩:=h s i j
   exact ⟨hh,le_trans (le_of_eq (fourth_four hh).symm) (pow_le_pow_left₀ (fourth_nn _) he _)⟩

namespace Axis
variable (d : Axis)
def carry (k : ℕ) (f : Pics n) : Pics n :=
    fun s i j=> loaded n d.a k*f s i j

def pinned (a : ℕ) (f : Pics n) := d.wmask a f=f

lemma ton_subnorm (f : Pics n) : d.ton (fun s i j=> |f s i j|)=d.ton f := Meter.Labs ..
lemma ton_ext {f g : Pics n}
    (h:∀ s i j, i∈src d.S d.u s → j∈dst d.S d.a s → f s i j=g s i j) :
    d.ton f=d.ton g := by
   have he1 : d.ton f ≤ d.ton g := by
     rw [← d.ton_subnorm g]; exact d.torder fun s i j he hg=>by rw [h s i j he hg]
   have he2 : d.ton g≤d.ton f := by
     rw [← d.ton_subnorm f]; exact d.torder fun s i j he hg=>by rw [h s i j he hg]
   exact le_antisymm he1 he2

lemma root_fee {f g : Pics n} {K} (h:RCap K f) (e:RCap K g) (hp : 1≤K) :
    d.ton (fun s i j=> f s i j-g s i j) ≤4*K^3*d.terr f g := by
   let a : Pics n := fun s i j=> fourth (f s i j)-fourth (g s i j)
   have hz : 0≤4*K^3 := by positivity
   change _≤4*K^3*d.ton a
   rw [← d.ton_subnorm a,← abs_of_nonneg hz,← d.tscale]
   refine d.torder fun s i j hv hh=>?_
   obtain ⟨h1,h2⟩:=h s i j; obtain ⟨h3,h4⟩:=e s i j
   exact ordinary h1 h3 h2 h4

lemma unit_change {a : ℕ} (h : d.a≤a) (hp : 2^a≤n) (f : Mat) :
   d.ton (n:=n) (w:=0) (fun _=>f) ≤
             2*box (a-d.a) * (narrowed d a).ton (n:=n) (w:=0) (fun _=>f) := by
   let K:= 2*box (a-d.a)
   have he : 0≤K := mul_nonneg (by norm_num) (box0 _).le
   change _ ≤ K * _
   apply (d.tm_le (mul_nonneg he ((d.narrowed a).tn0 _))).2
   rw [mul_pow, ton_four]
   exact le_of_mul_le_mul_left (a:= pct n a) (by
      let g:Mat:=fun i j=> f i j^4
      have hz := d.fswap_det (n:=n) g a
      change pct n a*d.ti (n:=n) (w:=0) (fun _=>g) ≤ pct n a*(K^4*(narrowed d a).ti (n:=n) (w:=0) (fun _=>g))
      rw [hz,← mul_assoc]
      have ho:pct n d.a ≤ pct n a *K^4 := by rw [mul_comm]; exact (div_le_iff₀ (pct_pos (NeZero.pos n) _)).1 (odds hp h)
      exact mul_le_mul_of_nonneg_right ho ((d.narrowed a).ti_nn (fun _ _ _ _ _=>by unfold g; positivity)))
              (pct_pos (NeZero.pos n) _)

lemma mean_move {a : ℕ} (h : d.a≤a) {f : Pics n} (e:d.pinned a f) i {j} (hj:j∈d.S) :
    (pct n d.a/pct n a) * d.fm f i j = (d.narrowed a).fm f i j := by
   have hp:= d.ite_wmask h f hj (i:=i); unfold pinned at e; rw [e] at hp
   field_simp [(pct_pos (NeZero.pos n) a).ne']
   linarith

lemma carry_change (k) {f:Pics n} (h:d.pinned (nar d.a k) f) (i) {j}
    (hj:j∈d.S) :
    d.fm (d.carry k f) i j=rate k/rate d.a*(d.narrowed (nar d.a k)).fm f i j := by
   unfold carry
   rw [d.fscalar,loaded,mul_assoc,d.mean_move (le_max_left ..) h i hj]

abbrev paycheck (K : ℝ) := 64*K^4

set_option maxHeartbeats 700000 in
/-- Comparison of one conditioned first-channel contribution. -/
lemma stream_fee {k : ℕ} (hp: 2^(nar d.a k)≤n) {K : ℝ} (hK:1≤K) {f g : Pics n}
    (hf:RCap K f) (hg:RCap K g)
    (hf':d.pinned (nar d.a k) f) (hg':d.pinned (nar d.a k) g)
    {D : Mat} (hD:∀ i∈d.S,∀ j∈d.S, 0≤D i j)
    (hb:∀ i∈d.S,∀ j∈d.S,d.fm (d.carry k f) i j≤K*D i j) :
    d.ton (n:=n) (w:=0) (fun _ i j=> rel (d.fm (d.carry k f) i j-
                                d.fm (d.carry k g) i j) (D i j))
        ≤ paycheck K * salary d.a k * (d.narrowed (nar d.a k)).terr f g := by
   let v (i j) := d.fm (d.carry k f) i j-d.fm (d.carry k g) i j
   have hl (i) (hi : i∈d.S) (j) (hj:j∈d.S) : 0≤rel (v i j) (D i j) := by
       unfold rel; have h:=hD i hi j hj; positivity
   have hk : 0<K := by linarith
   by_cases hu : k≤d.a
   · rw [nar,max_eq_left hu,salary,ite_eq_left hu]
     let p:= box (d.a-k)
     let e (i j):= fourth (d.fm f i j)-fourth (d.fm g i j)
     let a :=32*K*p
     have hp': 0<p:=box0 _
     have hA : 0≤a:=by unfold a; positivity
     have he (s i j) (h: i∈src d.S d.u (s:Pool n)) (h1:j∈dst d.S d.a s) :
         |rel (v i j) (D i j)|≤ a * |e i j| := by
       have he2:= (mem_filter.1 h).1; have he3:= (mem_filter.1 h1).1
       rw [abs_of_nonneg (hl _ he2 _ he3)]
       have Hv (g:Pics n): d.fm (d.carry k g) i j=p^4*d.fm g i j := by
          unfold carry; rw [d.fscalar,coarse_pay hu]
       have Ha : 0 ≤ d.fm f i j := (d.goodfm (fun s h h'=>from_cap hf s i j)).1
       have Hb : 0 ≤ d.fm g i j := (d.goodfm (fun s h h'=>from_cap hg s i j)).1
       have H2 := hb i he2 j he3
       unfold v; rw [Hv,Hv]; rw [Hv] at H2
       have hw : 0≤p^4:=by positivity
       apply le_trans (fidelity (mul_nonneg hw Ha) (mul_nonneg hw Hb) (hD i he2 j he3) H2 hK)
       rw [fourth_mul hw,fourth_mul hw,four_fourth hp'.le,← mul_sub,abs_mul,abs_of_nonneg hp'.le]
       unfold a e; exact le_of_eq (by ring)
     refine (d.torder he).trans ?_

     rw [d.tscale,d.ton_subnorm (f:=fun s i j=> e i j), abs_of_nonneg hA]
     have hs : d.narrowed d.a=d := rfl
     rw [hs]
     have hd: d.ton (n:=n) (w:=0) (fun _ i j=> e i j)≤ d.terr f g :=
         d.froot (fun s i j=>(hf s i j).1) (fun s i j=>(hg s i j).1)
     refine mul_le_mul (by
       change 32*K*p ≤ 64*K^4*p
       have hC : K≤K^4 := by simpa using pow_le_pow_right₀ hK (show 1≤ (4:ℕ) by omega)
       exact mul_le_mul_of_nonneg_right (by linarith) hp'.le) hd (d.tn0 _)
       (by unfold paycheck; have h:=box0 (d.a-k); positivity)
   have ht:=lt_of_not_ge hu
   have ha := show nar d.a k=k from max_eq_right ht.le
   let p:=dry (k-d.a)
   have hv (i j) (hj:j∈d.S) :
        v i j=p^4*(d.narrowed k).fm (fun s i j=>f s i j-g s i j) i j := by
     unfold v; rw [carry_change _ k hf' _ hj,carry_change _ k hg' _ hj,ha,←mul_sub,fmean_sub,shrink ht.le]
   let A : Mat := fun i j=> (d.narrowed k).fm (fun s i j=> f s i j-g s i j) i j
   have he (s i j) (hi:i∈src d.S d.u (s:Pool n)) (hj:j∈dst d.S d.a s) :
       |rel (v i j) (D i j)| ≤ p^4 * |A i j| := by
       have hx := (mem_filter.1 hi).1; have hy:=(mem_filter.1 hj).1
       have h0:=hD i hx j hy
       rw [abs_of_nonneg (hl _ hx _ hy)]
       unfold rel
       apply le_trans (min_le_right ..)
       have hh : 0≤ p^4:=by positivity
       rw [div_le_iff₀ (by linarith)]
       rw [hv i j hy,abs_mul,abs_of_nonneg hh]
       change p^4* |A i j| ≤ _
       nlinarith [show 0 ≤ p^4 * |A i j| from by positivity]
   apply (d.torder he).trans
   rw [d.tscale,d.ton_subnorm (f:=fun s i j=> A i j),abs_of_nonneg (by positivity)]
   rw [ha] at hp ⊢
   have hd := (d.narrowed k).fnorm (fun s i j=> f s i j-g s i j)
   have hx := (d.narrowed k).root_fee hf hg hK
   change (d.narrowed k).ton (w:=0) (n:=n) (fun _=> A) ≤ _ at hd
   have hf1 := le_trans hd hx
   apply le_trans (mul_le_mul_of_nonneg_left (d.unit_change (n:=n) ht.le hp A) (by positivity))
   apply le_trans (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hf1 (show 0≤2*box (k-d.a) from mul_nonneg (by norm_num) (box0 _).le))
                 (by positivity))
   rw [salary,ite_eq_right hu]
   have hg : p*box (k-d.a)=1:=reunite _
   let w:=(d.narrowed k).terr f g
   change p^4 * (2 * box (k-d.a) * (4*K^3*w)) ≤ _*p^3*w
   unfold paycheck
   have he : K^3≤K^4:=pow_le_pow_right₀ hK (by omega)
   have hp0 : 0 ≤ p:= (dry0 _).le
   have hw : 0≤w:= (d.narrowed k).tn0 _
   calc _ = 8*K^3*p^3*w*(p*box (k-d.a)) := by ring
        _ ≤ _ := by
          rw [hg,mul_one]
          have hk:=mul_le_mul_of_nonneg_right (show 8*K^3≤64*K^4 from by linarith [show 0≤K^4 by positivity])
                          (show 0 ≤ p^3*w by positivity)
          linarith

lemma realize_pin {a : ℕ} {f : Pics n}
    (h:∀ s i j,f s i j≠0 → j∈dst d.S a s) : d.pinned a f := by
   unfold pinned wmask; ext s i j; split
   · rfl
   · next he=> exact Eq.symm (not_not.mp (fun e=>he (h _ _ _ e)))

lemma raw_fee {k : ℕ} (hp: 2^(nar d.a k)≤n) {K : ℝ} (hK:1≤K) {f g : Pics n}
    (hf:RCap K f) (hg:RCap K g) (hf':d.pinned (nar d.a k) f) (hg':d.pinned (nar d.a k) g) :
    d.ton (fun s i j=> d.carry k f s i j-d.carry k g s i j) ≤
       paycheck K*box (4*distn d.a k)*(d.narrowed (nar d.a k)).terr f g := by
   let c:=loaded n d.a k; let a:=nar d.a k
   let z:Pics n:=fun s i j=>f s i j-g s i j
   have he : d.pinned a z:= by
      have ht:d.wmask a z= fun s i j=> d.wmask a f s i j-d.wmask a g s i j := by
         unfold wmask z; ext s i j; split <;> simp_all
      unfold pinned; rw [ht,show d.wmask a f=f from hf',show d.wmask a g=g from hg']
   have hw : d.ton z=(d.narrowed a).ton z := by conv_lhs=>rw [← show d.wmask a z=z from he]
                                                exact d.tmask a (le_max_left ..) z
   have hx := (d.narrowed a).root_fee hf hg hK
   change d.ton (fun s i j=> c*f s i j-c*g s i j) ≤ _
   simp_rw [← mul_sub]; rw [d.tscale]; change |c| * d.ton z ≤ _
   have hc : 0≤c := (cost_pos n _ _).le
   rw [abs_of_nonneg hc,hw]
   refine le_trans (mul_le_mul_of_nonneg_left hx hc) ?_
   let b:=box (4*distn d.a k)
   have hu : c≤16*b := burden hp
   have hk : 0≤K := by linarith
   have hv :=(d.narrowed a).tn0 (n:=n) (w:=0) (fun s i j=>fourth (f s i j)-fourth (g s i j))
   have hb : 0≤b := (box0 _).le
   rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hv
   apply le_trans (mul_le_mul_of_nonneg_right hu (show 0≤4*K^3 by positivity))
   unfold paycheck
   change _ ≤ _ * b
   have hz : K^3 ≤ K^4 := pow_le_pow_right₀ hK (by omega)
   nlinarith

set_option maxHeartbeats 600000 in
/-- One collective loss of a wholly fine tail. X/rate d.a are the raw units. -/
lemma fine_tail {X0 : Mat} {K : ℝ} {m : ℕ}
    (hK:1≤K) (hp : 2^d.a ≤ n) (hv : 2^d.u ≤ n)
    (hC:d.S.card≤d.N)
    (he:∀ i∈d.S,∀ j∈d.S,0≤X0 i j ∧ X0 i j ≤ K*rate (d.a+m))
    (hr:∀ i∈d.S,∑ j∈d.S,X0 i j ≤ K) :
    d.ton (n:=n) (w:=0) (fun _ i j=> X0 i j / rate d.a) ≤ 4*K*dry m^3 := by
   let f:=rate d.a; let g:=rate d.u; let a:=dry m
   have hf : 0<f:=rate_pos _
   have hg : 0<g:=rate_pos _
   have ha : 0≤a:= (dry0 _).le
   have hk : 0≤K:=by linarith
   have he2 : rate (d.a+m) = a^4*f := by rw [rr,dryP,mul_pow,mul_comm]; rfl
   let T:Mat:=fun i j=> (X0 i j/f)^4
   have H (i) (h:i∈d.S) :
      (∑ j∈d.S,T i j) ≤ K^4*(a^3)^4/f := by
     have hl (j) (hj:j∈d.S) :
        T i j≤ (K*a^4)^3 * (X0 i j/f) := by
       obtain ⟨h1,h2⟩:= he i h j hj
       have hh : X0 i j/f ≤ K*a^4 := by
          rw [div_le_iff₀ hf]
          rw [he2] at h2; linarith
       have he : 0≤X0 i j/f := div_nonneg h1 hf.le
       unfold T
       rw [pow_succ]
       exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ he hh 3) he
     apply le_trans (sum_le_sum hl)
     rw [← mul_sum, ← sum_div]
     apply le_trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hr i h) hf.le)
                            (show 0≤(K*a^4)^3 by positivity))
     exact le_of_eq (by ring)
   apply (d.tm_le (n:=n) (w:=0) (c:=4*K*a^3) (by positivity)).mpr
   change d.ti (fun (_:Pool n)=> T) ≤ (4*K*a^3)^4
   rw [d.fpivot,d.fdet]
   have hz : 0 ≤ pct n d.u*pct n d.a := mul_nonneg (pct_pos (NeZero.pos _) _).le (pct_pos (NeZero.pos _) _).le
   have hz' : pct n d.u*pct n d.a ≤16*g*(16*f) :=
      mul_le_mul (pct_bounds hv).2 (pct_bounds hp).2 (pct_pos (NeZero.pos _) _).le (by positivity)
   have h1 (i) (hi:i∈d.S) :
      ∑ j∈d.S,pct n d.u*pct n d.a*T i j ≤ (4*K*a^3)^4 *g := by
        rw [← mul_sum]
        have hT := H i hi
        apply le_trans (mul_le_mul hz' hT (by unfold T; apply sum_nonneg; intros; positivity) (by positivity))
        exact le_of_eq (by field_simp; ring)
   apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum h1) (scaleM_nn _ _))
   simp only [sum_const,nsmul_eq_mul]
   obtain hn|hn:=Nat.eq_zero_or_pos d.N
   · unfold scaleM; rw [hn]; simp; positivity
   unfold scaleM; change ((d.N:ℝ)*g)⁻¹ * _ ≤_
   have he0 : 0 < (d.N:ℝ)*g:=mul_pos (by exact_mod_cast hn) hg
   have he1 : (d.S.card:ℝ)≤ d.N:=by exact_mod_cast hC
   rw [← div_eq_inv_mul,div_le_iff₀ he0]
   have hl := mul_le_mul_of_nonneg_right he1 (show 0≤(4*K*a^3)^4*g by positivity)
   linarith

end Axis
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Finset Affine Square

variable {n : ℕ} [Fact n.Prime]

private instance s_one : Subsingleton (Salt 0) := inferInstanceAs (Subsingleton (V 1))
private lemma empty_seam (x y : ZMod n) (k j) (s : Env.Slice n k j 0) :
    (@Env.exportP n 0 0 _ k j x y le_rfl 0 s) = Env.outward k j x y s := by
   unfold Env.exportP; congr 1
   cases s with
   | mk a s =>
   cases s with
   | mk b s=>
   cases s with
   | mk c p=>
   apply Prod.ext
   · rfl
   apply Prod.ext
   · rfl
   apply Prod.ext
   · rfl
   exact Subsingleton.elim ..

def ebb := 1-loss Env.Choice (10*gap0)
lemma ebb_nn : 0<ebb ∧ ebb<1 := by
   have h : 1≤10*gap0 := by linarith [gapFuel_pos]
   obtain ⟨h,h1⟩ := loss_bounds (γ:=Env.Choice) h
   unfold ebb; constructor <;> linarith
/-- lam = walk length per unit statistical slack. -/
def Wind (e lam : ℕ) : Prop := ebb^lam*16≤dry e^4
lemma find_lam (e : ℕ) : ∃ lam, Wind e lam := by
   have he : 0 < dry e ^4 /16 := div_pos (pow_pos (dry0 _) _) (by norm_num)
   obtain ⟨l,hl⟩ := exists_pow_lt_of_lt_one he ebb_nn.2
   exact ⟨l,by unfold Wind; linarith⟩
lemma blow {e lam} (h:Wind e lam) {a : ℕ} (he:0<a) :
    ebb^(lam*a)*16 ≤dry (e*a)^4 := by
   have hz := pow_le_pow_left₀ (show 0≤ebb^lam*16 by have :=ebb_nn.1; positivity) h a
   rw [pow_mul,dryM]
   unfold Wind at h
   apply le_trans (b:=(ebb^lam*16)^a) ?_
   · exact hz.trans_eq (by rw [← pow_mul,← pow_mul,mul_comm a])
   · rw [mul_pow]
     have hx : (16:ℝ)≤16^a := calc
        _ = (16:ℝ)^1 := by ring
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) he
     exact mul_le_mul_of_nonneg_left hx (pow_nonneg (pow_nonneg ebb_nn.1.le _) _)

lemma blows {e lam} (h:Wind e lam) {a : ℕ} (he:0<a) (k j) (x y : ZMod n) (f : Pool n→ℝ) :
   Env.cond k j x y (fun s=> (Env.sampling k j x y (d:=0) (w:=0) le_rfl (lam*a) f s-
                           Env.cond k j x y f)^4) ≤
        dry (e*a)^4 * Env.cond k j x y (fun s=>f s^4) := by
   have hx:= @Env.sampler_est n 0 0 _ k j x y le_rfl 0 (lam*a) f
   let o:= Env.outward k j x y (w:=0)
   have hs (s:Env.Slice n k j 0) :
         @Env.panel n 0 0 _ k j x y le_rfl 0 f s=f (o s) := by
      change f (_:_)=_
      exact congrArg f (empty_seam x y k j s)
   dsimp only at hx
   unfold mass4 at hx
   simp_rw [hs,empty_seam x y k j] at hx
   rw [show @Env.panel n 0 0 _ _ _ x y le_rfl 0 f=(fun i=>f (o i)) from funext hs] at hx
   unfold Env.cond
   apply le_trans hx
   have hv : 0≤ av (fun s:Env.Slice n k j 0=> f (o s)^4) := av_nonneg _ fun _ => by positivity
   rw [← mul_assoc]
   exact mul_le_mul_of_nonneg_right (blow h he) hv

namespace Axis
variable (d:Axis)

def fluke (l : ℕ) (f : Pics n) : Pics n :=
    fun s i j=> d.fw l f s i j - d.fm f i j
def vluke (l : ℕ) (f : Paint n) : Paint n :=
    fun s i=>d.vw l f s i - d.vm f i

lemma windF {e lam} (h:Wind e lam) {a:ℕ} (he:0<a) (f:Pics n) :
   d.ton (d.fluke (lam*a) f) ≤ dry (e*a)*d.ton f := by
   apply (d.tm_le (mul_nonneg (dry0 _).le (d.tn0 f))).2
   rw [mul_pow,d.ton_four,← d.tmul]
   apply d.ftest; intro i hi j hj
   rw [d.fscalar]
   exact blows h he _ _ _ _ (fun s=> f s i j)

lemma windV {e lam} (h:Wind e lam) {a:ℕ} (he:0<a) (f:Paint n) :
   d.von (d.vluke (lam*a) f) ≤ dry (e*a)*d.von f := by
   apply (d.vm_le (mul_nonneg (dry0 _).le (d.vn0 f))).2
   rw [mul_pow,d.von_four,← d.vmul]
   apply d.vtest; intro i hi
   unfold vm Env.cond; rw [av_cmul]
   exact blows h he _ _ _ _ (fun s=>f s i)

end Axis

private lemma into_range {p q : ℝ} {α γ : Type} [Fintype α] [Nonempty α] [Fintype γ] [Nonempty γ]
    (G : Family γ α) {f : α→ℝ} (h:∀ x,p≤f x∧f x≤q) (l x) :
    p≤walk G f l x∧walk G f l x≤q := by
   induction l generalizing x with
   | zero=>exact h x
   | succ l ih=>
     let w:=walk G f l
     have hh (j:γ) : p≤(w (G j x)+w x)/2∧(w (G j x)+w x)/2≤q := by
        obtain ⟨hp,he⟩:=ih x
        obtain ⟨hs,ht⟩:=ih (G j x)
        unfold w; constructor <;> linarith
     change p≤av _∧av _ ≤ q
     refine ⟨le_trans (le_of_eq (av_const (α:=γ) p).symm) (av_mono fun i=> (hh i).1),
             le_trans (av_mono fun i=>(hh i).2) (le_of_eq (av_const (α:=γ) q))⟩

lemma magnitude {p q : ℝ} (x y : ZMod n) (k j l) {f:Pool n→ℝ}
    (h:∀ s,Env.mask k j x y s → p≤f s∧ f s≤q) {s}
    (hs:Env.mask k j x y s) :
    p≤@Env.sampling n 0 0 _ k j x y le_rfl l f s∧
       @Env.sampling n 0 0 _ k j x y le_rfl l f s ≤q := by
   let t:=Env.inward k j x y s
   let w:=@Env.exportP n 0 0 _ k j x y le_rfl 0
   have he : w t=s:= Eq.trans (empty_seam x y k j t) (Env.inverse1 _ _ _ _ _ hs)
   have hu:= @Env.sampler_identity n 0 0 _ k j x y le_rfl 0 l f t
   have hz (u) : p≤ f (w u)∧ f (w u)≤q := h _ (Env.hits ..)
   change @Env.sampling n 0 0 _ _ _ _ _ _ _ _ (w t) = walk _ _ _ _ at hu
   rw [he] at hu; rw [hu]
   exact into_range _ hz l t

end
end ExactDerandomization.Est

end

section

namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Finset

structure StepKey where
    a : ℕ
    u : ℕ
    r : ℕ

def allowance (A M : ℕ) (t : StepKey) : ℝ :=
    dry (M / 8) * box (2*t.a+2*t.u+A*t.r)
def active (A M : ℕ) (t : StepKey) := 2*t.a+2*t.u+A*t.r < M / 8

namespace StepKey
variable (t : StepKey)

def allowanceStep (A m k : ℕ) := allowance A m ⟨k,t.u,t.r-1⟩
def token (A M : ℕ) := allowance A M t * dry A
lemma allow_p (A M) : 0< allowance A M t := mul_pos (dry0 _) (box0 _)
lemma token_p (A M) : 0<t.token A M:=mul_pos (t.allow_p ..) (dry0 _)

lemma inactive {A M} (h:¬active A M t) : 1 ≤ allowance A M t := by
   unfold allowance
   have he := reunite (M/8)
   apply he.symm.le.trans (mul_le_mul_of_nonneg_left (box_mono (le_of_not_gt h)) (dry0 _).le)

lemma lower (k : ℕ) {v : StepKey} {B : ℕ} (hv : v.r<t.r) (ha:v.a≤ k+B)
    (hu:v.u≤t.u) (A m) :
    box (t.u-v.u)*allowance A m v ≤ box (2*B)*t.allowanceStep A m k := by
   unfold allowance allowanceStep allowance
   rw [mul_left_comm (box (t.u-v.u)),mul_left_comm (box (2*B)),← boxP,← boxP]
   apply mul_le_mul_of_nonneg_left (box_mono ?_) (dry0 _).le
   simp only
   have he:=Nat.mul_le_mul_left A (show v.r≤ t.r-1 by omega)
   omega

lemma budget_gap {M m} (h:m≤M) : dry (m/8)=dry (M/8)*box (M/8-m/8) := by
   let a:=m/8; let b:=M/8
   have hz:b=b-a+a:=by dsimp [a,b]; omega
   calc _ = dry (b-a+a)*box (b-a) := by
          rw [dryP,mul_comm (dry _*_),← mul_assoc,unify, one_mul]
        _ = _ := by change dry (b-a+a)*_=dry b*box _; congr 2; omega

lemma transfer {M m} (A k) (h:m≤M) (hp:0<t.r) :
    t.allowanceStep A m k=box (M/8-m/8) * ({t with a:=k}:StepKey).token A M := by
   unfold allowanceStep token allowance
   let a:=A*(t.r-1)
   have hv: A*t.r=a+A := by dsimp only [a]; rw [← Nat.mul_succ]; congr 1; omega
   dsimp only
   rw [budget_gap h,hv,← add_assoc,boxP (2*k+2*t.u+a) A]; change _ * box (2*k+2*t.u+a) = _
   rw [mul_assoc (dry _) (box _*box _) (dry A),mul_assoc (box _),unify,mul_one]; ring

lemma adjust (a k v) :
    salary a k * box (2*k+v) = dry (distn a k)*box (2*a+v) := by
   unfold salary distn; split
   · next h=>
      rw [show k-a=0 by omega,add_zero,← boxP]
      let d:=a-k
      have hh : 2*a+v=d+(d+(2*k+v)) := by dsimp [d]; omega
      rw [hh,boxP d (d+(2*k+v)),← mul_assoc,reunite,one_mul]
   · next h=>
      rw [show a-k=0 by omega,zero_add]
      let d:=k-a
      change dry d^3*_=dry d*_
      have hs : 2*k+v=d+d+(2*a+v):=by dsimp [d]; omega
      rw [hs,boxP,boxP]; rw [show dry d^3*(box d * box d * box (2*a+v))=
        dry d*box (2*a+v)*(dry d*box d)*(dry d*box d) from by ring,reunite]; ring

lemma divide {m M A} {k d} (h:m≤M) (he:M-m ≤ d+distn t.a k+1) (hp:1≤d) (hr:0<t.r) :
    salary t.a k*t.allowanceStep A m k ≤
       t.token A M * box (2*d) * dry (distn t.a k/2) := by
   rw [transfer t A _ h hr]
   have hz := adjust t.a k (2*t.u+A*t.r)
   simp only [← add_assoc] at hz
   let e:=distn t.a k
   change salary _ _ *_ ≤ t.token A M * box (2*d)*dry (e/2)
   calc
     _ = t.token A M * (box (M/8-m/8)*dry e) := by
       unfold token allowance
       dsimp only
       unfold e
       have he := congrArg (fun x=> (dry (M/8)*box (M/8-m/8)*dry A)*x) hz
       linear_combination he
     _ ≤ _ := by
       rw [mul_assoc]
       apply mul_le_mul_of_nonneg_left _ (t.token_p ..).le
       have he : M/8 - m/8 + e/2 ≤ 2*d + e := by dsimp [e]; omega
       have ht :=box_mono he
       rw [boxP,boxP] at ht
       let b:=box e; let c:=box (e/2)
       unfold dry
       rw [← div_eq_mul_inv,← div_eq_mul_inv, div_le_div_iff₀ (box0 _) (box0 _)]
       exact ht

lemma raw_pay {m M A} {k s} (h:m≤M) (he1:distn t.a k<s) (he:M-m≤ s+1) (hp:0<t.r) :
    box (4*distn t.a k)*t.allowanceStep A m k ≤
          t.token A M*box (8*s)*dry (distn t.a k/2) := by
    rw [transfer t A _ h hp]
    unfold token allowance
    dsimp only
    let d:=distn t.a k
    have hz : 4*d+(M/8-m/8)+(2*k+2*t.u+A*t.r)+d/2 ≤
                    8*s + (2*t.a+2*t.u+A*t.r) := by
       dsimp only [d] at *
       unfold distn at *
       omega
    have ht:= box_mono hz
    rw [boxP _ (d/2),boxP _ (2*k+2*t.u+A*t.r),boxP _ (2*t.a+2*t.u+A*t.r),
             boxP (4*d)] at ht
    have hk:=mul_le_mul_of_nonneg_right ht (show 0≤dry (d/2) from (dry0 _).le)
    have hh : box (4*d)*box (M/8-m/8) * box (2*k+2*t.u+A*t.r) ≤
       box (8*s)*box (2*t.a+2*t.u+A*t.r)*dry (d/2) := by
        simpa only [mul_assoc,unify,mul_one] using hk
    have he:=mul_le_mul_of_nonneg_right hh (mul_nonneg (dry0 (M/8)).le (dry0 A).le)
    unfold d at he; linear_combination he

lemma unbias (A M) (h:0<t.r) : dry M ^3 ≤ t.token A M := by
   have he:dry M≤dry (M/8) := dry_mono (by omega)
   calc
     _ ≤ dry M := by
       have h1:= dry_one M; have h2:=dry0 M
       exact le_trans (pow_le_pow_of_le_one h2.le h1 (show 1≤ (3:ℕ) by omega)) (by rw [pow_one])
     _ ≤ _ := he
     _ ≤ _ := by
        unfold token allowance
        have hh : A≤2*t.a+2*t.u+A*t.r := by nlinarith
        rw [mul_assoc]
        have ht := mul_le_mul_of_nonneg_right (box_mono hh) (dry0 A).le
        rw [unify] at ht
        exact le_trans (le_of_eq (mul_one _).symm) (mul_le_mul_of_nonneg_left ht (dry0 _).le)
end StepKey

/-- coefficient remainders when summing all scale offsets/slack levels -/
lemma breeze_charge (s d : ℕ) (h : d≤ s) :
    box (8*s)* dry (18*s) ≤ dry (8*d)*dry s := by
   rw [show 18*s=8*s+10*s by omega,dryP,← mul_assoc, unify,one_mul,← dryP]
   exact dry_mono (by omega)

abbrev lull (a k : ℕ) := dry (distn a k/2)

lemma low_total (_ w : ℕ) : ∑ k∈range w,dry (k/2)≤4 := by
   let p (k : ℕ) := ∑ i∈range k,dry (i/2)
   have he (k : ℕ) : p (2*k)=2*∑ i∈range k,dry i := by
      induction k with
      | zero=>simp [p]
      | succ k ih=>
        unfold p
        rw [show 2*(k+1)=2*k+1+1 by omega,sum_range_succ,sum_range_succ,sum_range_succ (n:=k)]
        change p (2*k)+_+_ = _
        rw [ih,show 2*k/2=k by omega,show (2*k+1)/2=k by omega]; ring
   apply le_trans (b:=p (2*w))
   · unfold p
     exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) fun i _ _=>(dry0 _).le
   · rw [he]; linarith [thinSum (range w)]

lemma scale_total (F : Domain) (a) : ∑ k∈F,lull a k≤8 := by
   classical
   let T:=1+a+∑ k∈F,k
   let p (k:ℕ) :=dry (k/2)
   have ht (i) (h:i∈F) : i≤T := by
      have he :=single_le_sum (f:=fun i:ℕ=>i) (fun _ _=>Nat.zero_le _) h
      unfold T; omega
   let U:=F.filter (fun i=>i≤a)
   let V:=F.filter (fun i=>¬i≤a)
   have H (F : Finset ℕ) (f : ℕ→ℕ) (he:∀ i∈F,f i≤T)
       (hk:∀ i∈F,∀ j∈F,f i=f j → i=j) :
       ∑ i∈F,p (f i)≤4 := by
      rw [← sum_image (f:=p) (by intros i hi j hj; exact hk i hi j hj)]
      apply le_trans (b:=∑ i∈range (T+1),p i)
      · refine sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _=>(dry0 _).le)
        intro i hi
        obtain ⟨j,hj,rfl⟩:=mem_image.mp hi
        exact mem_range.2 (by have := he j hj; omega)
      exact low_total 0 _
   have h1 : ∑ i∈U, lull a i ≤4 := by
      apply le_trans (b:=∑ i∈U,p (a-i))
      · apply sum_le_sum
        intro i hi; unfold p lull distn; rw [Nat.sub_eq_zero_of_le (mem_filter.1 hi).2,add_zero]
      apply H
      · intro i hi; unfold T; omega
      intro i hi j hj e; obtain ⟨h1,h2⟩:=mem_filter.mp hi
      obtain ⟨h3,h4⟩:=mem_filter.mp hj; omega
   have h2 : ∑ i∈V, lull a i ≤4 := by
      apply le_trans (b:=∑ i∈V,p (i-a))
      · apply sum_le_sum
        intro i hi; unfold p lull distn; rw [Nat.sub_eq_zero_of_le (not_le.mp (mem_filter.1 hi).2).le,zero_add]
      apply H
      · intro i hi; exact le_trans (Nat.sub_le i a) (ht i (mem_filter.1 hi).1)
      intro i hi j hj e; obtain ⟨h1,h2⟩:=mem_filter.mp hi; obtain ⟨h3,h4⟩:=mem_filter.mp hj
      omega
   have e := sum_filter_add_sum_filter_not F (fun i=>i≤a) (lull a)
   rw [←e]; linarith

end
end ExactDerandomization.Est

end

section

namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

/-- Recipe-independent additive schedule. -/
structure Stair where
    M : ℕ
    A : ℕ
    key : StepKey
    lam : ℕ

namespace Stair

variable (s : Stair)
def L := s.M.log2 + 1
lemma length_pos : 0< s.L:= by unfold L; omega
def gap (i) := gapD s.L i
def cut (k) := distn s.key.a k+1
/-- budget reached by group i. Difference indices m denote the paired
evaluation at m+1 and m. -/
def reach (k i : ℕ) := s.M-max (s.gap i) (s.cut k)
def yoke (k : ℕ) : ℕ→ℕ
 | 0=>0
 | i+1=>s.reach k i

def layers (k i : ℕ) := Ico (s.yoke k i) (s.reach k i)
def slack (m : ℕ) := s.M-(m+1)
def theta (L k : ℕ) := s.key.allowanceStep s.A L k
def wide := s.key.token s.A s.M

lemma wide_nn : 0 ≤ s.wide := (s.key.token_p ..).le
lemma theta_nn (m k) : 0 ≤ s.theta m k := (StepKey.allow_p ..).le
lemma last (i) : s.gap i=2^(s.L-1-i) := rfl
lemma reach_le (k i) : s.reach k i≤ s.M - s.cut k := by
   unfold reach; omega
lemma reach_M (k i) : s.reach k i ≤ s.M := Nat.sub_le _ _
lemma reach_loss (k i) : s.M-s.reach k i ≤ s.gap i+s.cut k := by unfold reach; omega
lemma under (k i) : s.yoke k i ≤ s.reach k i := by
  cases i with
  | zero => exact Nat.zero_le _
  | succ i=>
    rw [yoke]; unfold reach
    have he : s.gap (i+1) ≤ s.gap i := gapD_mono (show i≤ i+1 by omega)
    omega

lemma precision (h : 0 < s.key.r) (k i) :
    salary s.key.a k*s.theta (s.reach k i) k ≤
       s.wide*box (2*s.gap i)*lull s.key.a k := by
   apply s.key.divide (s.reach_M k i) _ (gapD_pos ..) h
   simpa only [gap,cut,← add_assoc] using s.reach_loss k i

lemma cheap {m k i} (he:m< s.reach k i) :
    s.gap i ≤ s.slack m ∧ s.cut k ≤ s.slack m ∧ m+1< s.M := by
  have hh : 1 ≤ s.gap i:= gapD_pos ..
  unfold reach at he
  unfold slack; omega

lemma full {k i m} (h : m∈s.layers k i) (hh:i< s.L) :
    s.gap i≤ s.slack m ∧ s.slack m< 2*s.gap i := by
   obtain ⟨ha,hb⟩:=mem_Ico.1 h
   obtain ⟨hk,hl,ht⟩:=s.cheap hb
   refine ⟨hk,?_⟩
   cases i with
   | zero =>
     unfold gap gapD L
     have he : s.M< 2^(s.M.log2+1):= Nat.lt_log2_self
     rw [show s.M.log2+1-1-0=s.M.log2 by omega]; rw [pow_succ] at he
     unfold slack; omega
   | succ i=>
     change s.reach k i≤ m at ha
     have hx : s.gap i=s.gap (i+1)*2 := gapD_succ hh
     unfold reach at ha hb
     unfold slack; omega

lemma pegged {m k i} (h:0< s.key.r) (he:m< s.reach k i) {x} (hx:x=m ∨ x=m+1) :
    box (4*distn s.key.a k)*s.theta x k ≤
       s.wide*box (8*s.slack m)*lull s.key.a k := by
   obtain ⟨hc,hd,hm⟩:=s.cheap he
   apply s.key.raw_pay (by omega)
   · unfold cut at hd; omega
   · unfold slack; omega
   exact h

lemma slack_plan (i k) :
    ∑ j∈range (s.reach k i),dry (s.slack j) ≤2 := by
   rw [← sum_image (f:=dry)]
   · apply thinSum
   intro a ha b hb h; unfold slack at h
   replace ha:=mem_range.1 ha; replace hb:=mem_range.1 hb
   have he: a+1< s.M:=(s.cheap ha).2.2
   have hz: b+1< s.M:=(s.cheap hb).2.2
   omega

lemma union_sum (i k : ℕ) (f : ℕ→ℝ) :
    ∑ j∈range (s.yoke k i),f j + ∑ j∈s.layers k i,f j =
        ∑ j∈range (s.yoke k (i+1)),f j := by
   change _ + ∑ j∈Ico (s.yoke k i) (s.reach k i),f j= ∑ j∈range (s.reach k i), f j
   rw [sum_Ico_eq_sub f (s.under k i)]; ring

end Stair
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

variable {n : ℕ} [Fact n.Prime]
def toll (b:Bool) (w d:ℝ) := if b then rel w d else |w|
lemma rel_nn {x d : ℝ} (h:0≤d) : 0≤ rel x d := by unfold rel; positivity
lemma toll_nn {b x d} (h:0≤d) : 0≤toll b x d := by unfold toll; split; exact rel_nn h; positivity
lemma rel_tip {x d:ℝ} (h:0≤d) : rel x d≤ |x| := by
   apply le_trans (min_le_right ..)
   rw [div_le_iff₀ (by linarith)]
   nlinarith [abs_nonneg x]
lemma toll_tip {b x d} (h:0≤d) : toll b x d≤|x| := by unfold toll; split; exact rel_tip h; rfl
lemma rel_subadd {x y d : ℝ} (h:0≤d) : rel (x+y) d≤rel x d+rel y d := by
   obtain h0:0<1+d:=by linarith
   unfold rel
   have hx : 0≤|x|/(1+d):=by positivity
   have hy : 0≤|y|/(1+d):=by positivity
   have hh := div_le_div_of_nonneg_right (abs_add_le x y) h0.le
   rw [add_div] at hh; grind
lemma toll_add {b x y d} (h:0≤d) : toll b (x+y) d≤toll b x d+toll b y d := by
   cases b
   · exact abs_add_le _ _
   exact rel_subadd h
lemma toll_minus (b) (x d:ℝ) : toll b (-x) d=toll b x d := by simp [toll,rel]
lemma toll_sum {d : ℝ} {α : Type} (S : Finset α) (b : Bool) (h : 0≤d) (f : α→ℝ) :
   toll b (∑ i∈S,f i) d≤∑ i∈S,toll b (f i) d := by
   classical
   induction S using Finset.induction_on with
   | empty=>simp [toll,rel]
   | @insert i S hi ih=>
     rw [sum_insert hi,sum_insert hi]; exact le_trans (toll_add h) (add_le_add_right ih _)

structure Line (n : ℕ) where
   seq : ℕ→ Pics n
   account : Mat

namespace Line

variable (f : Line n)
def shake (m : ℕ) : Pics n:=fun s i j=> f.seq (m+1) s i j-f.seq m s i j
def pick (s : Stair) (d:Axis) (m) := d.fw (s.lam*s.slack m) (f.shake m)
def wear (s : Stair) (d : Axis) (m) := d.fluke (s.lam*s.slack m) (f.shake m)
def waveR (s : Stair) (d:Axis) (k i : ℕ) : Pics n :=
    fun u x y=> ∑ m∈ s.layers k i, f.pick s d m u x y
def weatherR (s : Stair) (d:Axis) (k i : ℕ) : Pics n :=
    fun u x y=> ∑ m∈range (s.yoke k i),f.wear s d m u x y

lemma zeroWeather (s k d u x y) : f.weatherR s d k 0 u x y=0 := by simp [weatherR,Stair.yoke]
lemma runoff (s : Stair) (d:Axis) (k i : ℕ) (hi:f.seq 0=fun _ _ _=>0)
   (u x y) :
   ∑ m∈range (s.yoke k i),f.pick s d m u x y=
       f.weatherR s d k i u x y+d.fm (f.seq (s.yoke k i)) x y := by
   have he (t) : ∑ m∈ range t,f.pick s d m u x y=
       ∑ m∈range t,f.wear s d m u x y+d.fm (f.seq t) x y := by
     induction t with
     | zero=> rw [hi]; simp only [range_zero,sum_empty,zero_add]
              simp [Axis.fm, Env.cond,av_zero]
     | succ t ih=>
       rw [sum_range_succ,sum_range_succ,ih,wear]
       have hm : d.fm (f.shake t) x y=d.fm (f.seq (t+1)) x y-d.fm (f.seq t) x y:=d.fmean_sub ..
       unfold Axis.fluke
       rw [hm]; unfold pick; ring
   exact he _
lemma storm (s k d i u x y) :
   f.weatherR s d k (i+1) u x y=f.weatherR s d k i u x y+
       ∑ m∈s.layers k i, f.wear s d m u x y :=
   Eq.symm (s.union_sum i _ _)

/-- Guarantees for one additive ray. -/
structure Due (s : Stair) (k : ℕ) (d : Axis) (D : Mat)
     (b : Bool) (c : ℝ) (f : Line n) : Prop where
    pos : 0≤c
    eve : f.seq 0=fun _ _ _=>0
    accuracy : ∀ m≤ s.M-s.cut k, d.ton (n:=n) (w:=0)
        (fun _ i j=> toll b (d.fm (f.seq m) i j - f.account i j) (D i j))
              ≤ c * salary s.key.a k*s.theta m k
    progress : ∀ m, m+1 ≤ s.M-s.cut k → d.ton (f.shake m)
                ≤ c * box (4*distn s.key.a k)*(s.theta m k+s.theta (m+1) k)

lemma Due.enlarge {s : Stair} {k d D b c c'} {f:Line n} (h:Due s k d D b c f)
     (he:c≤c') : Due s k d D b c' f := by
   refine ⟨h.pos.trans he,h.eve,fun m e=>(h.accuracy _ e).trans ?_,
      fun m e=>(h.progress _ e).trans ?_⟩
   · exact mul_le_mul_of_nonneg_right
       (mul_le_mul_of_nonneg_right he (paypos ..).le) (s.theta_nn ..)
   exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right he (box0 _).le)
                 (add_nonneg (s.theta_nn ..) (s.theta_nn ..))

lemma winning {s k d D b c} (h : Due s k d D b c f) (hr : 0< s.key.r) (i) :
   d.ton (n:=n) (w:=0)
        (fun _ x y=>toll b (d.fm (f.seq (s.reach k i)) x y-f.account x y) (D x y)) ≤
            c * s.wide * liftB 2 s.L i * lull s.key.a k := by
   apply (h.accuracy _ (s.reach_le k i)).trans
   have he := mul_le_mul_of_nonneg_left (s.precision hr k i) h.pos
   unfold liftB; unfold Stair.gap at he; linarith

lemma foggy {s k d D b c} (h : Due s k d D b c f) (hw:Wind 18 s.lam) (hr:0< s.key.r)
    (i) :
    d.ton (f.weatherR s d k (i+1)) ≤ 4*c*s.wide*decay s.L i*lull s.key.a k := by
   unfold weatherR
   apply le_trans (d.tseries (fun m=>f.wear s d m) _)
   let C:=2*c*s.wide *decay s.L i*lull s.key.a k
   have h0:=h.pos
   let u:=lull s.key.a k
   have hu : 0≤u:=(dry0 _).le
   have heC:0≤ C := by
     have :=s.wide_nn
     change 0≤2*c*s.wide*dry _*u; have hv:0≤dry (8*gapD s.L i):= (dry0 _).le
     positivity
   have he (m) (e:m< s.reach k i) :
      d.ton (f.wear s d m) ≤ C*dry (s.slack m) := by
     obtain ⟨h1,h2,h3⟩:= s.cheap e
     let r:=s.slack m
     have hs : 0<r:=lt_of_lt_of_le (gapD_pos ..) h1
     apply (d.windF hw hs _).trans
     have hf:=h.progress _ (le_trans (show m+1 ≤ s.reach k i from e) (s.reach_le ..))
     have ht:=s.pegged (k:=k) hr e (Or.inl rfl)
     have hx:=s.pegged (k:=k) hr e (Or.inr (Eq.refl (m+1)))
     have ha : d.ton (f.shake m) ≤ 2*c*(s.wide*box (8*r)*lull s.key.a k) := by
        apply hf.trans
        rw [mul_assoc c,mul_add (box _)]
        linarith [mul_le_mul_of_nonneg_left (add_le_add ht hx) h0]
     let K:= 2*c*s.wide*lull s.key.a k
     have hz:=mul_le_mul_of_nonneg_left ha (dry0 (18*r)).le
     have hj : 0 ≤ K := mul_nonneg (mul_nonneg (by positivity) s.wide_nn) hu
     have h' : box (8*r)*dry (18*r) ≤ decay s.L i*dry r:= breeze_charge r (s.gap i) h1
     have hy:=mul_le_mul_of_nonneg_left h' hj
     apply hz.trans
     unfold K at hy; unfold C; change _ ≤ _ * dry r
     linarith
   change ∑ x∈range (s.reach k i),_ ≤ _
   apply le_trans (sum_le_sum (fun j (hj:j∈range (s.reach k i))=> he j (mem_range.1 hj)))
   rw [←mul_sum]
   have hx := s.slack_plan i k
   apply le_trans (mul_le_mul_of_nonneg_left hx heC)
   exact le_of_eq (by dsimp [C]; ring)

end Line
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

variable {n : ℕ} [Fact n.Prime]

lemma opposing (d:Axis) (f g : Pics n) :
    d.ton (fun s i j=> f s i j-g s i j)=d.ton (fun s i j=> g s i j-f s i j) := by
   rw [← d.ton_subnorm, ← d.ton_subnorm (f:=fun s i j=> g s i j-f s i j)]
   congr! 2
   ext; rw [abs_sub_comm]
lemma joint (d : Axis) (f g a : Pics n) :
    d.ton (fun s i j=> f s i j-g s i j) ≤ d.ton (fun s i j=>a s i j-f s i j)+
                        d.ton (fun s i j=>a s i j-g s i j) := by
   rw [opposing d a f]
   have he := d.tplus (fun s i j=> f s i j-a s i j) (fun s i j=> a s i j-g s i j)
   simp only [sub_add_sub_cancel] at he; exact he

namespace Line

lemma Due.negR {f:Line n} {s k d D b c} (h : Due s k d D b c f) :
    Due s k d D b c ⟨fun m u i j=> -f.seq m u i j,fun i j=> -f.account i j⟩ := by
   have hs:= h.eve
   refine ⟨h.pos,by ext; simp [hs],fun m hi=>?_,fun m hi=>?_⟩
   · dsimp only
     have he (i j) : d.fm (fun u i j=> -f.seq m u i j) i j= -d.fm (f.seq m) i j := by
        simpa only [neg_mul,one_mul] using (d.fscalar (-1) (f.seq m) i j)
     simp_rw [he,show ∀ x y:ℝ, -x - -y = -(x-y) from by intros; ring,toll_minus]
     exact h.accuracy m hi
   · unfold shake; simp_rw [show ∀ x y:ℝ,-x - -y = y-x from by intros; ring]
     rw [opposing]; exact h.progress m hi

/-- Build unscaled strand, including a column rank or vector mean, from
ordinary discrepancy of its full estimates to true pre-mean inputs. -/
lemma plain {s : Stair} {f:Line n} {d : Axis} {D b c}
    (h:0≤c) {g:Pics n} (hd:∀ i∈d.S,∀ j∈d.S,0≤D i j)
    (hs:f.seq 0 = fun _ _ _=>0) (ht:∀ i∈d.S,∀ j∈d.S,d.fm g i j=f.account i j)
    (he:∀ m ≤ s.M-s.cut s.key.a,d.ton (fun u i j=>g u i j-f.seq m u i j) ≤
                  c*s.theta m s.key.a) : Due s s.key.a d D b c f := by
   let k:=s.key.a
   refine ⟨h,hs,fun m hm=>?_,fun m hm=>?_⟩
   · let w:Pics n:=fun u i j=>f.seq m u i j-g u i j
     have hh := he _ hm
     have hg (u:Pool n) (i j) (hi:i∈src d.S d.u u) (hj:j∈dst d.S d.a u) :
        |toll b (d.fm (f.seq m) i j-f.account i j) (D i j)| ≤ |d.fm w i j| := by
          have hx := hd i (mem_filter.1 hi).1 j (mem_filter.1 hj).1
          rw [← ht i (mem_filter.1 hi).1 j (mem_filter.1 hj).1, show d.fm w i j=_ from d.fmean_sub ..,abs_of_nonneg (toll_nn hx)]
          exact toll_tip hx
     have hw := d.torder hg
     refine hw.trans ?_
     rw [d.ton_subnorm (f:=fun s i j=> d.fm w i j)]
     apply (d.fnorm w).trans
     unfold w
     rw [opposing]
     simpa [salary,box] using hh
   · have ht1:= joint d (f.seq (m+1)) (f.seq m) g
     apply ht1.trans
     have h1:= he (m+1) hm; have h2:=he m (by omega)
     simp only [distn,Nat.sub_self,Nat.zero_add,Nat.mul_zero,box,pow_zero,mul_one]
     linarith

lemma principal {s : Stair} {k : ℕ} {d : Axis} {D : Mat} {c K : ℝ} {f:Line n}
    (h0 : d.a=s.key.a)
    {a : ℕ→ Pics n} {g : Pics n}
    (hs:f.seq=fun m=> d.carry k (a m)) (ha:a 0=fun _ _ _=>0)
    (he : ∀ i∈d.S,∀ j∈d.S,d.fm (d.carry k g) i j=f.account i j)
    (hh : ∀ i∈d.S,∀ j∈d.S,f.account i j≤K*D i j)
    (hd : ∀ i∈d.S,∀ j∈d.S,0≤D i j) (hu:1≤K) (hc:0≤c)
    (hn:2^nar d.a k≤n)
    (hp : RCap K g) (hr:d.pinned (nar d.a k) g)
    (h:∀ m ≤ s.M-s.cut k,RCap K (a m) ∧ d.pinned (nar d.a k) (a m) ∧
           (d.narrowed (nar d.a k)).terr g (a m) ≤ c*s.theta m k) :
    Due s k d D true (Axis.paycheck K*c) f := by
   have hhk:0≤K:=by linarith
   have hv : 0≤Axis.paycheck K:=by unfold Axis.paycheck; positivity
   refine ⟨by positivity,?_,fun m hm=>?_,fun m hm=>?_⟩
   · rw [hs]; ext; simp only [ha,Axis.carry,mul_zero]
   · replace hh (i) (hi:i∈d.S) (j) (hj:j∈d.S) :
         d.fm (d.carry k g) i j≤K*D i j := by rw [he _ hi _ hj]; exact hh _ hi _ hj
     obtain ⟨h1,h2,h3⟩:=h m hm
     have ht := d.stream_fee hn hu hp h1 hr h2 hd hh
     have hy (i j) (hi:i∈d.S) (hj:j∈d.S) : toll true (d.fm (f.seq m) i j-f.account i j) (D i j)=
           rel (d.fm (d.carry k g) i j-d.fm (d.carry k (a m)) i j) (D i j) := by
        rw [hs,← he i hi j hj]; unfold toll rel; rw [abs_sub_comm]; rfl
     rw [d.ton_ext (f:=fun (_:Pool n) i j=> _) (g:=fun u i j=>
          rel (d.fm (d.carry k g) i j-d.fm (d.carry k (a m)) i j) (D i j))
                              (fun _ _ _ hi hj=>hy _ _ (mem_filter.1 hi).1 (mem_filter.1 hj).1)]
     have hx :=mul_le_mul_of_nonneg_left h3
         (show 0 ≤ Axis.paycheck K * salary d.a k from mul_nonneg hv (paypos _ _).le)
     apply (ht.trans hx).trans; rw [h0]; exact le_of_eq (by ring)
   · have hu (j : ℕ) (hj:j≤ s.M-s.cut k) :
       d.ton (fun u i t=>d.carry k g u i t-f.seq j u i t)≤
             Axis.paycheck K*c*box (4*distn s.key.a k)*s.theta j k := by
        obtain ⟨h1,h2,h3⟩:=h j hj
        rw [hs]
        have ht:= d.raw_fee hn hu hp h1 hr h2
        apply ht.trans
        apply le_trans (mul_le_mul_of_nonneg_left h3
          (show 0≤Axis.paycheck K*box (4*distn d.a k) from mul_nonneg hv (box0 _).le))
        rw [h0]; exact le_of_eq (by ring)
     unfold shake
     apply (joint d _ _ (d.carry k g)).trans
     linarith [hu (m+1) hm,hu m (by omega)]

end Line
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

abbrev Ray := ℕ × ℕ

structure Flame (n : ℕ) where
   rays : Finset Ray
   lines : Ray→Line n
   lamp : Mat
   base : Mat

namespace Flame
variable {n : ℕ} [Fact n.Prime]
variable (f : Flame n)

def first (i : ℕ) := if i=0 then (fun _ _=>(0:ℝ)) else f.base
def portion (s : Stair) (d : Axis) (i : ℕ) : Pics n :=
   fun u x y=> ∑ t∈f.rays,(f.lines t).waveR s d t.1 i u x y+
                          (if i=0 then f.base x y else 0)
def bundle (s : Stair) (d : Axis) (i : ℕ) : Pics n :=
   fun u x y=> if x∈src d.S d.u u ∧ y∈dst d.S d.a u then f.portion s d i u x y else 0

def prefixR (s : Stair) (d : Axis) (i:ℕ) : Pics n :=
   fun u x y=> ∑ t∈f.rays,∑ m∈range (s.yoke t.1 i),(f.lines t).pick s d m u x y
                  + f.first i x y
def central (s : Stair) (d:Axis) (i:ℕ) : Mat :=
   fun x y=> ∑ t∈f.rays,d.fm ((f.lines t).seq (s.yoke t.1 i)) x y + f.first i x y
def smoke (s : Stair) (d:Axis) (i:ℕ) : Pics n :=
   fun u x y=> ∑ t∈f.rays,(f.lines t).weatherR s d t.1 i u x y

lemma prefix0 (s d u x y) : f.prefixR s d 0 u x y=0 := by simp [prefixR,first, Stair.yoke]
lemma next (s d i u x y) :
    f.prefixR s d i u x y+f.portion s d i u x y=f.prefixR s d (i+1) u x y := by
   unfold prefixR portion
   let p (j : ℕ) (t:Ray) := ∑ m ∈ range (s.yoke t.1 j),(f.lines (t:Ray)).pick s d m u x y
   have H (t:Ray) : p i t+(f.lines t).waveR s d t.1 i u x y = p (i+1) t :=
      s.union_sum i _ _
   have he : f.first i x y + (if i=0 then f.base x y else 0)=f.first (i+1) x y := by
      unfold first; by_cases hi:i=0 <;> simp [hi]
   have ht := sum_congr rfl (s₁:=f.rays) fun t _=> H t
   rw [sum_add_distrib] at ht
   change ∑ t∈f.rays,p i t+f.first i x y+(∑ t∈f.rays,_ +_) =
                ∑ t∈f.rays,p (i+1) t+ _
   linarith

def tail (x y : ℕ) :=
    f.lamp x y-f.base x y-∑ t∈f.rays,(f.lines t).account x y

structure Owes (s : Stair) (d : Axis) (b : Bool) (c : ℝ) (f : Flame n) : Prop where
    on : 0< s.key.r
    breeze : Wind 18 s.lam
    coef : 1≤c
    due : ∀ t∈ f.rays,Line.Due s t.1 d f.lamp b c (f.lines t)
    gone : d.ton (n:=n) (w:=0) (fun _=> f.tail) ≤ c*s.wide
    heat : ∑ t∈f.rays,lull s.key.a t.1 ≤ c
    positive : ∀ x∈d.S,∀ y∈d.S,0≤ f.lamp x y

lemma Owes.more {s : Stair} {d b c c'} {f : Flame n} (h:Owes s d b c f) (he:c≤c') :
   Owes s d b c' f :=
   ⟨h.on,h.breeze,h.coef.trans he,fun i hi=>(h.due i hi).enlarge he,
          h.gone.trans (mul_le_mul_of_nonneg_right he s.wide_nn),
          h.heat.trans he,h.positive⟩

lemma coupling {s d b c} (h:Owes s d b c f) (i u x y) :
    f.prefixR s d i u x y=f.central s d i x y+f.smoke s d i u x y := by
  unfold prefixR central smoke
  have hx := sum_congr (s₁:=f.rays) rfl fun j hj=>
                        (f.lines j).runoff s d j.1 i (h.due j hj).eve u x y
  rw [sum_add_distrib] at hx; rw [hx]; ring

abbrev contract (s:Stair) (c:ℝ) := (4*c^2)*s.wide
lemma protocol {s : Stair} {c : ℝ} : 0≤contract s c :=
   mul_nonneg (by positivity) (s.wide_nn)

lemma fumes {s d b c} (h:Owes s d b c f) (i : ℕ) :
    d.ton (f.smoke s d (i+1)) ≤ contract s c*decay s.L i := by
   apply le_trans (d.tseries (fun j=> (f.lines j).weatherR s d j.1 (i+1)) _)
   apply le_trans (sum_le_sum (fun j hj=>(f.lines j).foggy (h.due j hj) h.breeze h.on i))
   rw [← mul_sum]
   have hp:= s.wide_nn; have hc:0≤c:= le_trans zero_le_one h.coef
   have hs : 0≤ decay s.L i:=(dry0 _).le
   apply le_trans (mul_le_mul_of_nonneg_left h.heat (by positivity))
   exact le_of_eq (by unfold contract; ring)

def picture (s : Stair) (d : Axis) (b : Bool) (i : ℕ) : Mat :=
   fun x y=>toll b (f.central s d (i+1) x y-f.lamp x y) (f.lamp x y)

lemma pink {s d b c} (h:Owes s d b c f) (i : ℕ) :
    d.ton (n:=n) (w:=0) (fun _=>f.picture s d b i) ≤ contract s c*liftB 2 s.L i := by
   let p (j:Ray) : Mat:= fun x y=> d.fm ((f.lines j).seq (s.reach j.1 i)) x y-
                                         (f.lines j).account x y
   let m (j:Ray) : Pics n:= fun _ x y=> toll b (p j x y) (f.lamp x y)
   let v : Pics n := fun u x y=> ∑ j∈f.rays,m j u x y
   let z : Pics n:= fun _ x y=> |f.tail x y|
   have he (u:Pool n) (x y:ℕ) (hx:x∈ src d.S d.u u) (hy:y∈dst d.S d.a u) :
      |f.picture s d b i x y|≤ v u x y+z u x y := by
       have hl := h.positive x (mem_filter.1 hx).1 y (mem_filter.1 hy).1
       have hz : f.central s d (i+1) x y - f.lamp x y =
                       ∑ j∈f.rays,p j x y+ -(f.tail x y) := by
          simp only [central,first,p,tail,sum_sub_distrib,show i+1≠0 by omega, ↓reduceIte,
            Stair.yoke]
          ring
       unfold picture; rw [abs_of_nonneg (toll_nn hl),hz]
       apply (toll_add hl).trans
       refine add_le_add (toll_sum _ _ hl _) (by rw [toll_minus]; exact toll_tip hl)
   have hs := d.torder he
   apply hs.trans
   apply (d.tplus v z).trans
   have h1 : d.ton z ≤ c*s.wide := by
      unfold z; rw [d.ton_subnorm]; exact h.gone
   let u:=liftB 2 s.L i
   have h0 := h.coef; have hp:=s.wide_nn
   have hu:1 ≤ u:=lift_one ..
   have h2 : d.ton v ≤ c^2*s.wide*u := by
      apply le_trans (d.tseries m _)
      apply le_trans (sum_le_sum (fun j hj=> show d.ton (m j) ≤ c*s.wide*u*lull s.key.a j.1 from
                          (f.lines j).winning (h.due j hj) h.on i))
      rw [← mul_sum]
      apply le_trans (mul_le_mul_of_nonneg_left h.heat (by positivity))
      exact le_of_eq (by ring)
   unfold contract; change _ ≤ _ * u
   have hh : c*s.wide ≤ c^2*s.wide*u :=
       le_trans (mul_le_mul_of_nonneg_right (by nlinarith : c ≤ c^2) hp)
                  (by nlinarith [show 0≤c^2*s.wide from by positivity])
   have hk : 0 ≤ c^2*s.wide*u := by positivity
   linarith

lemma tip_noise {s d b c} (h:Owes s d b c f) (i u) {x y}
   (hx:x∈d.S) (hy:y∈d.S) :
   toll b (f.prefixR s d (i+1) u x y-f.lamp x y) (f.lamp x y) ≤
            f.picture s d b i x y + |f.smoke s d (i+1) u x y| := by
   rw [f.coupling h,show f.central s d (i+1) x y+ f.smoke s d (i+1) u x y-f.lamp x y=
           f.central s d (i+1) x y-f.lamp x y+ f.smoke s d (i+1) u x y by ring]
   have he := h.positive _ hx _ hy
   exact (toll_add he).trans (add_le_add_right (toll_tip he) _)

end Flame
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 2048
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie Buf At Finset

variable {n w : ℕ} [Fact n.Prime]
/-- Inputs to the compression estimate. -/
structure Spray (n w : ℕ) [Fact n.Prime] where
    d : Axis
    t : ℕ
    L : ℕ
    K : ℕ
    b : ℕ
    a : Mat
    q : Mat
    inc : ℕ → X n w→ℕ → Buf.Row
    lead : ℕ → Mat
    seedB : ℕ → Mat
    fog : ℕ → TableF n w

namespace Spray
variable (s : Spray n w)
abbrev dst0 (i : X n w) := dst s.d.S s.d.a i
abbrev dst1 (i : X n w) := dst s.d.S s.t i
abbrev src0 (i : X n w) := src s.d.S s.d.u i
def go (u : X n w) (i : ℕ) : Run :=
   ⟨s.L,s.dst0 u,s.K,capacity s.b s.K s.L,floorR s.b s.L,fun j=>s.inc j u i,
       fun x=>(s.a i x, if x∈s.dst1 u then s.q i x else 0)⟩
def s1 (j : ℕ) : TableF n w := fun _=> s.lead j
def s2 (j:ℕ) : TableF n w := s.d.wmask s.t (fun _=>s.seedB j)
def pay (j:ℕ) : TableF n w := fun u i x=> s.s1 j u i x+s.s2 j u i x+s.fog j u i x

structure Works (p M : ℝ) : Prop where
    pos : 0≤ p
    mass : 1≤ M
    len : 0<s.L
    legal : Hie.legal n s.d.S
    kind : s.d.a≤ s.t
    window : 2^s.d.a ≤ n
    side : ∀ i∈s.d.S, ∀ j∈s.d.S,0≤ s.a i j ∧ |s.q i j|≤zeta ∧
                         (s.a i j ≤ At.small → s.q i j=0)
    row : ∀ i∈s.d.S,(∑ j ∈ s.d.S,s.a i j)*rate s.d.a ≤M
    error : ∀ j<s.L,∀ u,∀ i∈s.src0 u,∀ x∈s.dst0 u,(s.go u i).epi j x≤ s.pay j u i x
    h1 : ∀ j<s.L,s.d.ton (s.s1 j) ≤ p*liftB s.b s.L j
    h2 : ∀ j<s.L,s.d.ton (s.s2 j) ≤ p*liftB s.b s.L j
    noise : ∀ j<s.L,s.d.ton (s.fog j) ≤ p*decay s.L j

lemma ok {p M} (h:s.Works p M) {u i} (he:i∈s.src0 u) : (s.go u i).Good := by
    have H (j) (hj : j∈s.dst0 u) := h.side i (mem_filter.1 he).1 j (mem_filter.1 hj).1
    exact ⟨fun j _=>floor_pos ..,totaldust ..,fun i hi=>lead_dust _ _ _ hi,fun i _=>cap_K ..,
        fun j hj=>(H j hj).1,fun j hj=>by
         have := (H j hj).2.1
         by_cases h:j∈s.dst1 u <;> simp only [go,h,ite_true,ite_false]
         · exact this
         simp [zeta]; have :=smallp; positivity,
        fun j hj hx=> by
         have h := (H _ hj).2.2 hx
         simp [go,h]⟩

lemma pay_pub {p M} (h:s.Works p M) {i} (hi:i<s.L) :
    s.d.ton (s.pay i) ≤ 3*p*liftB s.b s.L i := by
   apply le_trans (s.d.tplus _ (s.fog i))
   have he := s.d.tplus (s.s1 i) (s.s2 i)
   have hv:=mul_le_mul_of_nonneg_left (decay_le s.b s.L i) h.pos
   linarith [h.noise i hi,h.h1 i hi,h.h2 i hi]

def heavy (i x : ℕ) :=
   s.d.S.filter fun j=> floorR s.b s.L i/4 < s.a x j
lemma binge_bits (j : ℕ) u i :
    (s.go u i).fatties j = retain s.d.a (s.heavy j i) u.2.1 := by
   ext x; simp only [go,Run.fatties,dst0,dst,retain,heavy,mem_filter]; tauto
def busy (j i : ℕ) (u : Channel n) : Prop :=
   capacity s.b s.K s.L j ≤ 2*(retain s.d.a (s.heavy j i) u).card
instance (j i : ℕ) (u : Channel n) : Decidable (s.busy j i u) := by unfold busy; infer_instance
lemma wrapped (j) u i : (s.go u i).binge j ↔ s.busy j i u.2.1 := by
   rw [Run.binge, binge_bits]; rfl

lemma cut_belly {p M} (h:s.Works p M) (j) {x} (hx:x∈s.d.S) :
   ((s.heavy j x).card:ℝ)*floorR s.b s.L j*rate s.d.a ≤ 4*M := by
   let u:=floorR s.b s.L j
   have he : (s.heavy j x).card * (u/4) ≤ ∑ k∈s.d.S,s.a x k := calc
      _ = ∑ i∈s.heavy j x, u/4 := by simp
      _ ≤ ∑ i∈s.heavy j x, s.a x i := sum_le_sum fun i hi=> le_of_lt (mem_filter.1 hi).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..)
                          fun i hi _=>(h.side _ hx _ hi).1
   have ht:= h.row x hx
   have hk := le_trans (mul_le_mul_of_nonneg_right he (rate_pos _).le) ht
   change _*u*_ ≤ _
   linarith

abbrev hefty (M : ℝ) := 1024*M
lemma raid {p M} (h:s.Works p M) (t i) {x y : ℕ} (hx:x∈s.d.S) (hy:y∈s.d.S) :
  atP t (↑y:ZMod n) (fun c:Channel n=> if s.busy i x c then (1:ℝ) else 0)
   ≤ (hefty M * firm s.b s.K s.L i)^4 := by
   let N : ℝ := capacity s.b s.K s.L i
   let z := floorR s.b s.L i
   let l:= s.heavy i x
   let R :=rate s.d.a
   let m := atP t (↑y:ZMod n) (fun c:Channel n=>if s.busy i x c then (1:ℝ) else 0)
   have hh : N*m ≤ 2*atP t (↑y:ZMod n) (tally s.d.a l) := by
      unfold m atP; rw [← av_cmul,← av_cmul]
      apply av_mono
      intro c; dsimp only; split
      · next e=>
        rw [mul_one]
        unfold busy at e; unfold N tally l
        exact_mod_cast e
      · rw [mul_zero]; unfold tally; positivity
   have hcap:=feed_power s.b s.K s.L i
   have hT : atP t (↑y:ZMod n) (tally s.d.a l)≤ 1+(l.card:ℝ)*(32*R):=
     tally_cond (S:=l) (fun i hi=>h.legal ((filter_subset _ _) hi)) h.window _ (mem_range.1 (h.legal hy))
   have hl:=s.cut_belly h i hx
   have hM:=h.mass
   have hz : 0<z:= floor_pos ..
   have hz' : z≤1:=dry_one _
   have hN : 0<N := by unfold N; exact_mod_cast cap_pos s.b s.K s.L i
   change (l.card:ℝ)*z*R≤4*M at hl
   change 1≤ N*z*(firm s.b s.K s.L i)^4 at hcap
   change m≤_
   apply le_of_mul_le_mul_left _ (show 0<N*z by positivity)
   have he2 : N*z*m ≤260*M := by
      have ht : N*m ≤2*(1+l.card*32*R) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left ht hz.le]
   apply le_trans he2 _
   have hE0 : hefty M ≥ 1024 := by unfold hefty; linarith
   have hE : 260*M ≤ (hefty M)^4 := by unfold hefty at *; nlinarith [sq_nonneg (M^2-1)]
   have hk:=mul_le_mul_of_nonneg_left hcap (show 0≤ (hefty M)^4 by positivity)
   rw [mul_pow]; linarith

end Spray
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 2048
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset
open scoped Classical

namespace Spray
variable {n w : ℕ} [Fact n.Prime]
variable (s : Spray n w)
def mh (j : ℕ) : Vertex n w := fun u i=> s.d.head (s.s1 j) u i+s.d.head (s.s2 j) u i
def nh (j : ℕ) := s.d.head (s.fog j)
def both (j : ℕ) : Vertex n w := fun u i=> s.mh j u i+s.nh j u i

lemma mnn (j) u i : 0≤ s.mh j u i:=add_nonneg (Axis.head_nn ..) (Axis.head_nn ..)
lemma nnn (j) u i : 0≤ s.nh j u i:=Axis.head_nn ..
lemma bnn (j) u i : 0≤ s.both j u i:=add_nonneg (s.mnn j u i) (s.nnn j u i)
lemma pointed {j p M} (h:s.Works p M) (hz:j<s.L) {u i} (hi:i∈s.src0 u) :
    (s.go u i).bad j ≤ s.both j u i := by
   apply rank_le (s.bnn ..)
   intro k hk
   apply le_trans (h.error j hz u i hi k hk)
   have hu (f : TableF n w) : f u i k ≤ s.d.head f u i :=
      le_trans (le_abs_self _) (s.d.head_ge f u i hk)
   exact add_le_add (add_le_add (hu ..) (hu ..)) (hu ..)

lemma nh_ub {p M} (h:s.Works p M) {j} (hi : j<s.L) :
    s.d.von (s.nh j) ≤ p*decay s.L j := by rw [nh,s.d.head_e]; exact h.noise _ hi
lemma mh_ub {p M} (h:s.Works p M) {j} (hi:j<s.L) :
    s.d.von (s.mh j) ≤ 2*p*liftB s.b s.L j := by
   apply le_trans (s.d.vplus (s.d.head (s.s1 j)) (s.d.head (s.s2 j)))
   rw [s.d.head_e,s.d.head_e]; linarith [h.h1 j hi,h.h2 j hi]
lemma both_ub {p M} (h:s.Works p M) {j} (hi:j<s.L) :
    s.d.von (s.both j) ≤3*p*liftB s.b s.L j := by
   apply le_trans (s.d.vplus (s.mh j) (s.nh j))
   have he := s.mh_ub h hi; have hn := s.nh_ub h hi
   linarith [mul_le_mul_of_nonneg_left (decay_le s.b s.L j) h.pos]

def phantom (j : ℕ) : Vertex n w :=
    fun u i=> if (s.go u i).hap j ∧ ¬(s.go u i).binge j then 1 else 0
lemma false_nn (j) u i : 0≤ s.phantom j u i := by unfold phantom; split <;> norm_num
abbrev fc (s : Spray n w) (i : ℕ) := firm s.b s.K s.L i
set_option maxHeartbeats 500000 in
lemma false_ub {p M} (h:s.Works p M) {j} (hi:j<s.L) :
    s.d.von (s.phantom j) ≤ 64*s.fc j*p*liftB s.b s.L j := by
   let N:ℝ:=capacity s.b s.K s.L j
   let R:=floorR s.b s.L j
   let A:= N/2*(R/8)^4
   let b:=liftB s.b s.L j
   let e:=s.fc j
   let f:=s.pay j
   have he (u) (i) (hx:i∈s.src0 u) :
       A*(s.phantom j u i)^4 ≤ ∑ k∈s.dst0 u,(f u i k)^4 := by
     unfold phantom; split
     · next hn=>
       simp only [one_pow,mul_one]
       apply le_trans (Run.fake (s.go u i) (s.ok h hx) hi hn.1 hn.2)
       apply sum_le_sum; intro k hk
       exact pow_le_pow_left₀ (Run.epi_nn ..) (h.error j hi u i hx k hk) 4
     · simp only [zero_pow ((show (4:ℕ) ≠ 0 by omega)),mul_zero]
       exact sum_nonneg fun _ _ => by positivity
   have ht : A * s.d.von (s.phantom j)^4≤ (3*p*b)^4 := calc
     _ = s.d.vi (fun u i=>A*s.phantom j u i^4) := by rw [s.d.von_four,s.d.vmul]
     _ ≤ _ := s.d.vi_mono he
     _ = s.d.ton (s.pay j)^4 := (s.d.ton_four _).symm
     _ ≤ _ := pow_le_pow_left₀ (s.d.tn0 _) (s.pay_pub h hi) _
   have hp:=h.pos; have hN : 0<N := by unfold N; exact_mod_cast cap_pos s.b s.K s.L j
   have hR : 0 < R:= floor_pos ..
   have hz : 0<e:= dry0 _
   have hb : 0<b:= box0 _
   have hu : 1 ≤ N*R^4*e^4 := forfeit s.b s.K s.L j
   change _ ≤ 64*e*p*b
   apply (s.d.vm_le (by positivity)).mpr
   rw [← s.d.von_four]
   apply le_of_mul_le_mul_left _ (show 0<A by unfold A; positivity)
   apply ht.trans
   let d:=p*b
   have hg : d^4 ≤ N*R^4*e^4*d^4 := by
      simpa using mul_le_mul_of_nonneg_right hu (show 0 ≤ d^4 by positivity)
   rw [show 3*p*b=3*d by dsimp [d]; ring, show 64*e*p*b=64*e*d by dsimp [d]; ring]
   unfold A
   nlinarith [show 0≤d^4 by positivity]

def chip (j : ℕ) (f : TableF n w) : TableF n w :=
    fun u i k=> if s.busy j i u.2.1 then f u i k else 0
def chipV (j : ℕ) (f : Vertex n w) : Vertex n w :=
    fun u i=> if s.busy j i u.2.1 then f u i else 0

lemma chipH (j : ℕ) (f : TableF n w) :
    s.chipV j (s.d.head f)=s.d.head (s.chip j f) := by
   ext u i; exact (s.d.head_mask (fun u i=>s.busy j i u.2.1) f u i).symm

lemma busy_avg {p M} (h:s.Works p M) (j l) {x y : ℕ}
    (hx:x∈s.d.S) (hy:y∈s.d.S) (u : ℝ) :
      @Env.cond n w _ s.d.u l (↑x:ZMod n) (↑y:ZMod n)
          (fun c=> (if s.busy j x c.2.1 then u else 0)^4)
        ≤ (hefty M*s.fc j)^4*
             @Env.cond n w _ s.d.u l (↑x:ZMod n) (↑y:ZMod n) (fun _ => u^4) := by
   let F (c : Channel n) := (if s.busy j x c then u else 0)^4
   have he1 : @Env.cond n w _ s.d.u l (↑x:ZMod n) (↑y:ZMod n) (fun c=> F c.2.1)=
                   atP l (↑y:ZMod n) F := by
      unfold Env.cond atP
      simp only [av_prod,Env.outward,av_const]
   have hA (c:Channel n) : F c=u^4*(if s.busy j x c then (1:ℝ) else 0) := by
        unfold F; split <;> norm_num
   change @Env.cond n w _ _ _ _ _ (fun c=> F c.2.1) ≤ _
   rw [he1]
   simp only [Env.cond,atP,hA,av_const,av_cmul]
   have hv:=s.raid h l j hx hy
   conv_rhs => rw [mul_comm]
   exact mul_le_mul_of_nonneg_left hv (show 0≤u^4 by positivity)

set_option maxHeartbeats 500000 in
lemma slice_costa {p M} (h:s.Works p M) (j l) (f : Mat) :
    (s.d.narrowed l).ton (s.chip j (fun _=> f)) ≤
       hefty M*s.fc j*(s.d.narrowed l).ton (fun (_:X n w)=> f) := by
   let d:=s.d.narrowed l
   let c:=hefty M*s.fc j
   have hc:0<c := mul_pos (show 0<hefty M by unfold hefty; linarith [h.mass]) (dry0 _)
   change d.ton _ ≤ c*d.ton _
   apply (d.tm_le (mul_nonneg hc.le (d.tn0 _))).mpr
   rw [mul_pow,d.ton_four, d.conditional,d.conditional]
   rw [mul_left_comm (c^4)]
   apply mul_le_mul_of_nonneg_left _ (scaleM_nn ..)
   rw [mul_sum]
   apply sum_le_sum; intro x hx
   rw [mul_sum]
   apply sum_le_sum; intro y hy
   rw [mul_left_comm (c^4)]
   refine mul_le_mul_of_nonneg_left (busy_avg s h j _ hx hy _) ?_
   exact mul_nonneg (pct_pos (NeZero.pos n) _).le (pct_pos (NeZero.pos n) _).le

lemma masked_leaf {p M} (h:s.Works p M) (i j) :
    s.d.von (s.chipV i (s.mh j)) ≤
      hefty M*s.fc i*(s.d.ton (s.s1 j)+s.d.ton (s.s2 j)) := by
   let w1:=s.d.head (s.s1 j)
   let w2:=s.d.head (s.s2 j)
   have he : s.chipV i (s.mh j)=fun u x=>s.chipV i w1 u x+s.chipV i w2 u x := by
      ext u x; unfold chipV; split
      · rfl
      · norm_num
   rw [he,mul_add]
   apply (s.d.vplus (s.chipV i w1) (s.chipV i w2)).trans (add_le_add ?_ ?_)
   · unfold w1
     rw [chipH,s.d.head_e]
     exact s.slice_costa h i s.d.a (s.lead j)
   unfold w2; rw [chipH,s.d.head_e]; unfold s2
   have hv (f : TableF n w) : s.chip i (s.d.wmask s.t f)=s.d.wmask s.t (s.chip i f) := by
      ext u x y; unfold chip Axis.wmask; grind
   rw [hv,s.d.tmask s.t h.kind,s.d.tmask s.t h.kind]
   exact s.slice_costa h i s.t (s.seedB j)
lemma masked_ub {p M} (h:s.Works p M) (i j) (he:j<s.L) :
    s.d.von (s.chipV i (s.mh j)) ≤
               hefty M*s.fc i*(2*p*liftB s.b s.L j) := by
   have ht : 0≤ hefty M := by unfold hefty; linarith [h.mass]
   apply (s.masked_leaf h i j).trans (mul_le_mul_of_nonneg_left _ (mul_nonneg ht (dry0 _).le))
   linarith [h.h1 j he,h.h2 j he]

end Spray
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 2048
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset
open scoped Classical

namespace Spray
variable {n w : ℕ} [Fact n.Prime]
variable (s : Spray n w)

def sky (j : ℕ) : Vertex n w :=
   fun u i => (24/small * floorR s.b s.L j)*s.both j u i
def clouds : Vertex n w :=
   fun u i=>∑ j∈range s.L,s.sky j u i
def trail (j : ℕ) : Vertex n w :=
   fun u i=>∑ k∈Ico j s.L,(32:ℝ)^(s.L-k)*s.chipV j (s.mh k) u i
def march : Vertex n w :=
   fun u i=>∑ j∈range s.L,s.trail j u i
def rim : Vertex n w :=
   fun u i=>32*s.mh (s.L-1) u i
def thunder : Vertex n w :=
   fun u i=>∑ j∈range s.L,(32:ℝ)^(s.L-j)*s.nh j u i
def beasts : Vertex n w :=
   fun u i=> ∑ j∈range s.L,s.phantom j u i
def sumB : Vertex n w :=
   fun u i=> s.clouds u i+s.march u i+s.rim u i+s.thunder u i+s.beasts u i

lemma sky_nn (j) u i : 0≤ s.sky j u i := mul_nonneg
    (mul_nonneg (div_nonneg (by norm_num) smallp.le) (floor_pos ..).le) (s.bnn ..)
lemma clouds_nn u i : 0≤ s.clouds u i:=sum_nonneg fun _ _=> s.sky_nn ..
lemma trail_nn (j) u i : 0≤ s.trail j u i :=
    sum_nonneg fun k _=>mul_nonneg (by positivity) (by unfold chipV; split; apply s.mnn; norm_num)
lemma march_nn u i : 0≤ s.march u i:=sum_nonneg fun _ _=>s.trail_nn ..
lemma rim_nn u i : 0≤ s.rim u i:=mul_nonneg (by norm_num) (s.mnn ..)
lemma thunder_nn u i : 0≤ s.thunder u i:=
    sum_nonneg fun k _=>mul_nonneg (by positivity) (s.nnn ..)
lemma beasts_nn u i : 0≤ s.beasts u i:=sum_nonneg fun _ _=>s.false_nn ..
lemma sumB_nn u i : 0 ≤ s.sumB u i := by
   unfold sumB; linarith [s.clouds_nn u i,s.march_nn u i,s.rim_nn u i,s.thunder_nn u i,
                      s.beasts_nn u i]

lemma cloud_plan {p M} (h:s.Works p M) {u i} (hs:i∈s.src0 u) {j} (hj:j<s.L) :
    (s.go u i).rain j ≤ s.clouds u i := by
   unfold Run.rain clouds
   refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (range_mono hj.le) (fun x hx _=>s.sky_nn x u i))
   apply sum_le_sum; intro k hk
   exact mul_le_mul_of_nonneg_left (s.pointed h ((mem_range.1 hk).trans hj) hs)
     (mul_nonneg (div_nonneg (by norm_num) smallp.le) (floor_pos ..).le)

lemma tail_route {p M} (h:s.Works p M) {u i} (hs:i∈s.src0 u) {j} (hi:j<s.L)
    (hh : s.L=j+1 ∨ (s.go u i).binge j) :
    (s.go u i).tail j ≤ s.march u i+s.rim u i+s.thunder u i := by
   let a:= (∑ k∈Ico j s.L,(32:ℝ)^(s.L-k)*s.mh k u i)
   let b:= (∑ k∈Ico j s.L,(32:ℝ)^(s.L-k)*s.nh k u i)
   have hz : (s.go u i).tail j≤a+b := by
      unfold Run.tail a b; rw [← sum_add_distrib]; apply sum_le_sum
      intro k hk; rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (s.pointed h (mem_Ico.1 hk).2 hs) (by positivity)
   have hb : b≤ s.thunder u i := by
      apply sum_le_sum_of_subset_of_nonneg (fun k hi=>mem_range.2 (mem_Ico.1 hi).2)
                (fun k hk _=>mul_nonneg (by positivity) (s.nnn ..))
   apply hz.trans (add_le_add _ hb)
   obtain hl|hl:=hh
   · have hs0 : s.L-1=j := by omega
     have he : a=s.rim u i := by
       dsimp only [a,rim]
       rw [hl]
       simp
     rw [he]; linarith [s.march_nn u i]
   have ha : a=s.trail j u i := by simp [a,trail,chipV,(s.wrapped j u i).1 hl]
   have he : s.trail j u i ≤ s.march u i := by
      unfold march; exact single_le_sum (f:=fun k=> s.trail k u i) (fun k _=>s.trail_nn k u i) (mem_range.mpr hi)
   rw [ha]; linarith [s.rim_nn u i]

def diff (f : Trio) : TableF n w :=
    fun u i k=> let r:=s.go u i
                fourth ((r.mid s.L).val r.S r.K f k)-fourth (r.origin.val r.S r.K f k)

lemma receipt {theta C f p M} (h:s.Works p M) (hf:TS theta C f) (hz:delta≤theta)
    (hc:theta≤1) {u i k} (hi:i∈s.src0 u) (hk:k∈s.dst0 u) :
       |s.diff f u i k| ≤ Run.charge C*s.sumB u i := by
   let r:=s.go u i
   obtain ⟨j,hj,hl,hp⟩:=r.earliest h.len
   have hC := hf.start.one
   have h1 : 0<C^3 := pow_pos (by linarith) _
   have he1 : 1 ≤ Run.wideK (C+12) := by unfold Run.wideK; linarith
   have hu : C^3 ≤ Run.charge C := by unfold Run.charge; nlinarith
   by_cases he : r.L=j+1 ∨ r.binge j
   · have hT := s.tail_route h hi hj he
     have hD := s.cloud_plan h hi hj
     apply (r.wave (s.ok h hi) hf hz hc hj hl hk).trans (mul_le_mul_of_nonneg_left _ (by linarith))
     unfold sumB r; linarith [s.beasts_nn u i]
   obtain hl1 : r.overflow j:=hp.resolve_left (fun e=> he (Or.inl e))
   have hb : s.phantom j u i=1 := ite_eq_left ⟨⟨hl,hl1⟩,fun e=>he (Or.inr e)⟩
   have hp : 1≤ s.beasts u i := by
      unfold beasts
      exact le_trans (le_of_eq hb.symm) (single_le_sum (f:=fun k=>s.phantom k u i)
                        (fun k _=>s.false_nn k u i) (mem_range.2 hj))
   have hs : 1 ≤ s.sumB u i := by unfold sumB; linarith [s.clouds_nn u i,s.march_nn u i,s.rim_nn u i,s.thunder_nn u i]
   have hC0 (v : Blob) : 0≤fourth (v.val r.S r.K f k) ∧ fourth (v.val r.S r.K f k)≤C^3 :=
      ⟨fourth_nn _,hf.rootub ..⟩
   change |fourth ((r.mid s.L).val r.S r.K f k)-fourth (r.origin.val r.S r.K f k)| ≤ _
   obtain ⟨ha,hb⟩:=hC0 (r.mid s.L)
   obtain ⟨he,hk2⟩:=hC0 r.origin
   refine le_trans (b:=C^3) ?_ ?_
   · rw [abs_le]; constructor <;> linarith
   nlinarith

end Spray
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 2048
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset
open scoped Classical

namespace Spray
variable {n w : ℕ} [Fact n.Prime]
variable (s : Spray n w)

abbrev droplets := (24/At.small)*3
lemma vgeo {c : ℝ} (he:0≤c) {f : ℕ→ Vertex n w}
    (h : ∀ i<s.L,s.d.von (f i) ≤ c*dry (gapD s.L i)) :
    s.d.von (fun u i=>∑ j∈range s.L,f j u i) ≤ c*2 := by
   apply le_trans (s.d.vseries f (range s.L))
   have hd := sum_le_sum (s:=range s.L) fun i hi=> h i (mem_range.1 hi)
   apply hd.trans
   rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (binsum s.L) he

lemma droplets_ub {p M} (h:s.Works p M) :
    s.d.von s.clouds ≤ droplets*p*2 := by
   let a:=24/small
   have hp:=h.pos; have ha : 0≤a:=div_nonneg (by norm_num) smallp.le
   apply s.vgeo (by change 0≤a*3*p; positivity) (f:=s.sky)
   intro j hi
   let r:=floorR s.b s.L j
   have hr : 0≤ r:= (floor_pos ..).le
   change s.d.von (fun u i=>a*r*s.both j u i) ≤ _
   rw [s.d.vscale,abs_of_nonneg (by positivity)]
   have he:=floor_lift s.b s.L j
   have ht:=mul_le_mul_of_nonneg_left (s.both_ub h hi) (show 0 ≤ a*r by positivity)
   refine ht.trans ?_
   change a*r*_ ≤ a*3*p*_
   change r*_ ≤ _ at he
   have hd:=mul_le_mul_of_nonneg_left he (show 0≤ a*3*p by positivity)
   linarith

lemma beasts_ub {p M} (h:s.Works p M) :
    s.d.von s.beasts ≤ 64*p*2 := by
   have hp:=h.pos
   apply s.vgeo (by positivity) (f:=s.phantom)
   intro j hi
   apply (s.false_ub h hi).trans
   have hh:= mul_le_mul_of_nonneg_left (firm_plain s.b s.K s.L j) (show 0≤64*p by positivity)
   unfold fc; linarith

lemma thunder_ub {p M} (h:s.Works p M) :
    s.d.von s.thunder ≤ p*2 := by
   apply s.vgeo h.pos (f:=fun j u i=>(32:ℝ)^(s.L-j)*s.nh j u i)
   intro j hi
   rw [s.d.vscale,abs_of_nonneg (by positivity)]
   calc _ ≤ _ := mul_le_mul_of_nonneg_left (s.nh_ub h hi) (by positivity)
        _ ≤ _ := by linarith [mul_le_mul_of_nonneg_left (cyclone hi) h.pos]

lemma rim_ub {p M} (h:s.Works p M) :
    s.d.von s.rim ≤32*2*p*box s.b := by
   have hl : s.L-1<s.L := by have := h.len; omega
   unfold rim; rw [s.d.vscale]; norm_num
   have ht := s.mh_ub h hl
   have he : liftB s.b s.L (s.L-1)=box s.b := by unfold liftB; rw [gap_end,mul_one]
   rw [he] at ht; linarith

lemma march_ub {p M} (h:s.Works p M) :
    s.d.von s.march ≤ hefty M*2*p*2 := by
   have hp:=h.pos; have hM : 0 ≤ hefty M := by unfold hefty; linarith [h.mass]
   apply s.vgeo (by positivity) (f:=s.trail)
   intro i hi
   unfold trail
   apply le_trans (s.d.vseries (fun k u j=>(32:ℝ)^(s.L-k)*s.chipV i (s.mh k) u j) (Ico i s.L))
   let W (k : ℕ) := (32:ℝ)^(s.L-k)
   have hh (k) (hk:k∈Ico i s.L) :
     s.d.von (fun u j=>W k*s.chipV i (s.mh k) u j) ≤
        (hefty M*2*p)*(s.fc i)*(W k*liftB s.b s.L k) := by
      have h0 : 0≤W k := by unfold W; positivity
      rw [s.d.vscale,abs_of_nonneg h0]
      apply le_trans (mul_le_mul_of_nonneg_left (s.masked_ub h i k (mem_Ico.1 hk).2) h0)
      exact le_of_eq (by ring)
   apply (sum_le_sum hh).trans
   rw [← mul_sum, mul_assoc]
   exact mul_le_mul_of_nonneg_left (firm_tail s.b s.K s.L i hi) (by positivity)

def Bprice (b : ℕ) (M : ℝ) :=
    droplets*2+hefty M*2*2+32*2*box b+2+64*2
lemma bprice_pos {M : ℝ} (h:1≤M) (b) : 0 < Bprice b M := by
   have hs:=smallp; have hb:=box0 b
   unfold Bprice droplets hefty
   have :0<M := by linarith
   positivity
lemma subtotal {p M} (h:s.Works p M) :
    s.d.von s.sumB ≤ Bprice s.b M*p := by
   let c : Vertex n w :=fun u i=> s.clouds u i+s.march u i
   let a : Vertex n w :=fun u i=> c u i+s.rim u i
   let b : Vertex n w :=fun u i=> a u i+s.thunder u i
   apply le_trans (s.d.vplus b s.beasts)
   have h1 : s.d.von b ≤ s.d.von a+s.d.von s.thunder:= s.d.vplus a s.thunder
   have h2 : s.d.von a ≤ s.d.von c+s.d.von s.rim:=s.d.vplus c s.rim
   have h3 : s.d.von c ≤ s.d.von s.clouds+s.d.von s.march:=s.d.vplus s.clouds s.march
   have h4:=s.thunder_ub h; have h5:=s.march_ub h; have h6:=s.droplets_ub h
   have h7:=s.rim_ub h; have h8:=s.beasts_ub h
   unfold Bprice; linarith

lemma charge_pos (C : ℝ) (h:1≤C) : 0≤Run.charge C := by
   unfold Run.charge Run.wideK
   have :0≤C:=by linarith
   positivity
def localP (K b : ℕ) (C M : ℝ) :=
   (1+2*K:ℝ)*Run.charge C*Bprice b M

set_option maxHeartbeats 500000 in
/-- Integrated buffered row estimate. -/
theorem compress {p M theta C f} (h:s.Works p M) (hf:TS theta C f)
    (hz:delta≤theta) (hc:theta≤1) :
    s.d.ton (s.diff f) ≤localP s.K s.b C M*p := by
   let g:= s.diff f
   let c:=Run.charge C
   let u:Vertex n w:=fun s' i=> (1+2*s.K:ℝ)*c*s.sumB s' i
   have hcp : 0≤c := charge_pos C hf.start.one
   have hd (u i k : ℝ) (hi:0≤k) : u≤ i → k*u≤k*i := fun e => mul_le_mul_of_nonneg_left e hi
   have hv := s.sumB_nn
   have hh (w' i) (hi:i∈s.src0 w') :
       ∑ j∈s.dst0 w',g w' i j^4≤u w' i^4 := by
      let b:= c*s.sumB w' i
      let r:=s.go w' i
      let F (v : Blob) := r.S.filter fun j=>v.val r.S r.K f j≠0
      let t:=(F (r.mid r.L) ∪ F r.origin)
      have hs: t⊆s.dst0 w':= union_subset (filter_subset ..) (filter_subset ..)
      have he : ∑ j∈s.dst0 w',g w' i j^4=∑ j∈t,g w' i j^4 := by
         symm; apply sum_subset hs
         intro j hj hz
         have h1 : j ∈ r.S :=hj
         have ha : (r.mid r.L).val r.S r.K f j=0 := by
            by_contra e; exact hz (mem_union_left _ (mem_filter.mpr ⟨h1,e⟩))
         have hb : r.origin.val r.S r.K f j=0 := by
            by_contra e; exact hz (mem_union_right _ (mem_filter.mpr ⟨h1,e⟩))
         change (fourth ((r.mid r.L).val r.S r.K f j)-fourth (r.origin.val r.S r.K f j))^4=0
         rw [ha,hb]; norm_num
      have hk (v) : (F v).card≤ s.K:=Blob.support_size hf (lt_of_lt_of_le dp hz) _ _ _
      have hcard : t.card≤2*s.K :=
         le_trans (card_union_le ..) (by linarith [hk (r.mid r.L),hk r.origin])
      have hc1 : (t.card:ℝ)≤2*(s.K:ℝ) := by exact_mod_cast hcard
      have hc2 : (t.card:ℝ) ≤ (1+2*s.K:ℝ)^4 := by
         let v:ℝ:=2*s.K
         change (t.card:ℝ) ≤ (1+v)^4
         change (t.card:ℝ)≤v at hc1
         have hz : 0≤v:=by dsimp only [v]; positivity
         nlinarith [sq_nonneg v]
      calc _ = _:=he
           _ ≤ ∑ j∈t,b^4 :=
               sum_le_sum fun j hj=> by rw [← Meter.abs4];
                                        exact pow_le_pow_left₀ (abs_nonneg _) (s.receipt h hf hz hc hi (hs hj)) _
           _ = (t.card:ℝ)*b^4 := by simp
           _ ≤ (1+2*s.K:ℝ)^4*b^4 := mul_le_mul_of_nonneg_right hc2 (by positivity)
           _ = _ := by unfold b u; ring
   have hg : s.d.ton g ≤ s.d.von u :=
      (s.d.tm_le (s.d.vn0 _)).2 (by rw [s.d.von_four]; exact s.d.vi_mono hh)
   apply hg.trans
   unfold u; rw [s.d.vscale,abs_of_nonneg (by positivity)]
   have hl:= hd _ _ ((1+2*s.K:ℝ)*Run.charge C) (by change 0≤(1+2*s.K:ℝ)*c; positivity)
                         (s.subtotal h)
   unfold localP c; linarith

end Spray
end
end ExactDerandomization.Est

end

section

set_option synthInstance.maxSize 4096
namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset

namespace Flame
variable {n : ℕ} [Fact n.Prime]

def spill (s : Stair) (d : Axis) (a : ℕ) (K : ℕ) (v w : Flame n) : Spray n 0 :=
   let p:=d.narrowed a
   let tint (i : ℕ) := fun (q:Pool n) x y=> |w.smoke s p (i+1) q x y|
   let fog:=fun i q x y=> |v.smoke s d (i+1) q x y| + d.wmask a (tint i) q x y
   { d:=d,t:=a,L:=s.L,K:=K,b:=2
     a:=v.lamp,q:=w.lamp
     inc:=fun i q x y=>(v.bundle s d i q x y,w.bundle s p i q x y)
     lead:=v.picture s d true,seedB:=w.picture s p false,fog:=fog }

lemma exact1 (s d a K) (v w : Flame n) (i q x y)
   (hx:x∈src d.S d.u q) (hy:y∈dst d.S d.a q) :
   (((spill s d a K v w).go q x).pile i y).1=v.prefixR s d i q x y := by
   induction i with
   | zero=>rw [v.prefix0]; rfl
   | succ i ih=>
     rw [← v.next s d]; rw [Run.pile]; rw [Pi.add_apply,Prod.fst_add,ih]
     congr 1
     change v.bundle _ _ _ _ _ _=_
     unfold bundle; rw [ite_eq_left ⟨hx,hy⟩]

lemma exact2 (s d a K) (v w : Flame n) (i q x y) (hx:x∈src d.S d.u q) :
   (((spill s d a K v w).go q x).pile i y).2=
               d.wmask a (w.prefixR s (d.narrowed a) i) q x y := by
   induction i with
   | zero=> rw [Axis.wmask, w.prefix0]; split <;> rfl
   | succ i ih=>
     rw [Run.pile,Pi.add_apply,Prod.snd_add,ih]
     change _+w.bundle s (d.narrowed a) i q x y=_
     unfold bundle Axis.wmask
     by_cases h:y∈dst d.S a q
     · simp only [Axis.narrowed,hx,h,and_self,ite_true]
       exact w.next s (d.narrowed a) i q x y
     · simp [h]

lemma outputcard (p q : ℝ) : min 1 (max p q) = max (min 1 p) (min 1 q) := by grind

set_option maxHeartbeats 500000 in
lemma earliestCost {s d a K c} {v w : Flame n} (h1:Owes s d true c v) (h2:Owes s (d.narrowed a) false c w)
    (j) (q x y) (hx:x∈src d.S d.u q) (hy:y∈dst d.S d.a q) :
        ((spill s d a K v w).go q x).epi j y≤(spill s d a K v w).pay j q x y := by
   have hi : x∈d.S := (mem_filter.mp hx).1
   have hh : y∈d.S := (mem_filter.mp hy).1
   let r:=d.narrowed a
   let C (f:Flame n) (d : Axis) := f.prefixR s d (j+1) q x y-f.lamp x y
   have e1:v.picture s d true j x y+|v.smoke s d (j+1) q x y|≥ rel (C v d) (v.lamp x y) :=
         v.tip_noise h1 j q hi hh
   have e2:w.picture s r false j x y+|w.smoke s r (j+1) q x y|≥ |C w r| :=
         w.tip_noise h2 j q hi hh
   have he : 0≤ rel (C v d) (v.lamp x y) := rel_nn (h1.positive x hi y hh)
   simp only [Run.epi,outputcard,exact1 s d a K v w _ q x y hx hy,exact2 s d a K v w _ q x y hx]
   simp only [Spray.pay,Spray.s1,Spray.s2,spill,Spray.go,Spray.dst1,Axis.wmask]
   by_cases hz:y∈dst d.S a q
   · simp only [hz,ite_true]; unfold C r at *; unfold rel at *
     grind
   · simp only [hz,ite_false,sub_self,abs_zero]
     unfold C r at *; unfold rel at *; grind

lemma ready {s : Stair} {d K a c M} {v w : Flame n}
   (hv : Owes s d true c v) (hw : Owes s (d.narrowed a) false c w)
   (hm:1≤M) (hl : legal n d.S) (hq : d.a≤a) (hz:2^d.a≤n)
   (hs : ∀ i∈d.S,∀ j∈d.S, |w.lamp i j|≤zeta ∧ (v.lamp i j ≤ At.small → w.lamp i j=0))
   (ht : ∀ i∈d.S,(∑ j∈d.S,v.lamp i j)*rate d.a≤ M) :
     (spill s d a K v w).Works (2*contract s c) M := by
   let z:=contract s c
   have hh : 0≤ z:=protocol
   have he (j) : z*liftB 2 s.L j≤2*contract s c*liftB 2 s.L j := by
       apply mul_le_mul_of_nonneg_right (show z≤2*z by linarith) (le_trans zero_le_one (lift_one ..))
   refine ⟨show 0≤2*z by positivity,hm,s.length_pos,hl,hq,hz,
      fun i hi j hj=> ⟨hv.positive i hi j hj,hs i hi j hj⟩,ht,
      fun i _ u j hj k hk=> earliestCost hv hw i _ _ _ hj hk,?_,?_,?_⟩
   · intro j _
     exact le_trans (v.pink hv j) (he j)
   · intro j _
     change d.ton (d.wmask a _)≤_
     rw [d.tmask _ hq]
     exact le_trans (w.pink hw j) (he j)
   · intro j _
     let f:Pics n:=fun u x y=> |v.smoke s d (j+1) u x y|
     let g:Pics n:=fun u x y=> |w.smoke s (d.narrowed a) (j+1) u x y|
     apply le_trans (d.tplus f (d.wmask a g))
     unfold f g; rw [d.ton_subnorm,d.tmask a hq, Axis.ton_subnorm]
     change _≤ _*decay s.L j
     linarith [v.fumes hv j,w.fumes hw j]

end Flame
end
end ExactDerandomization.Est

end

section

namespace ExactDerandomization.Est
noncomputable section
open Analysis Hie At Buf Finset
set_option synthInstance.maxSize 4096

variable {n : ℕ} [Fact n.Prime]
/-- Use only diagonal of a picture as one vertex. Y conditioned
nominally at rate 1, also pin at the diagonal for the mix. -/
def ridge (f : Vec) : Mat := fun x y=> if x=y then f x else 0
def core (f : Paint n) : Pics n := fun s=>ridge (f s)
def diagP (f : Pics n) : Paint n := fun s x=> f s x x

namespace Axis
variable (d : Axis)
lemma diagh {f : Paint n} (x y : ℕ) :
    (d.narrowed 0).fm (core f) x y=ridge (d.vm f) x y := by
   have he (p : ℕ) :
      pct n d.u * (pct n 0) * Env.cond d.u 0 (x:ZMod n) (p:ZMod n) (w:=0)
                       (fun s=>f s x) =
          av (fun s:Pool n=> if hit d.u (x:ZMod n) s.1 then f s x else 0) := by
       rw [← Env.two_cond]; simp only [Env.mask,allhit,and_true]
   by_cases ht:x=y
   · simp only [fm,core,vm,ridge,ht,ite_true]
     subst y
     apply mul_left_cancel₀ (mul_pos (pct_pos (NeZero.pos n) d.u) (pct_pos (NeZero.pos n) 0)).ne'
     simpa only [Nat.cast_zero] using Eq.trans (he x) (he 0).symm
   · simp only [fm,core,ridge,ht,ite_false]
     unfold Env.cond; rw [av_zero]

lemma diagonal (f : Paint n) :
    (d.narrowed 0).ton (core f)=d.von f := by
   conv_lhs=> rw [← four_fourth ((d.narrowed 0).tn0 _),ton_four]
   conv_rhs=> rw [← four_fourth (d.vn0 _),von_four]
   congr 1; rw [ti_apply,vi_apply]; dsimp only [narrowed]
   congr 1
   apply congrArg av; ext s
   apply sum_congr rfl; intro i hi
   have hg:i∈dst d.S 0 s:=mem_filter.2 ⟨(mem_filter.1 hi).1,allhit ..⟩
   rw [sum_eq_single i]
   · simp [core,ridge]
   · intro j hj ht
     simp only [core,ridge,Ne.symm ht,↓reduceIte]; norm_num
   simp [hg]

lemma vproject (f : Pics n) :
    d.von (diagP f) ≤ (d.narrowed 0).ton f := by
   apply (d.vm_le ((d.narrowed 0).tn0 f)).2
   rw [ton_four]; apply d.vi_mono
   intro s x hx
   have ht : x∈dst d.S 0 s:= mem_filter.2 ⟨(mem_filter.1 hx).1,allhit ..⟩
   exact single_le_sum (f:=fun j=> f s x j^4) (fun _ _=>by positivity) ht

def color (s:Stair) (v:Flame n) : Paint n :=
    fun u i => if i∈src d.S d.u u then smooth (v.prefixR s (d.narrowed 0) s.L u i i) else 0
lemma boundsC (s v u i) : in01 (d.color (n:=n) s v u i) := by
    unfold color; split; exact unit_mem _
    unfold in01; norm_num

/- the group 1 slack answer of a vector flame. -/
lemma drawn {s : Stair} {v:Flame n} {c : ℝ} (h : v.Owes s (d.narrowed 0) false c)
    {f : Vec} (hf:∀ x∈d.S,in01 (f x)) (he:∀ x∈d.S,v.lamp x x=f x) :
    d.von (fun u i=>d.color s v u i-f i) ≤ 6*Flame.contract s c := by
   let b := d.narrowed 0
   let i:=s.L-1
   have hs : i+1=s.L := by have :=s.length_pos; dsimp only [i]; omega
   let P : Pics n := fun _=> v.picture s b false i
   let q:=v.smoke s b (i+1)
   let t : Pics n := fun u x y=> P u x y+|q u x y|
   have hp : d.von (fun u i=>d.color s v u i-f i)≤d.von (diagP t) := by
     apply d.vorder
     intro u x hx
     have he1 := (mem_filter.1 hx).1
     have hu:=v.tip_noise h i u he1 he1; change |_ - v.lamp x x|≤ t u x x at hu
     change |d.color s v u x-f x|≤ t u x x
     have hh := hf x he1
     have hv : smooth (f x)=f x := by
        unfold smooth in01 at *; grind
     unfold color; rw [ite_eq_left hx]
     refine le_trans (b:=|v.prefixR s b (i+1) u x x - f x|) ?_ ?_
     · rw [hs]
       conv_lhs=> rhs; rw [← hv]
       have hg := unit_ic.lip (f x) (v.prefixR s b s.L u x x)
       rwa [one_mul] at hg
     simpa only [he x he1] using hu
   apply (hp.trans (d.vproject _)).trans
   apply (b.tplus P (fun u x y=> |q u x y|)).trans
   rw [b.ton_subnorm]
   have ht:=v.pink h i; have hz:=v.fumes h i
   let k:=Flame.contract s c
   change b.ton P ≤ k* liftB _ _ _ at ht
   change b.ton q≤ k*_ at hz
   have hl : liftB 2 s.L i=4 := by unfold liftB i; rw [gap_end]; norm_num [box]
   have hh : decay s.L i≤1:=dry_one _
   rw [hl] at ht
   have hkp :0≤k:=Flame.protocol
   change _≤6*k
   nlinarith

end Axis
end
end ExactDerandomization.Est

end

end OAI
