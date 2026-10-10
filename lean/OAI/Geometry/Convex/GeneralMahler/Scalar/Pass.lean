import OAI.Geometry.Convex.GeneralMahler.Scalar.Grid

namespace OAI
/-! Range assertions and combined first derivative assertion for §07.
Integers in tables denote exact multiples 1/10000. -/
open Set Filter Real
namespace GeneralMahler.SCal
open Profile Layers Jet Tag Cert Cert.IV

namespace Grid
-- exact scale
def bandD : Int:=den / 10000
def bd (n:Int):IV:= box (n*bandD) (n*bandD)
def band (l u:Int) : IV:= box (l*bandD) (u*bandD)
lemma w_bd (a:Int): w (a*bandD) = (a:ℝ)/10000 := by unfold w; norm_num [bandD,den]; ring
lemma mem_band (x:ℝ) (l u:Int): x∈band l u ↔ (l:ℝ)/10000 ≤ x ∧ x ≤ (u:ℝ)/10000 := by
  change (w _ ≤ _ ∧ _ ≤w _)↔_
  rw [w_bd,w_bd]
lemma mbd (a:Int): (a:ℝ)/10000∈ bd a:= by apply (mem_band _ a a).mpr; simp

def rng : Tag→IV
  | R => band 530 1680
  | K => band (-70) 275
  | C => band (-5010) (-3410)
  | Q => band 775 2559
  | dK => band (-660) 660
  | dC => band (-2470) 2470
  | dQ => band (-1930) 1930
  | ddK=>band (-2600) 2600
  | ddC=>band (-9500) 9500
  | ddQ=>band (-5600) 5600
  | NK=>band (-3000) 3000
  | NC=>band (-9500) 9500
  | NQ=>band (-5600) 5600
  | RV=>band (-3190) 3190
  | V =>band 7250 10600
  | S =>band 1130 5140
def roff : Tag→IV
  | K=>band (-1) 191
  | C=>band (-5010) (-4950)
  | Q=>band 2350 2559
  | dK=>band (-211) 211
  | dC=>band (-84) 84
  | NK=>band 0 3000
  | _=>unk

structure Panel where
  lo:Nat -- beginning t-index, inclusive
  hi:Nat
  qR:IV
  sr:IV
  vR:IV
  rh:Int -- rho max tick
def pan (a b:Nat) (l u v w x y z:Int):Panel:=
  ⟨a,b, band (10*l) (10*u),band (10*v) (10*w),band (10*x) (10*y),10*z⟩
def panel : Nat→Panel
  | 0=> pan 0 20 77 81 113 132 725 743 804
  | 1=> pan 20 40 80 88 125 166 740 785 814
  | 2=> pan 40 60 87 100 159 220 782 848 831
  | 3=> pan 60 80 99 116 213 288 845 920 853
  | 4=> pan 80 100 115 134 281 359 917 986 877
  | 5=> pan 100 140 133 171 352 464 983 1055 927
  | 6=> pan 140 200 170 211 457 504 1041 1059 992
  | 7=> pan 200 340 210 245 497 513 1009 1044 1072
  | _=> pan 340 720 244 256 506 514 999 1012 1104
def stage (n:Nat):Nat:=
  if n<20 then 0 else if n<40 then 1 else if n<60 then 2 else if n<80 then 3
  else if n<100 then 4 else if n<140 then 5 else if n<200 then 6 else if n<340 then 7 else 8

def checkSR (b:Tag→IV) (k:Panel):Bool :=
  SubB (b Q) k.qR && SubB (b S) k.sr && SubB (b V) k.vR
def SIn (b:Tag→ℝ) (k:Panel):Prop:=
  b Q∈k.qR∧b S∈k.sr∧b V∈k.vR
lemma SIn_check {b:Tag→IV} {a:Tag→ℝ} (ha:∀ i,a i∈b i) {k:Panel} (hh:checkSR b k=true): SIn a k := by
  simp only [checkSR,Bool.and_eq_true] at hh
  exact ⟨subB (ha Q) hh.1.1,subB (ha S) hh.1.2,subB (ha V) hh.2⟩

noncomputable def Ucost (f:Tag→ℝ):ℝ:=
  (1507/1000)*max 0 (-(f NK))+
    ((12*(8/10))/mstar^2)*
      (125/100*(f dK+tc*f dC)^2+5*Profile.tr^2*f dC^2)
def Ubox (b:Tag→IV):IV:=
  bd 15070*Zmax 0 (-(b NK))+(bd 96000 /sq (bd 3520))*
    (bd 12500 * sq (b dK+bd 210*b dC)+ (IV.c 5)*sq (bd 430)*sq (b dC))
noncomputable def Ur:=54/100*r^2*omegaP^2
def UrB:IV:=bd 5400*sq (bd 2200)*sq (bd 46000)
noncomputable def Cor (k c:ℝ) (r:ℝ):=lam*r^2+r*c+k
noncomputable def Ta (k c:ℝ):=2*ell0*c-ell0^2-4*lam*k
def CorB (k c r:IV):IV:=bd 6500*sq r+r*c+k
def TaB (k c:IV):IV:=bd (-7400)*c-sq (bd 3700)-bd 26000*k
lemma mUcost (b:Tag→IV) (f:Tag→ℝ) (he:∀ i,f i∈b i): Ucost f∈ Ubox b := by
  have h1:= mmul (mbd 15070) (mmax mz (mneg (he NK)))
  have h2:=mdiv (mbd 96000) (msq (mbd 3520))
  have h3:= mmul (mbd 12500) (msq (madd (he dK) (mmul (mbd 210) (he dC))))
  have h4:= mmul (mmul (mc 5) (msq (mbd 430))) (msq (he dC))
  have hi:=madd h1 (mmul h2 (madd h3 h4))
  unfold Ucost
  convert hi using 1
  all_goals first|rfl| (unfold mstar tc Profile.tr; norm_num)
lemma mUr: Ur∈UrB := by
  have hi:= mmul (mmul (mbd 5400) (msq (mbd 2200))) (msq (mbd 46000))
  unfold Ur
  convert hi using 1
  all_goals first|rfl| (unfold r omegaP; norm_num)
lemma mCor {x y z:ℝ} {a b c:IV} (hx:x∈a) (hy:y∈b) (hz:z∈c): Cor x y z∈ CorB a b c := by
  have hi:= madd (madd (mmul (mbd 6500) (msq hz)) (mmul hz hy)) hx
  unfold Cor
  convert hi using 1
  all_goals first|rfl| (unfold lam; norm_num)
lemma mTa {x y:ℝ}{a b:IV} (hx:x∈a) (hy:y∈b): Ta x y∈ TaB a b := by
  have hi:=msub (msub (mmul (mbd (-7400)) hy) (msq (mbd 3700))) (mmul (mbd 26000) hx)
  unfold Ta
  convert hi using 1
  all_goals first|rfl| (unfold ell0 lam; norm_num)
def Corr (f:Tag→ℝ): Prop:=
  0<Cor (f K) (f C) tmin ∧
    Cor (f K) (f C) tmax<0 ∧ mstar^2<Ta (f K) (f C) ∧ Ucost f≤ Ur
def joint (b:Tag→IV):Bool :=
  Less 0 (CorB (b K) (b C) (bd (-220))) &&
    Less (CorB (b K) (b C) (bd 640)) 0 &&
    Less (sq (bd 3520)) (TaB (b K) (b C)) &&
    LeB (Ubox b) UrB
lemma c_check {a:Tag→ℝ} {b:Tag→IV} (h:∀ i,a i∈b i) (he:joint b=true): Corr a := by
  simp only [joint,Bool.and_eq_true] at he
  have hi : tmin ∈ bd (-220) := by convert mbd (-220); norm_num [tmin]
  have hp : tmax ∈ bd 640 := by convert mbd 640; norm_num [tmax]
  have hh : mstar∈ bd 3520 := by convert mbd 3520; norm_num [mstar]
  exact ⟨mlt mz (mCor (h K) (h C) hi) he.1.1.1, mlt (mCor (h K) (h C) hp) mz he.1.1.2,
    mlt (msq hh) (mTa (h K) (h C)) he.1.2, mle (mUcost b a h) mUr he.2⟩

def allT := [R,K,C,Q,dK,dC,dQ,ddK,ddC,ddQ,NK,NC,NQ,RV,V,S]
lemma allT_mem (a:Tag):a∈allT := by cases a <;> decide
def checkIn (b w:Tag→IV):Bool:= allT.all (fun i=>SubB (b i) (w i))
lemma hasSub {a b:Tag→IV} (h:checkIn a b=true) (i:Tag): SubB (a i) (b i)=true :=
  List.all_eq_true.mp h i (allT_mem i)

def x5:=band 2203 2559
def pass0 (n:ℕ) (b:Tag→IV):Bool :=
  checkIn b rng && joint b &&
    (if n ≥ 280 then checkIn b roff else true) &&
    checkSR b (panel (stage n)) &&
    (if n ≥ 225 then SubB (b Q) x5 else true)

def pass (n:ℕ):Bool:=pass0 n (tot n)

structure passR (n:ℕ) (a:Tag→ℝ):Prop where
  gr:∀ i,a i∈rng i
  uu:Corr a
  off:280≤n → ∀ i,a i∈ roff i
  pn:SIn a (panel (stage n))
  five:225≤n → a Q∈x5

lemma passes {n:ℕ} {b:Tag→IV} {a:Tag→ℝ} (ha:∀ i,a i∈b i) (he:pass0 n b=true):
    passR n a := by
  simp only [pass0,Bool.and_eq_true] at he
  refine
    ⟨fun i=> subB (ha i) (hasSub he.1.1.1.1 i), c_check ha he.1.1.1.2,
      fun hi i=>subB (ha i) (hasSub ?_ i), SIn_check ha he.1.2,
      fun hi=>subB (ha Q) ?_⟩
  · have h:=he.1.1.2
    simpa only [ite_eq_left hi] using h
  have h:=he.2; simpa only [ite_eq_left hi] using h
lemma cell_R {n} (hp:pass n) {x:ℝ} (hx:x∈Icc (nd n) (nd (n+1))) :
    (Tag.R.act x) ∈ rng R := by
  have he := htot n R CJet.Ir x hx
  have hv : R.Fld x 0=R.act x:= CJet.rje x
  rw [hv] at he
  simp only [pass,pass0,Bool.and_eq_true] at hp
  apply subB he (hasSub hp.1.1.1.1 R)
lemma cell_pass {n} (hp:pass n) (h:CJet.RadH) (hQ:TestF qu) {x:ℝ} (hx:x∈Icc (nd n) (nd (n+1))) :
    passR n (fun t=>t.act x) := by
  apply passes _ hp
  intro i; rw [← i.field_val h hQ]
  apply htot n i (tower i h) x hx
end Grid
end GeneralMahler.SCal

end OAI
