import OAI.Geometry.Convex.GeneralMahler.Scalar.Circle

namespace OAI
/-! §07 layer rectangles. Evaluate only 4 vertices in H and V2. -/
open Set Filter Real
namespace GeneralMahler.SCal.PA
open Tag Grid Jet Profile Cert Cert.IV
def endp (k:Bool):IV→Int
  | unk=>0
  | box a b=> if k then b else a
noncomputable def eR (k:Bool)(A:IV):ℝ := IV.w (endp k A)
def eB (k:Bool)(A:IV):IV:=box (endp k A) (endp k A)
lemma ek (k:Bool)(A:IV): eR k A∈eB k A:= ⟨le_rfl,le_rfl⟩
lemma orderE {x:ℝ}{A:IV}(h:x∈A) (he:A≠ unk) :
    eR false A ≤ x ∧ x≤ eR true A := by cases A; contradiction; exact h

noncomputable def Ldef (x v:ℝ):=
  let j:= x+v-2*kar
  x+tc*j-(Profile.tr/(2*h₀)+1/alpha)* j^2
noncomputable def Lcost (x y:ℝ):=
  2*(bb+eta+(bb+eta-kar)*tmin)+ 2*bm*x*y +2*e₀*(2*Profile.tr)^2+Profile.tr*h₀/2
noncomputable def HV (q s:ℝ):= 4*cc+4*kk*q+2*(kk-q)*s
def defB (x v:IV):=
  let j:=x+v-2*bd 11600
  x+bd 210*j-(bd 430/(2*bd 5000)+(1:IV)/bd 22600)*sq j
def bmb:IV:=
  ((1:IV)+bd 640)*(bd 6020-3*bd 220)/
    (3*(3*(bd 6020+bd 220)-4*bd 3650))
-- The fixed term in the layer inequality.
noncomputable def fixedCost := 2*(bb+eta+(bb+eta-kar)*tmin)+ 2*e₀*(2*Profile.tr)^2+Profile.tr*h₀/2
-- Rational interval enclosures for the layer constants.
lemma mnums :
    Profile.tc∈bd 210∧ kar∈bd 11600 ∧ Profile.tr∈bd 430 ∧ h₀ ∈ bd 5000 ∧
      alpha∈ bd 22600 ∧ tmin∈bd (-220) ∧ eta∈bd 220 ∧ e₀∈bd 2560 := by
  have h:=mbd
  unfold Profile.tc Profile.tr kar h₀ alpha tmin eta e₀
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals change w _ ≤ _ ∧ _ ≤ w _; norm_num [w,bandD,den]
lemma mDef {x v:ℝ} {A B:IV}(h:x∈A) (hv:v∈B): Ldef x v ∈ defB A B := by
  obtain ⟨hc,hk,ht,hh,hb,_⟩:=mnums
  have hj:= msub (madd h hv) (mmul mtwo hk)
  exact msub (madd h (mmul hc hj)) (mmul (madd (mdiv ht (mmul mtwo hh)) (mdiv mo hb)) (msq hj))

lemma mBBc : bb∈bd 6020∧cc∈bd 3650∧ tmax∈bd 640 := by
  unfold bb cc tmax
  refine ⟨?_,?_,?_⟩
  all_goals change w _ ≤ _ ∧ _ ≤ w _; norm_num [w,bandD,den]
lemma mthree:(3:ℝ)∈(3:IV):= mc 3
lemma mfour:(4:ℝ)∈(4:IV):= mc 4
lemma mbMc : bm∈bmb := by
  obtain ⟨hb,hc,ht⟩:=mBBc
  obtain ⟨_,_,_,_,_,_,he,_⟩:=mnums
  exact mdiv (mmul (madd mo ht) (msub hb (mmul mthree he))) (mmul mthree
    (msub (mmul mthree (madd hb he)) (mmul mfour hc)))
def costB (s t:IV):=
  2*(bd 6020 +bd 220+(bd 6020+bd 220-bd 11600)*bd (-220))+
    2*bmb*s*t+2*bd 2560*sq (2*bd 430) + bd 430*bd 5000/2
lemma mCost {x v:ℝ} {A B:IV}(h:x∈A) (he:v∈B): Lcost x v ∈ costB A B := by
  obtain ⟨_,hk,hr,hj,_,ht,ha,hb⟩:=mnums
  have hi:= madd mBBc.1 ha
  exact madd (madd (madd (mmul mtwo (madd hi (mmul (msub hi hk) ht)))
    (mmul (mmul (mmul mtwo mbMc) h) he)) (mmul (mmul mtwo hb) (msq (mmul mtwo hr))))
    (mdiv (mmul hr hj) mtwo)
def hvB (x v:IV):=4*bd 3650+4*Row0.kkB*x+2*(Row0.kkB-x)*v
lemma mHV {x v:ℝ} {A B:IV}(h:x∈A) (he:v∈B): HV x v∈ hvB A B :=
  madd (madd (mmul mfour mBBc.2.1) (mmul (mmul mfour Row0.mkkB) h)) (mmul (mmul mtwo (msub Row0.mkkB h)) he)

noncomputable def Hbnd (k:Bool) (x z:Nat):=
  HV (eR k (panel x).qR) (eR k (panel z).sr) + (if k then 2*r*rPanel z else -(2*r*rPanel z))
def hbB (k:Bool)(x z:Nat):=
  let V:=2*bd 2200*bd (panel z).rh
  hvB (eB k (panel x).qR) (eB k (panel z).sr)+ (if k then V else -V)
lemma hBm (k:Bool)(x z:Nat):Hbnd k x z∈hbB k x z := by
  have h : Profile.r∈bd 2200 := by convert mbd 2200; norm_num [r]
  have he:=mmul (mmul mtwo h) (mbd (panel z).rh)
  unfold Hbnd hbB
  refine madd (mHV (ek ..) (ek ..)) ?_
  cases k
  · exact mneg he
  exact he
def cond (x z:ℕ) (a b:Bool):Bool:= Less
  (costB (eB true (panel x).sr) (eB true (panel z).sr))
  (defB (hbB a x z) (eB b (panel x).vR))
def corners (x z:ℕ):Bool:=
  cond x z true true && cond x z true false && cond x z false true && cond x z false false
def allCn (x:Nat): Bool:= (List.range 9).all (corners x)
lemma passC (x:Nat) (hx:x≤8): allCn x=true := by
  interval_cases x <;> decide +kernel
lemma corner_pos {x z:Nat}(h:x≤8)(he:z≤8)(a b:Bool):
    Lcost (eR true (panel x).sr) (eR true (panel z).sr) <
      Ldef (Hbnd a x z) (eR b (panel x).vR):= by
  apply mlt (mCost (ek ..) (ek ..)) (mDef (hBm a x z) (ek ..))
  have hp := List.all_eq_true.mp (passC x h) z (List.mem_range.mpr (by omega))
  suffices hh:cond x z a b=true from hh
  simp only [corners,Bool.and_eq_true] at hp; cases a <;> cases b
  · exact hp.2
  · exact hp.1.2
  · exact hp.1.1.2
  exact hp.1.1.1

lemma lpos {x y a b c T:ℝ} (hc:c∈Icc (0:ℝ) 1) (hx:T<Ldef x a) (hy:T<Ldef y b):
    T<Ldef (mix x y c) (mix a b c) := by
  have he : T < mix (Ldef x a) (Ldef y b) c := by
    unfold mix; have h1:=hc.1; have h2:=hc.2
    rcases le_or_gt 1 c with h|h
    · have hh:c=1:=le_antisymm h2 h; rw [hh]; linarith
    have hi:= mul_lt_mul_of_pos_left hx (show 0<1-c by linarith)
    have hh:= mul_le_mul_of_nonneg_left hy.le h1
    linarith
  apply lt_of_lt_of_le he
  let r:=Profile.tr/(2*h₀)+1/alpha
  have hr:0≤r:=by unfold r Profile.tr h₀ alpha; norm_num
  have hh : Ldef (mix x y c) (mix a b c) - mix (Ldef x a) (Ldef y b) c=
      r*(1-c)*c*((x+a)-(y+b))^2:= by unfold mix Ldef r; ring
  rw [← sub_nonneg,hh]; have hp:=hc.1; have hz:0≤1-c:=sub_nonneg.mpr hc.2
  positivity
lemma whole {x z:Nat} (hx:x≤8) (hz:z≤8) (t v:ℝ)
    (ht:t∈Icc (Hbnd false x z) (Hbnd true x z))
    (hv:v∈Icc (eR false (panel x).vR) (eR true (panel x).vR)):
    Lcost (eR true (panel x).sr) (eR true (panel z).sr)< Ldef t v := by
  obtain ⟨a,ha,he⟩:= mix_exists ht.1 ht.2
  obtain ⟨b,hb,hg⟩:= mix_exists hv.1 hv.2
  let c:=Lcost (eR true (panel x).sr) (eR true (panel z).sr)
  have h (p t:ℝ):mix t t p=t:=by unfold mix; ring
  have hh (k:Bool):c<Ldef (Hbnd k x z) v := by
    have hi:=lpos hb (corner_pos hx hz k false) (corner_pos hx hz k true)
    rwa [h, ← hg] at hi
  have hi:=lpos ha (hh false) (hh true)
  rwa [← he,h] at hi
end GeneralMahler.SCal.PA

end OAI
