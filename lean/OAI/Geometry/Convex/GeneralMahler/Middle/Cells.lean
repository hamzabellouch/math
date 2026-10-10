import OAI.Geometry.Convex.GeneralMahler.Middle.Prefix

namespace OAI
/-! Adaptive grid interpolation verification. -/
open Set Filter Real
namespace GeneralMahler.SCal.Mid
open Grid Jet Profile Segment SE Cert Cert.IV
variable (B:PrefixC)(b:Bool)

def wlt0 (d:Nat):IV:= IV.c (Int.ofNat d)/IV.c 200
def berr (d:Nat):IV:= - (((IV.c 37)/(IV.c 4))*IV.sq (wlt0 d))
def gtwt (b:Bool)(i j:Nat):Bool:=
  if b then decide (i+j>0) else decide (i<j)
def ckF (i j d:ℕ):Bool:=
  gtwt b i j && Less (dotE B b i j) (berr d)
def quad (i j d:ℕ):Bool:=
  ckF B b i j d && ckF B b (i+d) j d &&
    ckF B b i (j+d) d && ckF B b (i+d) (j+d) d
def vac (b:Bool)(i j d:Nat):Bool:=
  if b then decide (j+d < i) || decide (j+d+i+d<64)
  else decide (j+d < i+64)
def stepCheck (i j d:Nat):Bool:= vac b i j d || quad B b i j d
def quadRun : ℕ→ℕ→ℕ→Bool
  | 0,i,j=>stepCheck B b i j 1
  | n+1,i,j=>let d:=2^n
             stepCheck B b i j (d+d) || (quadRun n i j && quadRun n (i+d) j &&
               quadRun n i (j+d) && quadRun n (i+d) (j+d))
noncomputable def limk (d:ℕ):ℝ:= -(37/4)*((d:ℝ)/200)^2
lemma ckval (h:NG)(g:Works B)(i j d:ℕ)(hi:i ≤720)(hj:j ≤720)(hz:ckF B b i j d=true):
    Fval (signF b (nd i)) (nd j)<limk d:= by
  simp only [ckF,Bool.and_eq_true] at hz
  have ht:signF b (nd i)<nd j:= by
    have hv:=hz.1; cases b <;> simp only [gtwt, Bool.false_eq_true, ite_false, ite_true,decide_eq_true_eq] at hv
    · exact nd_m hv
    simp only [signF,ite_true]
    unfold nd
    have he :0 < (i:ℝ)+(j:ℝ):=by exact_mod_cast hv
    linarith
  have hd: (d:ℝ)/200 ∈ wlt0 d:=mgrid d
  apply mlt (dot_ok h _ g _ _ _ hi hj ht) _ hz.2
  have hi:=mneg (mmul (mdiv (mc 37) (mc 4)) (msq hd))
  unfold limk; convert hi using 1
  all_goals first|rfl| norm_num
noncomputable def InRegion (b:Bool)(i j d:Nat)(x y:ℝ):Prop:=
  nd i ≤ x∧ x≤nd (i+d) ∧ nd j ≤ y ∧ y≤ nd (j+d) ∧ x≤y ∧
    32/100 ≤ y-signF b x
lemma vacC (b:Bool){i j d:ℕ}(x y:ℝ)(h:InRegion b i j d x y):vac b i j d=false:=by
  obtain ⟨ha,hb,hc,hd,he,hf⟩:=h
  cases b <;> simp only [signF,vac,Bool.false_eq_true,ite_true,ite_false,Bool.or_eq_false_iff,decide_eq_false_iff_not] at *
  · have hh : (i:ℝ)+64 ≤ j+d :=by unfold nd at *; push_cast at *;linarith
    exact Nat.not_lt.mpr (by exact_mod_cast hh)
  have hh : (i:ℝ)≤j+d:=by unfold nd at *; push_cast at *; linarith
  have hu : (64:ℝ) ≤ j +d+i+d:=by unfold nd at *; push_cast at *;linarith
  exact ⟨Nat.not_lt.mpr (by exact_mod_cast hh),Nat.not_lt.mpr (by exact_mod_cast hu)⟩

lemma chord_U {f:ℝ→ℝ}(hf:Guard f budgetCap) (b:Bool)(i d:ℕ) {x:ℝ}
    (hx:nd i≤x)(he:x≤nd (i+d))(c:ℝ)(h1:f (signF b (nd i))<c)(h2:f (signF b (nd (i+d)))<c):
    f (signF b x)<c-limk d/2:=by
  let A:=nd i; let E:=nd (i+d)
  have hv (u:ℝ): |ddf f u|≤ 37:=(hf.fc u).trans Bcost
  have hh {a b x:ℝ} (ha:a≤x)(hb:x≤b)(hl:b-a= (d:ℝ)/200)(he₁:f a<c)(he₂:f b<c):
      f x < c-limk d/2:=by
    obtain ⟨t,ht,hx⟩:=mix_exists ha hb
    have hi:=chord_error hf.Df hf.Db (ha.trans hb) ht 37 (by norm_num) (fun x _=>hv x)
    rw [hl,← hx] at hi
    have hh:=le_of_abs_le hi
    have hc: mix (f a) (f b) t<c:=by
      unfold mix
      have ht':= sub_nonneg.mpr ht.2
      rcases ht.1.eq_or_lt with h|h
      · rw [← h];linarith
      have he:=mul_lt_mul_of_pos_left he₂ h
      have h1:=mul_le_mul_of_nonneg_left he₁.le ht'
      linarith
    unfold limk;linarith
  cases b
  · exact hh hx he (by unfold nd;push_cast;ring) h1 h2
  exact hh (neg_le_neg he) (neg_le_neg hx) (by unfold nd;push_cast;ring)
    h2 h1

lemma quadCV (H:NG)(g:Works B){i j d:Nat}(hi:i+d ≤720)(hj:j+d ≤720)
    (hz:stepCheck B b i j d=true) {x y:ℝ}(he:InRegion b i j d x y):
    Fval (signF b x) y < 0:=by
  rw [stepCheck,vacC b x y he,Bool.false_or] at hz
  unfold quad at hz; simp only [Bool.and_eq_true] at hz
  obtain ⟨ha,hb,hc,hd,he⟩:=he
  have hh (c:ℕ) (hu:c ≤720) (h₁:ckF B b i c d=true) (h₂:ckF B b (i+d) c d=true):
      Fval (signF b x) (nd c)<limk d-limk d/2:=by
    rw [efFlip H]
    apply chord_U (gv2 H _) b _ _ ha hb
    · rw [efFlip H];exact ckval B b H g _ _ _ (by omega) hu h₁
    rw [efFlip H]; exact ckval B b H g _ _ _ hi hu h₂
  have hv:= chord_U (gv2 H (signF b x)) false j d hc hd _
    (hh _ (by omega) hz.1.1.1 hz.1.1.2) (hh _ hj hz.1.2 hz.2)
  change Fval (signF b x) y < _ at hv; linarith

lemma quadR (H:NG)(g:Works B)(n i j:ℕ)(hi:i+2^n≤720)(hj:j+2^n≤720)
    (h:quadRun B b n i j=true)(x y:ℝ)(he:InRegion b i j (2^n) x y):
    Fval (signF b x) y <0:=by
  induction n generalizing i j with
  | zero=>
    simp only [pow_zero] at *
    exact quadCV B b H g hi hj h he
  | succ n ih=>
    let d:=2^n
    rw [show 2^(n+1)=d+d from by unfold d; rw [pow_succ];omega] at *
    rw [quadRun] at h
    simp only [Bool.or_eq_true,Bool.and_eq_true] at h
    rcases h with h|⟨⟨⟨h0,h1⟩,h2⟩,h3⟩
    · exact quadCV B b H g hi hj h he
    have hh(n:Nat): n+d+d=n+(d+d):=by omega
    have iL:i+d≤720:= le_trans (Nat.add_le_add_left (Nat.le_add_right d d) i) hi
    have jL:j+d≤720:= le_trans (Nat.add_le_add_left (Nat.le_add_right d d) j) hj
    obtain ⟨ha,hb,hc,hd,hx,hv⟩:=he
    rcases le_total x (nd (i+d)) with ht|ht<;>
      rcases le_total y (nd (j+d)) with hu|hu
    · apply ih i j iL jL h0 ⟨ha,ht,hc,hu,hx,hv⟩
    · apply ih i (j+d) iL (by omega) h2 ⟨ha,ht,hu,hh j |>.symm ▸ hd,hx,hv⟩
    · apply ih (i+d) j (by omega) jL h1 ⟨ht,hh i |>.symm ▸ hb,hc,hu,hx,hv⟩
    apply ih (i+d) (j+d) (by omega) (by omega) h3 ⟨ht,hh i |>.symm ▸ hb,hu,hh j |>.symm ▸ hd,hx,hv⟩
end GeneralMahler.SCal.Mid

end OAI
