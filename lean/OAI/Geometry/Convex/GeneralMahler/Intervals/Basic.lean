import Mathlib

namespace OAI
/-!
Fixed-denominator rational interval certificates (§07–08).
Unknown intervals admit all real values.
-/
namespace GeneralMahler.Cert
inductive IV
  | unk
  | box (lo hi:Int)
deriving DecidableEq, Repr

namespace IV
def den : Int := 1000000000000000000000000000000
noncomputable def w (a:Int) := (a:ℝ)/(den:ℝ)
def Has (x:ℝ): IV → Prop
  | unk => True
  | box l h=> w l ≤ x ∧ x ≤ w h

instance : Membership ℝ IV := ⟨fun v x=>Has x v⟩

def c (n:Int):IV := box (n*den) (n*den)
instance (n:Nat) : OfNat IV n := ⟨c n⟩

protected def add0 : IV→IV→IV
  | box a b,box c d=> box (a+c) (b+d)
  | _,_=> unk
instance : Add IV := ⟨IV.add0⟩
protected def n0 : IV → IV
  | box a b=> box (-b) (-a)
  | _=> unk
instance : Neg IV := ⟨IV.n0⟩
instance : Sub IV := ⟨fun a b=> a+ -b⟩

-- upward round division
def ud (a b : Int) : Int := -((-a)/b)
protected def mul0 : IV → IV → IV
  | box a b,box c d =>
    let l:=min (min (a*c) (a*d)) (min (b*c) (b*d))
    let h:=max (max (a*c) (a*d)) (max (b*c) (b*d))
    box (l/den) (ud h den)
  | _,_=> unk
instance : Mul IV := ⟨IV.mul0⟩

def posInv (a b:Int) : IV := box (den*den/b) (ud (den*den) a)
protected def inv0 : IV→IV
  | box a b=> if a>0 then posInv a b else if b<0 then -posInv (-b) (-a) else unk
  | unk=> unk
instance : Inv IV := ⟨IV.inv0⟩
instance : Div IV := ⟨fun a b=>a*b⁻¹⟩

protected def pow0 (A:IV) : ℕ→IV
  | 0=>1
  | n+1=> (A.pow0 n)*A
instance : Pow IV ℕ := ⟨IV.pow0⟩

def pos0 : IV→IV
  | box a b=> box (max 0 a) (max 0 b)
  | unk=> unk
def clampNN : IV→IV
  | box a b=> box (max 0 a) b
  | unk=> unk

def Zmax : IV→IV→IV
  | box a b,box c d=> box (max a c) (max b d)
  | _,_ =>unk
def Zmin (x y:IV) : IV := - Zmax (-x) (-y)
def Zabs (x:IV) : IV := clampNN (Zmax x (-x))
def sq (x:IV) : IV := (Zabs x)*(Zabs x)
def span : IV→IV→IV
  | box a b,box c d=> box (min a c) (max b d)
  | _,_=>unk
def meet : IV→IV→IV
  | unk,x=>x
  | x,unk=>x
  | box a b,box c d=>box (max a c) (min b d)
def Less : IV→IV→Bool
  | box _ b,box c _=> decide (b<c)
  | _,_=>false
def LeB : IV→IV→Bool
  | box _ b,box c _=> decide (b≤c)
  | _,_=>false
def SubB : IV→IV→Bool
  | _,unk=>true
  | box a b,box c d=> decide (c≤a) && decide (b≤d)
  | _,_=>false

lemma dpos : 0<den := by decide
lemma rpos : 0<(den:ℝ) := by exact_mod_cast dpos
lemma w_mono : Monotone w := by
  intro a b h; apply div_le_div_of_nonneg_right _ rpos.le; exact_mod_cast h
lemma w_strict : StrictMono w := by
  intro a b h; apply div_lt_div_of_pos_right _ rpos; exact_mod_cast h
lemma w_max (a b:Int) : w (max a b)=max (w a) (w b) := w_mono.map_max
lemma w_min (a b:Int) : w (min a b)=min (w a) (w b) := w_mono.map_min
lemma w_add (a b:Int) : w (a+b)=w a+w b := by unfold w; push_cast; ring
lemma w_neg (a:Int): w (-a)= -w a:= by unfold w; push_cast; ring
lemma w0 : w 0=0 := by simp [w]

lemma mc (a:Int) : (a:ℝ)∈c a := by
  change _≤ _ ∧ _ ≤ _
  unfold w
  push_cast; rw [mul_div_cancel_right₀ _ rpos.ne']; exact ⟨le_rfl,le_rfl⟩
lemma nc (n:ℕ) : (n:ℝ)∈c (n:Int) := by simpa using mc (n:Int)
lemma mz : (0:ℝ) ∈ (0:IV) := by change (0:ℝ) ∈ c (Int.ofNat 0); simpa using mc (Int.ofNat 0)
lemma mo : (1:ℝ)∈(1:IV) := by change (1:ℝ) ∈ c (Int.ofNat 1); simpa using mc (Int.ofNat 1)
variable {u v:ℝ} {A B:IV}
lemma madd (hu:u∈A) (hv:v∈B) :
    u+v∈A+B := by
  cases A <;> cases B <;> first | trivial | skip
  rename_i a b c d
  change w _ ≤ _ ∧ _ ≤ w _
  rw [w_add,w_add]
  exact ⟨add_le_add hu.1 hv.1, add_le_add hu.2 hv.2⟩
lemma mneg (hu:u∈A) : -u∈-A := by
  cases A
  · trivial
  change w _ ≤ _ ∧ _ ≤ w _
  rw [w_neg,w_neg]; exact ⟨neg_le_neg hu.2,neg_le_neg hu.1⟩
lemma msub (hu:u∈A) (hv:v∈B) :
    u-v∈A-B := by rw [sub_eq_add_neg]; exact madd hu (mneg hv)
lemma lower_div (a b:Int) (h:0<b):
    ((a/b:Int):ℝ)≤ (a:ℝ)/(b:ℝ) := by
  apply (le_div_iff₀ (show (0:ℝ)<b from by exact_mod_cast h)).mpr
  exact_mod_cast Int.ediv_mul_le a h.ne'
lemma upper_div (a b:Int) (h:0<b):
    (a:ℝ)/(b:ℝ)≤(ud a b:ℝ) := by
  have he:=lower_div (-a) b h
  push_cast at he
  unfold ud; push_cast; rw [neg_div] at he; linarith

lemma product_box (a b c d:ℝ) (ha:a≤u) (hb:u≤b) (hc:c≤v) (hd:v≤d):
    min (min (a*c) (a*d)) (min (b*c) (b*d))≤ u*v ∧
      u*v≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  have hi (r:ℝ): min (r*c) (r*d) ≤ r*v ∧ r*v≤ max (r*c) (r*d) := by
    rcases le_total 0 r with h|h
    · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hc h),
        le_trans (mul_le_mul_of_nonneg_left hd h) (le_max_right _ _)⟩
    exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hd h),
      le_trans (mul_le_mul_of_nonpos_left hc h) (le_max_left _ _)⟩
  rcases le_total 0 v with h|h
  · exact ⟨le_trans (min_le_left _ _) ((hi _).1.trans (mul_le_mul_of_nonneg_right ha h)),
      le_trans ((mul_le_mul_of_nonneg_right hb h).trans (hi _).2) (le_max_right _ _)⟩
  exact ⟨le_trans (min_le_right _ _) ((hi _).1.trans (mul_le_mul_of_nonpos_right hb h)),
      le_trans ((mul_le_mul_of_nonpos_right ha h).trans (hi _).2) (le_max_left _ _)⟩

lemma wdn (a:Int): w (a/den) ≤ w a / den :=
  div_le_div_of_nonneg_right (lower_div a den dpos) rpos.le
lemma wup (a:Int): w a / den ≤ w (ud a den) :=
  div_le_div_of_nonneg_right (upper_div a den dpos) rpos.le
lemma wm (a b:Int): w (a*b)/(den:ℝ)=w a*w b := by unfold w; push_cast; ring

lemma mmul (hu:u∈A) (hv:v∈B) : u*v∈ A*B := by
  cases A <;> cases B <;> first| trivial|skip
  rename_i a b c d
  let l := min (min (a*c) (a*d)) (min (b*c) (b*d))
  let h := max (max (a*c) (a*d)) (max (b*c) (b*d))
  change w (l/den)≤_ ∧ _ ≤ w (ud h den)
  have he : Monotone (fun a=>w a/(den:ℝ)) :=
    fun a b ha=> div_le_div_of_nonneg_right (w_mono ha) rpos.le
  have hmin (a b:Int) : w (min a b)/den=min (w a/den) (w b/den) := he.map_min
  have hmax (a b:Int) : w (max a b)/den=max (w a/den) (w b/den) := he.map_max
  have hp:= product_box (w a) (w b) (w c) (w d) hu.1 hu.2 hv.1 hv.2
  refine ⟨(wdn l).trans ?_,le_trans ?_ (wup h)⟩
  · unfold l; simp_rw [hmin,wm]; exact hp.1
  unfold h; simp_rw [hmax,wm]; exact hp.2

lemma mposInv (a b:Int) (h:0<a) (hu:u∈box a b) : u⁻¹∈posInv a b := by
  have ha : 0<w a := w0 ▸ w_strict h
  have hp : 0<u := lt_of_lt_of_le ha hu.1
  have hh : 0<w b := lt_of_lt_of_le hp hu.2
  have hb : 0<b := w_strict.lt_iff_lt.mp (by rwa [w0])
  change w _ ≤ _ ∧ _≤ w _
  have H (a:Int): (((den*den:Int):ℝ)/(a:ℝ))/(den:ℝ)=(w a)⁻¹ := by
    unfold w; push_cast; rw [inv_div]; field_simp
  refine ⟨le_trans ?_ ((inv_le_inv₀ hh hp).mpr hu.2),
    le_trans ((inv_le_inv₀ hp ha).mpr hu.1) ?_⟩
  · rw [← H]; exact div_le_div_of_nonneg_right (lower_div _ _ hb) rpos.le
  rw [← H]; exact div_le_div_of_nonneg_right (upper_div _ _ h) rpos.le

lemma minv (hu:u∈A) : u⁻¹∈A⁻¹ := by
  cases A
  · trivial
  rename_i a b
  change _∈ if a>0 then _ else if b<0 then _ else _
  split
  next h=> exact mposInv a b h hu
  split
  next h=>
    have hi : -u∈box (-b) (-a):=mneg hu
    simpa only [inv_neg,neg_neg] using mneg (mposInv (-b) (-a) (neg_pos.mpr h) hi)
  trivial

lemma mdiv (hu:u∈A) (hv:v∈B): u/v∈A/B := by rw [div_eq_mul_inv]; exact mmul hu (minv hv)
lemma mpow (hu:u∈A) (n:ℕ): u^n∈A^n := by
  induction n with
  | zero=> rw [pow_zero]; exact mo
  | succ n ih=> rw [pow_succ]; exact mmul ih hu

lemma mle (hu:u∈A) (hv:v∈B) (he:LeB A B=true): u≤v := by
  cases A <;> cases B <;> simp only [LeB,Bool.false_eq_true,decide_eq_true_eq] at he
  exact hu.2.trans ((w_mono he).trans hv.1)
lemma mlt (hu:u∈A) (hv:v∈B) (he:Less A B=true): u<v := by
  cases A <;> cases B <;> simp only [Less,Bool.false_eq_true,decide_eq_true_eq] at he
  exact lt_of_le_of_lt hu.2 (lt_of_lt_of_le (w_strict he) hv.1)
lemma subB (hu:u∈A) (he:SubB A B=true): u∈B := by
  cases B
  · trivial
  cases A
  · contradiction
  simp only [SubB,Bool.and_eq_true,decide_eq_true_eq] at he
  exact ⟨(w_mono he.1).trans hu.1,hu.2.trans (w_mono he.2)⟩

lemma mmax (hu:u∈A) (hv:v∈B): max u v∈Zmax A B := by
  cases A <;> cases B <;> first| trivial|skip
  change w _ ≤ _ ∧ _ ≤ w _
  rw [w_max,w_max]
  exact ⟨max_le_max hu.1 hv.1,max_le_max hu.2 hv.2⟩
lemma mclamp (hu:u∈A) (hh:0≤u): u∈clampNN A := by
  cases A
  · trivial
  refine ⟨?_,hu.2⟩
  rw [w_max,w0]; exact max_le hh hu.1
lemma mabs (hu:u∈A): |u|∈Zabs A := mclamp (mmax hu (mneg hu)) (abs_nonneg _)
lemma msq (hu:u∈A) : u^2∈sq A := by
  have h:=mmul (mabs hu) (mabs hu)
  rwa [← pow_two,sq_abs] at h
lemma mmeet (hu:u∈A) (hv:u∈B): u∈meet A B := by
  cases A
  · exact hv
  cases B
  · exact hu
  refine ⟨?_,?_⟩
  · rw [w_max]; exact max_le hu.1 hv.1
  rw [w_min]; exact le_min hu.2 hv.2
lemma span_conv {x:ℝ} (hu:u∈A) (hv:v∈B) (he:u≤x) (ht:x≤v): x∈span A B := by
  cases A <;> cases B <;> first| trivial|skip
  refine ⟨?_,?_⟩
  · rw [w_min]; exact (min_le_left _ _).trans (hu.1.trans he)
  rw [w_max]; exact ht.trans (hv.2.trans (le_max_right _ _))

end IV
end GeneralMahler.Cert

end OAI
