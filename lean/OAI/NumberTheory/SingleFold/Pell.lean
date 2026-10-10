import OAI.NumberTheory.SingleFold.EllipticGrowth

namespace OAI

namespace SingleFold.PellPower

variable {a : ℕ} (ha : 1 < a)

lemma y_positive {n : ℕ} (hn : 0 < n) : 0 < Pell.yn ha n :=
  lt_of_lt_of_le hn (Pell.yn_ge_n ha n)

lemma step_bounds (n : ℕ) :
    (2*a-1)*Pell.yn ha (n+1) ≤ Pell.yn ha (n+2) ∧
    Pell.yn ha (n+2) ≤ (2*a)*Pell.yn ha (n+1) := by
  have hr := Pell.yn_succ_succ ha n
  have hm := (Pell.strictMono_y ha).monotone (Nat.le_succ n)
  have ha' : 2*a-1+1=2*a := by omega
  constructor <;> nlinarith

lemma power_bounds (n : ℕ) :
    (2*a-1)^n ≤ Pell.yn ha (n+1) ∧ Pell.yn ha (n+1) ≤ (2*a)^n := by
  induction n with
  | zero => simp
  | succ n hn =>
    obtain ⟨hl,hu⟩ := step_bounds ha n
    constructor
    · calc
        (2*a-1)^(n+1)=(2*a-1)*(2*a-1)^n := pow_succ' _ _
        _ ≤ (2*a-1)*Pell.yn ha (n+1) := Nat.mul_le_mul_left _ hn.1
        _ ≤ Pell.yn ha (n+2) := hl
    · calc
        Pell.yn ha (n+2) ≤ (2*a)*Pell.yn ha (n+1) := hu
        _ ≤ (2*a)*(2*a)^n := Nat.mul_le_mul_left _ hn.2
        _ = (2*a)^(n+1) := (pow_succ' _ _).symm

noncomputable def rate (n : ℕ) : ℝ := (Pell.yn ha (n+2):ℝ)/Pell.yn ha (n+1)

lemma rate_bounds (n : ℕ) : 2*(a:ℝ)-1 ≤ rate ha n ∧ rate ha n ≤ 2*a := by
  have hp : (0:ℝ) < Pell.yn ha (n+1) := by exact_mod_cast y_positive ha (by omega : 0<n+1)
  simp only [rate]
  rw [le_div_iff₀ hp,div_le_iff₀ hp]
  have hb := step_bounds ha n
  have ha' : 1 ≤ 2*a := by omega
  constructor
  · have hc : ((2*a-1:ℕ):ℝ)=2*(a:ℝ)-1 := by rw [Nat.cast_sub ha']; push_cast; rfl
    rw [←hc]; exact_mod_cast hb.1
  · exact_mod_cast hb.2

lemma rate_pos (n : ℕ) : 0 < rate ha n := by
  have hh := (rate_bounds ha n).1
  have ha' : (1:ℝ)<a := by exact_mod_cast ha
  linarith

lemma rate_zero : rate ha 0 = 2*a := by
  have hh := Pell.yn_succ_succ ha 0
  norm_num only [Pell.yn_zero,Pell.yn_one,add_zero,mul_one] at hh
  simp only [rate,zero_add,Pell.yn_one,hh,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,div_one]

lemma rate_succ (n : ℕ) : rate ha (n+1)=2*a-1/rate ha n := by
  have hr := Pell.yn_succ_succ ha (n+1)
  have hr' : (Pell.yn ha (n+3):ℝ)+Pell.yn ha (n+1)=2*a*Pell.yn ha (n+2) := by exact_mod_cast hr
  have hp : (Pell.yn ha (n+1):ℝ) ≠ 0 := by exact_mod_cast (y_positive ha (by omega : 0<n+1)).ne'
  have hp' : (Pell.yn ha (n+2):ℝ) ≠ 0 := by exact_mod_cast (y_positive ha (by omega : 0<n+2)).ne'
  simp only [rate]
  have hn : n+1+2=n+3 := by omega
  rw [hn]
  rw [one_div_div]
  apply (div_eq_iff hp').mpr
  rw [sub_mul,div_mul_cancel₀ _ hp']
  linarith only [hr']

lemma ratio_rate {b u : ℕ} (hb : 1 < b) (hu : 1 < u) (n : ℕ) :
    (b:ℝ)*rate hu n ≤ rate (show 1 < b*u by nlinarith) n := by
  have hbu : 1 < b*u := by nlinarith
  have hb' : (1:ℝ)<b := by exact_mod_cast hb
  induction n with
  | zero => simp only [rate_zero,Nat.cast_mul]; ring_nf; rfl
  | succ n hn =>
    rw [rate_succ,rate_succ]
    have hp := rate_pos hu n
    have hp' := rate_pos hbu n
    have hh : 1/rate hbu n ≤ (b:ℝ)/rate hu n := by
      rw [div_le_div_iff₀ hp' hp]
      nlinarith
    simp only [Nat.cast_mul,div_eq_mul_inv,one_mul] at hh ⊢
    nlinarith only [hh]

lemma ratio_bounds {b u : ℕ} (hb : 1 < b) (hu : 1 < u) (n : ℕ) :
    (b:ℝ)^n ≤ (Pell.yn (show 1 < b*u by nlinarith) (n+1):ℝ)/Pell.yn hu (n+1) ∧
    (Pell.yn (show 1 < b*u by nlinarith) (n+1):ℝ)/Pell.yn hu (n+1) ≤
      (b:ℝ)^n*(1+1/(2*u-1))^n := by
  have hbu : 1 < b*u := by nlinarith
  have hu' : (1:ℝ)<u := by exact_mod_cast hu
  have hb' : (1:ℝ)<b := by exact_mod_cast hb
  have hd : 0 < 2*(u:ℝ)-1 := by linarith
  induction n with
  | zero => simp
  | succ n hn =>
    have hp : (0:ℝ)<Pell.yn hu (n+1) := by exact_mod_cast y_positive hu (by omega : 0<n+1)
    have hp' : (0:ℝ)<Pell.yn hbu (n+1) := by exact_mod_cast y_positive hbu (by omega : 0<n+1)
    have hrp := rate_pos hu n
    have hrp' := rate_pos hbu n
    have he : (Pell.yn hbu (n+2):ℝ)/Pell.yn hu (n+2) =
        (rate hbu n/rate hu n)*((Pell.yn hbu (n+1):ℝ)/Pell.yn hu (n+1)) := by
      simp only [rate]
      field_simp
    have hl : (b:ℝ) ≤ rate hbu n/rate hu n := (le_div_iff₀ hrp).mpr (ratio_rate hb hu n)
    have hh : rate hbu n/rate hu n ≤ (b:ℝ)*(1+1/(2*u-1)) := by
      have hstep := (rate_bounds hbu n).2
      have hstep' := (rate_bounds hu n).1
      calc
        _ ≤ (2*(b*u:ℕ):ℝ)/(2*u-1) := div_le_div₀ (by positivity) hstep hd hstep'
        _ = (b:ℝ)*(1+1/(2*u-1)) := by push_cast; field_simp; ring
    rw [he,pow_succ',pow_succ']
    constructor
    · exact mul_le_mul hl hn.1 (by positivity) (by positivity)
    · calc
        _ ≤ ((b:ℝ)*(1+1/(2*u-1)))*((b:ℝ)^n*(1+1/(2*u-1))^n) :=
          mul_le_mul hh hn.2 (by positivity) (by positivity)
        _ = _ := by ring

end SingleFold.PellPower

namespace SingleFold.PellAnalytics
lemma reciprocal_binomial (z : ℝ) (hz : 0≤z) (n : ℕ) :
    (1+z)^n*(1-(n:ℝ)*z)≤1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    rw [pow_succ]
    have hh : 0≤(1+z)^n*((n:ℝ)+1)*z^2 := by positivity
    nlinarith only [ih,hh]
lemma binomial_error (z : ℝ) (hz : 0≤z) (n : ℕ) (hn : (n:ℝ)*z<1) :
    (1+z)^n-1≤(n:ℝ)*z/(1-(n:ℝ)*z) := by
  apply (le_div_iff₀ (by linarith)).mpr
  nlinarith only [reciprocal_binomial z hz n]

lemma index_cutoff_real : ∀ u : ℕ, 4≤u → (u:ℝ)<(2-1/(u:ℝ))^(u-1) := by
  apply Nat.le_induction
  · norm_num
  · intro u hu ih
    have hp : (0:ℝ)<u := by exact_mod_cast (show 0<u by omega)
    have hu' : (4:ℝ)≤u := by exact_mod_cast hu
    have hr : 0<2-1/(u:ℝ) := by
      have : 1/(u:ℝ)≤1 := (div_le_one hp).mpr (by linarith)
      linarith
    have hr' : 2-1/(u:ℝ)≤2-1/((u:ℝ)+1) := by
      have := one_div_le_one_div_of_le hp (show (u:ℝ)≤u+1 by linarith)
      linarith
    have hpow := pow_le_pow_left₀ hr.le hr' u
    have hh := mul_lt_mul_of_pos_right ih hr
    have he : (u-1)+1=u := by omega
    rw [←pow_succ,he] at hh
    have he' : (u:ℝ)*(2-1/(u:ℝ))=2*u-1 := by field_simp
    rw [he'] at hh
    push_cast
    linarith

lemma index_cutoff (u : ℕ) (hu : 4≤u) : u^u<(2*u-1)^(u-1) := by
  have hh := index_cutoff_real u hu
  have hp : (0:ℝ)<u := by exact_mod_cast (show 0<u by omega)
  have he : (2-1/(u:ℝ))=((2*u:ℕ)-1:ℕ)/(u:ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤2*u)]
    push_cast
    field_simp
  rw [he,div_pow] at hh
  have hh' := (lt_div_iff₀ (pow_pos hp (u-1))).mp hh
  have he' : (u-1)+1=u := by omega
  rw [←pow_succ',he'] at hh'
  exact_mod_cast hh'

lemma quotient_error {b n c u : ℕ} (hu : (c+1)*(n+1)+4≤u)
    (hc : b^n≤c) {F H : ℝ} (_hH : 0<H)
    (hlo : (b:ℝ)^n≤F/H)
    (hhi : F/H≤(b:ℝ)^n*(1+1/(2*(u:ℝ)-1))^n) :
    0≤F/H-(b:ℝ)^n ∧ F/H-(b:ℝ)^n<1 := by
  have hu' : ((c:ℝ)+1)*((n:ℝ)+1)+4≤u := by exact_mod_cast hu
  have hc' : (b:ℝ)^n≤c := by exact_mod_cast hc
  have hn : (0:ℝ)≤n := by positivity
  have hcn : (0:ℝ)≤c := by positivity
  have hd : 0<2*(u:ℝ)-1 := by nlinarith
  have hdn : 0<2*(u:ℝ)-1-n := by nlinarith
  have hz : 0≤1/(2*(u:ℝ)-1) := by positivity
  have hnz : (n:ℝ)*(1/(2*(u:ℝ)-1))<1 := by
    rw [mul_one_div,div_lt_one hd]
    linarith
  have he := binomial_error _ hz n hnz
  have hh := mul_le_mul_of_nonneg_left he (show 0≤(b:ℝ)^n by positivity)
  have heq : (b:ℝ)^n*((n:ℝ)*(1/(2*(u:ℝ)-1))/(1-(n:ℝ)*(1/(2*(u:ℝ)-1))))=
      (b:ℝ)^n*n/(2*(u:ℝ)-1-n) := by
    field_simp
  rw [heq] at hh
  have hb : F/H-(b:ℝ)^n≤(b:ℝ)^n*n/(2*(u:ℝ)-1-n) := by nlinarith only [hh,hhi]
  have hbc : (b:ℝ)^n*n/(2*(u:ℝ)-1-n)≤(c:ℝ)*n/(2*(u:ℝ)-1-n) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc' hn) hdn.le
  have hcq : (c:ℝ)*n/(2*(u:ℝ)-1-n)<1 := by
    rw [div_lt_one hdn]
    nlinarith
  exact ⟨sub_nonneg.mpr hlo,lt_of_le_of_lt (hb.trans hbc) hcq⟩
end SingleFold.PellAnalytics

namespace SingleFold.PellSystem
lemma index_pinned {a u n i q : ℕ} (hu : 4≤u) (ha : u≤a) (hn : n+1<u-1)
    (hcut : Pell.yn (show 1<a by omega) i<u^u)
    (hres : Pell.yn (show 1<a by omega) i=n+1+(a-1)*q) : i=n+1 := by
  have ha' : 1<a := by omega
  have hi : i<u := by
    by_contra h
    have hui : u ≤ i := by omega
    have hpow : (2*u-1)^(u-1)≤(2*a-1)^(u-1) := Nat.pow_le_pow_left (by omega) _
    have hb := (PellPower.power_bounds ha' (u-1)).1
    rw [Nat.sub_add_cancel (by omega : 1≤u)] at hb
    have hmono := (Pell.strictMono_y ha').monotone hui
    have hcut' := PellAnalytics.index_cutoff u hu
    omega
  have hn' : n+1<a-1 := by omega
  have hmod : i ≡ n+1 [MOD a-1] := by
    have h := (Pell.yn_modEq_a_sub_one ha' i).symm
    rw [hres] at h
    exact h.trans (by unfold Nat.ModEq; simp)
  have his : i<a-1 := by
    by_contra h
    have he : i=a-1 := by omega
    rw [he] at hmod
    have hh : (n+1)%(a-1)=0 := by simpa only [Nat.ModEq,Nat.mod_self] using hmod.symm
    rw [Nat.mod_eq_of_lt hn'] at hh
    omega
  exact hmod.eq_of_lt_of_lt his hn'

lemma pell_pinned {a u n X F q : ℕ} (hu : 4≤u) (ha : u≤a) (hn : n+1<u-1)
    (hpell : X^2=1+(a^2-1)*F^2) (hcut : F<u^u) (hres : F=n+1+(a-1)*q) :
    X=Pell.xn (show 1<a by omega) (n+1) ∧ F=Pell.yn (show 1<a by omega) (n+1) := by
  have ha' : 1<a := by omega
  have he : X*X-(a*a-1)*F*F=1 := by
    have hp : X*X=1+(a*a-1)*F*F := by simpa only [pow_two, Nat.mul_assoc] using hpell
    omega
  obtain ⟨i,rfl,rfl⟩ := Pell.eq_pell ha' he
  have hi := index_pinned hu ha hn hcut hres
  subst i
  exact ⟨rfl,rfl⟩

lemma quotient_sound {b u n c r : ℕ} (hb : 2≤b) (hu : (c+1)*(n+1)+4≤u)
    (hdiv : Pell.yn (show 1<b*u by nlinarith) (n+1)=c*Pell.yn (show 1<u by nlinarith) (n+1)+r)
    (hr : r<Pell.yn (show 1<u by nlinarith) (n+1)) : c=b^n := by
  have hb' : 1<b := by omega
  have hu' : 1<u := by nlinarith
  have hbu : 1<b*u := by nlinarith
  let F := Pell.yn hbu (n+1)
  let H := Pell.yn hu' (n+1)
  have hH : 0<H := PellPower.y_positive hu' (by omega)
  have hH' : (0:ℝ)<H := by exact_mod_cast hH
  have hbds := PellPower.ratio_bounds hb' hu' n
  change (b:ℝ)^n≤(F:ℝ)/H ∧ (F:ℝ)/H≤(b:ℝ)^n*(1+1/(2*(u:ℝ)-1))^n at hbds
  have hlow : b^n*H≤F := by
    have hh := (le_div_iff₀ hH').mp hbds.1
    exact_mod_cast hh
  have hhigh : F<(c+1)*H := by change F=c*H+r at hdiv; change r<H at hr; nlinarith
  have hbc : b^n≤c := by
    by_contra h
    have hc : c+1≤b^n := by omega
    have hh := Nat.mul_le_mul_right H hc
    omega
  have herr := PellAnalytics.quotient_error hu hbc hH' hbds.1 hbds.2
  have hclow : (c:ℝ)≤(F:ℝ)/H := by
    apply (le_div_iff₀ hH').mpr
    have hh : c*H≤F := by change F=c*H+r at hdiv; omega
    exact_mod_cast hh
  have hlt : (c:ℝ)<(b:ℝ)^n+1 := by linarith [herr.2]
  have hcle : c<b^n+1 := by exact_mod_cast hlt
  omega

lemma residue_exists {a : ℕ} (ha : 1<a) (n : ℕ) :
    ∃! q : ℕ, Pell.yn ha (n+1)=n+1+(a-1)*q := by
  have hge := Pell.yn_ge_n ha (n+1)
  obtain ⟨q,hq⟩ := (Pell.yn_modEq_a_sub_one ha (n+1)).symm.dvd'
  refine ⟨q,by omega,?_⟩
  intro q' hq'
  have hai : 0<a-1 := by omega
  have he : (a-1)*q'=(a-1)*q := by omega
  exact Nat.eq_of_mul_eq_mul_left hai he
end SingleFold.PellSystem

end OAI
