import OAI.NumberTheory.SingleFold.HeightGrowth

namespace OAI

namespace SingleFold.EllipticModel
open WeierstrassCurve.Affine.Point
abbrev E := CurveHeight.E

def Hx : E.Point → ℕ
  | zero => 1
  | WeierstrassCurve.Affine.Point.some x _ _ => max x.num.natAbs x.den
lemma Hx_pos (Q : E.Point) : 0<Hx Q := by
  cases Q with
  | zero => exact Nat.zero_lt_one
  | some x y h => exact lt_of_lt_of_le x.den_pos (le_max_right _ _)
lemma log_Hx (Q : E.Point) : Real.log (Hx Q:ℝ)=CurveHeight.naiveHeight Q := by
  cases Q with
  | zero => simp only [Hx,Nat.cast_one,Real.log_one,←zero_def,CurveHeight.naiveHeight_zero]
  | some x y h => exact (CurveHeight.naiveHeight_some h).symm
lemma Hx_neg (Q : E.Point) : Hx (-Q)=Hx Q := by
  cases Q with
  | zero => rfl
  | some x y h => rfl

variable {T : Type} [AddCommGroup T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
noncomputable def point (n : ℤ) (t : T) : E.Point := f.symm (fun _ => n,t)
noncomputable def P : E.Point := point f 1 0
noncomputable def index (Q : E.Point) : ℤ := (f Q).1 0
lemma point_add (n m : ℤ) (t s : T) : point f (n+m) (t+s)=point f n t+point f m s := by
  apply f.injective
  simp [point]
  rfl
lemma point_zero : point f 0 0=0 := by
  apply f.injective
  simp [point]
  rfl
lemma point_int (n : ℤ) : point f n 0=n • P f := by
  apply f.injective
  simp [point,P]
  funext i; simp
lemma point_split (n : ℤ) (t : T) : point f n t=n • P f+point f 0 t := by
  rw [←point_int,←point_add,add_zero,zero_add]
lemma point_nsmul (n : ℤ) (t : T) (m : ℕ) : m • point f n t=point f (m*n) (m • t) := by
  apply f.injective
  simp [point]
  rfl
lemma point_torsion [Finite T] (t : T) : IsOfFinAddOrder (point f 0 t) := by
  have h := isOfFinAddOrder_of_finite t
  obtain ⟨n,hn,hnt⟩ := h.exists_nsmul_eq_zero
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n,hn,?_⟩
  rw [point_nsmul,hnt,mul_zero,point_zero]
lemma double_torsion [Finite T] (t : T) : (2:ℕ) • point f 0 t=0 :=
  (Torsion.torsion_iff _).mp (point_torsion f t)
lemma P_nontorsion : ¬IsOfFinAddOrder (P f) := by
  intro h
  obtain ⟨n,hn,hne⟩ := h.exists_nsmul_eq_zero
  have hh := congrArg (fun Q => (f Q).1 0) hne
  simp [P,point] at hh
  omega
lemma normal_form (Q : E.Point) : Q=point f (index f Q) (f Q).2 := by
  apply f.injective
  simp only [point,AddEquiv.apply_symm_apply,index]
  apply Prod.ext
  · funext i
    exact congrArg (fun j => (f Q).1 j) (Subsingleton.elim _ _)
  · rfl

noncomputable def W (m : ℕ) (Q : E.Point) : ℕ := Hx (m • Q)
noncomputable def sequence (m : ℕ) (j : ℕ) : ℕ := W m (j • P f)
lemma W_pos (m : ℕ) (Q : E.Point) : 0<W m Q := Hx_pos _
lemma sequence_zero (m : ℕ) : sequence f m 0=1 := by
  unfold sequence W
  rw [zero_nsmul,nsmul_zero]
  rfl
lemma W_neg (m : ℕ) (Q : E.Point) : W m (-Q)=W m Q := by
  change Hx (m • (-Q))=Hx (m • Q)
  rw [show m • (-Q)= -(m • Q) from (nsmulAddMonoidHom (α:=E.Point) m).map_neg Q,Hx_neg]
lemma W_point [Finite T] (m : ℕ) (hm : Even m) (n : ℤ) (t : T) : W m (point f n t)=W m (n • P f) := by
  obtain ⟨d,hd⟩ := hm
  have ht : m • point f 0 t=0 := by
    rw [hd,show d+d=2*d by omega,mul_comm,mul_smul,double_torsion,nsmul_zero]
  rw [point_split,W,nsmul_add,ht,add_zero]
  rfl
lemma W_index [Finite T] (m : ℕ) (hm : Even m) (Q : E.Point) : W m Q=sequence f m (index f Q).natAbs := by
  calc
    W m Q = W m ((index f Q) • P f) := by
      conv_lhs => rw [normal_form f Q]
      exact W_point f m hm _ _
    _ = sequence f m (index f Q).natAbs := by
      by_cases h : 0 ≤ index f Q
      · have hn : ((index f Q).natAbs:ℤ)=index f Q := by rw [Int.natCast_natAbs,abs_of_nonneg h]
        rw [sequence,←natCast_zsmul,hn]
      · have hn : index f Q= -((index f Q).natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_neg (lt_of_not_ge h),neg_neg]
        conv_lhs => rw [hn,neg_smul,W_neg,natCast_zsmul]
        rfl
lemma sequence_approx (m : ℕ) (c : ℝ)
    (hc : ∀ Q : E.Point, |CurveHeight.naiveHeight Q-2*CurveHeight.canonicalHeight Q|≤c) (j : ℕ) :
    |Real.log (sequence f m j:ℝ)-(2*(m:ℝ)^2*CurveHeight.canonicalHeight (P f))*(j:ℝ)^2|≤c := by
  have hh := hc (m • (j • P f))
  rw [CurveHeight.canonicalHeight_nsmul,CurveHeight.canonicalHeight_nsmul] at hh
  rw [sequence,W,log_Hx]
  convert hh using 1
  congr 1
  ring
noncomputable def xcoord : E.Point → ℚ
  | .zero => 0
  | .some x _ _ => x
noncomputable def ycoord : E.Point → ℚ
  | .zero => 0
  | .some _ y _ => y
lemma xcoord_neg (Q : E.Point) : xcoord (-Q)=xcoord Q := by cases Q <;> rfl
lemma ycoord_neg (Q : E.Point) : ycoord (-Q)= -ycoord Q := by
  cases Q with
  | zero => rfl
  | some x y h => change E.negY x y= -y; simp [WeierstrassCurve.Affine.negY]
lemma xy_unique {Q R : E.Point} (hQ : Q≠0) (hR : R≠0)
    (hx : xcoord Q=xcoord R) (hyQ : 0≤ycoord Q) (hyR : 0≤ycoord R) : Q=R := by
  cases Q with
  | zero => exact False.elim (hQ rfl)
  | some x y h =>
    cases R with
    | zero => exact False.elim (hR rfl)
    | some z w h' =>
      change x=z at hx
      subst z
      have he := CurveHeight.E_equation h
      have he' := CurveHeight.E_equation h'
      have hy : y=w := by
        change 0≤y at hyQ
        change 0≤w at hyR
        nlinarith
      subst w
      rfl
lemma index_point (n : ℤ) (t : T) : index f (point f n t)=n := by simp [index,point]
lemma index_zero : index f 0=0 := by simp [index]
lemma index_add (Q R : E.Point) : index f (Q+R)=index f Q+index f R := by simp [index]
lemma index_neg (Q : E.Point) : index f (-Q)= -index f Q := by simp [index]
lemma point_ne_zero {n : ℤ} (hn : n≠0) (t : T) : point f n t≠0 := by
  intro h
  have hh := congrArg (index f) h
  rw [index_point,index_zero] at hh
  exact hn hh

def Representative (m : ℕ) (Q : E.Point) : Prop :=
  Q≠0 ∧ 0≤ycoord Q ∧ 1<W m Q ∧
  ∀ t : T, Q+point f 0 t≠0 ∧ xcoord (Q+point f 0 t)≤xcoord Q
lemma representative_max {m : ℕ} {Q R : E.Point} (hQ : Representative f m Q)
    (hidx : (index f R).natAbs=(index f Q).natAbs) : xcoord R≤xcoord Q := by
  have hidx' : index f R=index f Q ∨ index f R= -index f Q := by
    exact Int.natAbs_eq_natAbs_iff.mp hidx
  rcases hidx' with h|h
  · let t := (f R).2-(f Q).2
    have he : R=Q+point f 0 t := by
      apply f.injective
      simp only [map_add,point,AddEquiv.apply_symm_apply]
      apply Prod.ext
      · funext i
        change (f R).1 i=(f Q).1 i+0
        simpa only [add_zero,index,show i=(0:Fin 1) from Subsingleton.elim _ _] using h
      · simp [t]
    rw [he]
    exact (hQ.2.2.2 t).2
  · let t := -(f R).2-(f Q).2
    have he : -R=Q+point f 0 t := by
      apply f.injective
      simp only [map_add,map_neg,point,AddEquiv.apply_symm_apply]
      apply Prod.ext
      · funext i
        change -(f R).1 i=(f Q).1 i+0
        have hi : i=(0:Fin 1) := Subsingleton.elim _ _
        simp only [hi,add_zero]
        change -(index f R)=index f Q
        rw [h,neg_neg]
      · simp [t]
    rw [←xcoord_neg R,he]
    exact (hQ.2.2.2 t).2
lemma representative_unique {m : ℕ} {Q R : E.Point}
    (hQ : Representative f m Q) (hR : Representative f m R)
    (hidx : (index f Q).natAbs=(index f R).natAbs) : Q=R :=
  xy_unique hQ.1 hR.1 (le_antisymm (representative_max f hR hidx) (representative_max f hQ hidx.symm)) hQ.2.1 hR.2.1

lemma representative_exists [Finite T] (m : ℕ) (hm : Even m)
    (hstrict : StrictMono (sequence f m)) (j : ℕ) (hj : 1≤j) :
    ∃! Q : E.Point, Representative f m Q ∧ (index f Q).natAbs=j := by
  obtain ⟨t,ht⟩ := Finite.exists_max (fun t : T => xcoord (point f j t))
  let A := point f j t
  have hj0 : (j:ℤ)≠0 := by omega
  have hA : A≠0 := point_ne_zero f hj0 t
  have hiA : (index f A).natAbs=j := by simp [A,index_point]
  have hWA : 1<W m A := by
    rw [W_index f m hm,hiA,←sequence_zero f m]
    exact hstrict (by omega)
  have htA (s : T) : A+point f 0 s≠0 ∧ xcoord (A+point f 0 s)≤xcoord A := by
    change point f j t+point f 0 s≠0 ∧ _
    rw [←point_add,add_zero]
    exact ⟨point_ne_zero f hj0 _,ht _⟩
  have hex : ∃ Q, Representative f m Q ∧ (index f Q).natAbs=j := by
    by_cases hy : 0≤ycoord A
    · exact ⟨A,⟨hA,hy,hWA,htA⟩,hiA⟩
    · refine ⟨-A,⟨neg_ne_zero.mpr hA,?_,?_,?_⟩,?_⟩
      · rw [ycoord_neg]; linarith
      · rw [W_neg]; exact hWA
      · intro s
        have he : -A+point f 0 s= -(A+point f 0 (-s)) := by
          have hn : point f 0 (-s)= -point f 0 s := by
            apply f.injective; simp [point]; rfl
          rw [hn]; abel
        rw [he,xcoord_neg,xcoord_neg]
        exact ⟨neg_ne_zero.mpr (htA (-s)).1,(htA (-s)).2⟩
      · rw [index_neg,Int.natAbs_neg,hiA]
  obtain ⟨Q,hQ⟩ := hex
  refine ⟨Q,hQ,?_⟩
  intro R hR
  exact representative_unique f hR.1 hQ.1 (hR.2.trans hQ.2.symm)

theorem height_constants : ∃ (c : ℝ) (κ m : ℕ),
    0 < c ∧ 0 < κ ∧ 0 < m ∧ Even m ∧
    (∀ Q : E.Point, |CurveHeight.naiveHeight Q-2*CurveHeight.canonicalHeight Q|≤c) ∧
    2*c < 2*(m:ℝ)^2*CurveHeight.canonicalHeight (P f) ∧
    6*c < Real.log κ ∧ Real.log κ < 2*(2*(m:ℝ)^2*CurveHeight.canonicalHeight (P f))-6*c := by
  obtain ⟨c,hc,herr⟩ := CurveHeight.uniform_height
  have hp := CurveHeight.canonicalHeight_pos (P_nontorsion f)
  obtain ⟨κ,hκ⟩ := exists_nat_gt (Real.exp (6*c))
  have hκpos : 0<κ := by exact_mod_cast lt_trans (Real.exp_pos _) hκ
  have hlog : 6*c<Real.log κ := by
    rw [←Real.log_exp (6*c)]
    exact Real.log_lt_log (Real.exp_pos _) hκ
  let B := max (2*c) ((Real.log κ+6*c)/2)
  obtain ⟨d,hd⟩ := exists_nat_gt (max (B/CurveHeight.canonicalHeight (P f)+1) 1)
  have hd1 : (1:ℝ)<d := lt_of_le_of_lt (le_max_right _ _) hd
  have hdn1 : 1<d := by exact_mod_cast hd1
  have hdB : B/CurveHeight.canonicalHeight (P f)+1<(d:ℝ) := lt_of_le_of_lt (le_max_left _ _) hd
  have hB : B<(d:ℝ)*CurveHeight.canonicalHeight (P f) := by
    apply (div_lt_iff₀ hp).mp
    linarith
  have hBd : B<8*(d:ℝ)^2*CurveHeight.canonicalHeight (P f) := by
    have hmul := mul_lt_mul_of_pos_right (show (d:ℝ)<8*(d:ℝ)^2 by nlinarith) hp
    exact hB.trans hmul
  refine ⟨c,κ,2*d,hc,hκpos,by omega,even_two_mul d,herr,?_,hlog,?_⟩
  · have hb := le_max_left (2*c) ((Real.log κ+6*c)/2)
    dsimp [B] at hBd
    push_cast
    nlinarith
  · have hb := le_max_right (2*c) ((Real.log κ+6*c)/2)
    dsimp [B] at hBd
    push_cast
    nlinarith
lemma neighbor_index (n : ℤ) : max (n+1).natAbs (n-1).natAbs=n.natAbs+1 := by
  apply Int.natCast_inj.mp
  simp only [Nat.cast_max,Int.natCast_natAbs,Nat.cast_add,Nat.cast_one]
  rcases le_total 0 n with hn|hn
  · rw [abs_of_nonneg hn,abs_of_nonneg (by omega : 0≤n+1),max_eq_left (by
      rw [abs_le]; omega)]
  · rw [abs_of_nonpos hn,abs_of_nonpos (by omega : n-1≤0),max_eq_right (by
      rw [abs_le]; omega)]
    ring
lemma index_P : index f (P f)=1 := by rw [P,index_point]
lemma neighbor_max [Finite T] (m : ℕ) (hm : Even m) (hs : StrictMono (sequence f m)) (Q : E.Point) :
    max (W m (Q+P f)) (W m (Q-P f))=sequence f m ((index f Q).natAbs+1) := by
  rw [W_index f m hm,W_index f m hm,←hs.monotone.map_max]
  have hi : index f (Q-P f)=index f Q-1 := by
    change (f (Q-P f)).1 0= _
    simp only [map_sub,Prod.fst_sub,Pi.sub_apply]
    change index f Q-index f (P f)= _
    rw [index_P]
  rw [hi,index_add,index_P,neighbor_index]
lemma double_index (Q : E.Point) : (index f ((2:ℕ) • Q)).natAbs=2*(index f Q).natAbs := by
  rw [two_nsmul,index_add,←two_mul,Int.natAbs_mul]
  rfl

lemma representative_index_pos [Finite T] {m : ℕ} (hm : Even m) {Q : E.Point}
    (hQ : Representative f m Q) : 1 ≤ (index f Q).natAbs := by
  have hw := hQ.2.2.1
  rw [W_index f m hm] at hw
  by_contra hn
  have hi : (index f Q).natAbs=0 := by omega
  rw [hi,sequence_zero] at hw
  omega

def Bracket (m u : ℕ) (Q : E.Point) : Prop :=
  W m Q ≤ u+W m (P f) ∧ u+W m (P f) < max (W m (Q+P f)) (W m (Q-P f))
def Window (m κ : ℕ) (Q R : E.Point) : Prop :=
  W m (2 • Q)*W m R*W m (P f) ≤ κ*(W m Q^2*max (W m (R+P f)) (W m (R-P f))) ∧
  W m Q^2*max (W m (R+P f)) (W m (R-P f)) ≤ κ*(W m (2 • Q)*W m R*W m (P f))
lemma sequence_one (m : ℕ) : sequence f m 1=W m (P f) := by simp only [sequence,one_nsmul]
lemma bracket_iff [Finite T] {m : ℕ} (hm : Even m) (hs : StrictMono (sequence f m))
    (u : ℕ) (Q : E.Point) : Bracket f m u Q ↔
      sequence f m (index f Q).natAbs ≤ u+sequence f m 1 ∧
        u+sequence f m 1 < sequence f m ((index f Q).natAbs+1) := by
  dsimp only [Bracket]
  rw [W_index f m hm Q,←sequence_one,neighbor_max f m hm hs]
lemma window_iff [Finite T] {m κ : ℕ} {a c : ℝ} (hm : Even m) (hs : StrictMono (sequence f m))
    (hc : 0 ≤ c) (hκ : 0 < κ) (h₁ : 6*c < Real.log κ) (h₂ : Real.log κ < 2*a-6*c)
    (ha : ∀ j, 1 ≤ j → |Real.log (sequence f m j:ℝ)-a*(j:ℝ)^2| ≤ c)
    {Q R : E.Point} (hQ : Representative f m Q) (hR : Representative f m R) :
    Window f m κ Q R ↔ (index f R).natAbs=(index f Q).natAbs^2 := by
  dsimp only [Window]
  rw [W_index f m hm (2 • Q),W_index f m hm R,W_index f m hm Q,
    ←sequence_one,neighbor_max f m hm hs,double_index]
  exact HeightWindow.square_window (fun j => W_pos _ _) ha hc hκ h₁ h₂
    (representative_index_pos f hm hQ) (representative_index_pos f hm hR)

def GrowthPair (m κ u : ℕ) (A : E.Point × E.Point) : Prop :=
  Representative f m A.1 ∧ Bracket f m u A.1 ∧ Representative f m A.2 ∧ Window f m κ A.1 A.2

lemma growth_pair_existsUnique [Finite T] {m κ : ℕ} {a c : ℝ}
    (hm : Even m) (hs : StrictMono (sequence f m))
    (hu : ∀ U, ∃ j, U < sequence f m j) (hc : 0 ≤ c) (hκ : 0 < κ)
    (h₁ : 6*c < Real.log κ) (h₂ : Real.log κ < 2*a-6*c)
    (ha : ∀ j, 1 ≤ j → |Real.log (sequence f m j:ℝ)-a*(j:ℝ)^2| ≤ c) (u : ℕ) :
    ∃! A, GrowthPair f m κ u A := by
  obtain ⟨k,hk,hku⟩ := GrowthEstimate.bracket_unique hs hu u
  obtain ⟨Q,⟨hQ,hiQ⟩,_⟩ := representative_exists f m hm hs k hk.1
  obtain ⟨R,⟨hR,hiR⟩,_⟩ := representative_exists f m hm hs (k^2) (by nlinarith [hk.1])
  have hbQ : Bracket f m u Q := (bracket_iff f hm hs u Q).mpr (by simpa only [hiQ] using hk.2)
  have hwQR : Window f m κ Q R := (window_iff f hm hs hc hκ h₁ h₂ ha hQ hR).mpr (by rw [hiQ,hiR])
  refine ⟨(Q,R),⟨hQ,hbQ,hR,hwQR⟩,?_⟩
  rintro ⟨Q',R'⟩ ⟨hQ',hbQ',hR',hwQR'⟩
  have hiQ' : (index f Q').natAbs=k := hku _ ⟨representative_index_pos f hm hQ',
    (bracket_iff f hm hs u Q').mp hbQ'⟩
  have hQQ : Q'=Q := representative_unique f hQ' hQ (hiQ'.trans hiQ.symm)
  have hiR' := (window_iff f hm hs hc hκ h₁ h₂ ha hQ' hR').mp hwQR'
  have hRR : R'=R := representative_unique f hR' hR (by rw [hiR',hiQ',hiR])
  exact Prod.ext hQQ hRR

theorem growth_model [Finite T] : ∃ (m κ : ℕ) (g : ℕ → ℕ) (δ : ℝ) (u₀ : ℕ),
    0 < m ∧ Even m ∧ 0 < κ ∧ 0 < δ ∧ 4 ≤ u₀ ∧
    (∀ u, ∃! A : E.Point × E.Point, GrowthPair f m κ u A) ∧
    (∀ u v, (∃ A, GrowthPair f m κ u A ∧ W m A.2=v) ↔ v=g u) ∧
    (∀ u, u₀ ≤ u → δ*(Real.log (u:ℝ))^2 < Real.log (g u:ℝ) ∧
      Real.log (g u:ℝ) < (u:ℝ)*Real.log (u:ℝ)) := by
  classical
  obtain ⟨c,κ,m,hc,hκ,hm,heven,herr,hlarge,hlog,hlog'⟩ := height_constants f
  let a : ℝ := 2*(m:ℝ)^2*CurveHeight.canonicalHeight (P f)
  have hp := CurveHeight.canonicalHeight_pos (P_nontorsion f)
  have ha : 0 < a := by dsimp [a]; positivity
  have happ : ∀ j, 1 ≤ j → |Real.log (sequence f m j:ℝ)-a*(j:ℝ)^2| ≤ c :=
    fun j _ => sequence_approx f m c herr j
  have hs : StrictMono (sequence f m) := GrowthEstimate.sequence_strict
    (fun j => W_pos _ _) (sequence_zero f m) hc.le hlarge happ
  have hunb := GrowthEstimate.sequence_unbounded (fun j => W_pos m (j • P f)) ha happ
  have hpair (u) := growth_pair_existsUnique f heven hs hunb hc.le hκ hlog hlog' happ u
  let A (u : ℕ) : E.Point × E.Point := Classical.choose (hpair u)
  have hA (u) : GrowthPair f m κ u (A u) := (Classical.choose_spec (hpair u)).1
  let g (u) := W m (A u).2
  obtain ⟨u₀,hu₀,hu⟩ := GrowthEstimate.eventual_output (fun j => W_pos m (j • P f)) ha hc.le happ
  refine ⟨m,κ,g,1/(128*a),u₀,hm,heven,hκ,by positivity,hu₀,hpair,?_,?_⟩
  · intro u v
    constructor
    · rintro ⟨B,hB,hv⟩
      have hBA : B=A u := (Classical.choose_spec (hpair u)).2 B hB
      subst B
      exact hv.symm
    · rintro rfl; exact ⟨A u,hA u,rfl⟩
  · intro u huu
    have hQ := (hA u).1
    have hR := (hA u).2.2.1
    have hb := (bracket_iff f heven hs u (A u).1).mp (hA u).2.1
    have hi := (window_iff f heven hs hc.le hκ hlog hlog' happ hQ hR).mp (hA u).2.2.2
    have hg : g u=sequence f m ((index f (A u).1).natAbs^2) := by
      dsimp [g]; rw [W_index f m heven,hi]
    rw [hg]
    exact hu u huu _ (representative_index_pos f heven hQ) hb

end SingleFold.EllipticModel

namespace SingleFold.GrowthCompilation
open Compiler PointCompiler
abbrev E := EllipticModel.E
lemma encoded_height (Q : E.Point) : (encode Q).height=EllipticModel.Hx Q := by
  cases Q with
  | zero => change max ((RationalCode.encode 0).p+(RationalCode.encode 0).n) (RationalCode.encode 0).d=1
            rw [rational_height]; norm_num
  | some x y h => exact rational_height x
lemma encoded_x (Q : E.Point) : (encode Q).x.value=EllipticModel.xcoord Q := by
  cases Q <;> exact RationalCode.encode_value _
lemma encoded_y (Q : E.Point) : (encode Q).y.value=EllipticModel.ycoord Q := by
  cases Q <;> exact RationalCode.encode_value _
lemma height_sf {α : Type} {Q : (α → ℕ) → E.Point} (hQ : PointSF Q) (m : ℕ) :
    ScalarSF (fun z => EllipticModel.W m (Q z)) := by
  refine MapSF.congr (PointSF.height m hQ) ?_
  intro z; funext j; exact encoded_height _

section
variable {T α : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
variable {Q R : (α → ℕ) → E.Point}
lemma representative_sf (m : ℕ) (hQ : PointSF Q) :
    SF (fun z => EllipticModel.Representative f m (Q z)) := by
  have hy := hQ.ynonneg.congr (fun z => by rw [encoded_y])
  have hw := (ScalarSF.const 1).lt (height_sf hQ m)
  have ht := SF.all (fun t : T =>
    let hadd := hQ.add (PointSF.const (EllipticModel.point f 0 t))
    hadd.nonzero.and (hadd.xle hQ))
  refine (hQ.nonzero.and (hy.and (hw.and ht))).congr ?_
  intro z
  change (Q z ≠ 0 ∧ 0 ≤ EllipticModel.ycoord (Q z) ∧ 1 < EllipticModel.W m (Q z) ∧
    ∀ t : T, Q z + EllipticModel.point f 0 t ≠ 0 ∧
      (encode (Q z + EllipticModel.point f 0 t)).x.value ≤ (encode (Q z)).x.value) ↔ _
  simp only [EllipticModel.Representative, encoded_x]
omit [Finite T] in
lemma bracket_sf (m : ℕ) {u : (α → ℕ) → ℕ} (hu : ScalarSF u) (hQ : PointSF Q) :
    SF (fun z => EllipticModel.Bracket f m (u z) (Q z)) := by
  have hw := height_sf hQ m
  have hplus := height_sf (hQ.add (PointSF.const (EllipticModel.P f))) m
  have hminus := height_sf (hQ.add (PointSF.const (-EllipticModel.P f))) m
  have hb := hu.add (ScalarSF.const (EllipticModel.W m (EllipticModel.P f)))
  have hn := hplus.max hminus
  refine ((hw.le hb).and (hb.lt hn)).congr ?_
  intro z
  simp only [sub_eq_add_neg,EllipticModel.Bracket]
  rfl
omit [Finite T] in
lemma window_sf (m κ : ℕ) (hQ : PointSF Q) (hR : PointSF R) :
    SF (fun z => EllipticModel.Window f m κ (Q z) (R z)) := by
  have hL := ((height_sf (hQ.smul 2) m).mul (height_sf hR m)).mul
    (ScalarSF.const (EllipticModel.W m (EllipticModel.P f)))
  have hmax := (height_sf (hR.add (PointSF.const (EllipticModel.P f))) m).max
    (height_sf (hR.add (PointSF.const (-EllipticModel.P f))) m)
  have hD := ((height_sf hQ m).pow 2).mul hmax
  refine ((hL.le ((ScalarSF.const κ).mul hD)).and (hD.le ((ScalarSF.const κ).mul hL))).congr ?_
  intro z
  simp only [sub_eq_add_neg,EllipticModel.Window]
  rfl
lemma pair_sf (m κ : ℕ) {u : (α → ℕ) → ℕ} (hu : ScalarSF u) (hQ : PointSF Q) (hR : PointSF R) :
    SF (fun z => EllipticModel.GrowthPair f m κ (u z) (Q z,R z)) :=
  (representative_sf f m hQ).and ((bracket_sf f m hu hQ).and
    ((representative_sf f m hR).and (window_sf f m κ hQ hR)))
end

lemma decode_injective_valid {a b : Code} (ha : a.Valid) (hb : b.Valid)
    (he : a.decode=b.decode) : a=b := by
  apply Code.unique ha hb
  simpa only [Code.decode,dite_eq_left ha,dite_eq_left hb] using he

section
variable {T : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
lemma graph_sf (m κ : ℕ) (hunique : ∀ u, ∃! A, EllipticModel.GrowthPair f m κ u A) :
    SF (fun z : Fin 2 → ℕ => ∃ A, EllipticModel.GrowthPair f m κ (z 0) A ∧ EllipticModel.W m A.2=z 1) := by
  let α := Fin 2⊕(Fin 2×Var)
  let q : Var → α := fun k => .inr (0,k)
  let r : Var → α := fun k => .inr (1,k)
  let Q (z : α → ℕ) := (fromTuple (z ∘ q)).decode
  let R (z : α → ℕ) := (fromTuple (z ∘ r)).decode
  have hQ : PointSF Q := PointSF.var q
  have hR : PointSF R := PointSF.var r
  have hv := allValid_semi.reindex (Sum.inr : Fin 2×Var → α)
  have hp := pair_sf f m κ (ScalarSF.proj (.inl 0)) hQ hR
  have hw := (height_sf hR m).eq (ScalarSF.proj (.inl 1))
  have h := hv.1.and (hp.and hw)
  have hdec (z : Fin 2 → ℕ) (w : Fin 2×Var → ℕ) :
      (Q (Sum.elim z w),R (Sum.elim z w))=((At w 0).decode,(At w 1).decode) := rfl
  have hu : ∀ (z : Fin 2 → ℕ) (w w' : Fin 2×Var → ℕ),
      (AllValid w ∧ EllipticModel.GrowthPair f m κ (z 0) ((At w 0).decode,(At w 1).decode) ∧
        EllipticModel.W m (At w 1).decode=z 1) →
      (AllValid w' ∧ EllipticModel.GrowthPair f m κ (z 0) ((At w' 0).decode,(At w' 1).decode) ∧
        EllipticModel.W m (At w' 1).decode=z 1) → w=w' := by
    intro z w w' hw hw'
    have he := (hunique (z 0)).unique hw.2.1 hw'.2.1
    have hcode (i : Fin 2) : At w i=At w' i := by
      apply decode_injective_valid (hw.1 i) (hw'.1 i)
      fin_cases i
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    funext ⟨i,j⟩
    exact congrFun (fromTuple_injective (hcode i)) j
  refine (h.ex hu).congr ?_
  intro z
  change (∃ w : Fin 2×Var → ℕ, AllValid w ∧
    EllipticModel.GrowthPair f m κ (z 0) ((At w 0).decode,(At w 1).decode) ∧
    EllipticModel.W m (At w 1).decode=z 1) ↔ _
  constructor
  · rintro ⟨w,_,hp,hw⟩; exact ⟨_,hp,hw⟩
  · rintro ⟨⟨P,S⟩,hp,hw⟩
    let w : Fin 2×Var → ℕ := fun v => tuple (encode (if v.1=0 then P else S)) v.2
    have hc (i : Fin 2) : At w i=encode (if i=0 then P else S) := from_tuple _
    have hd0 : (At w 0).decode=P := by rw [hc]; exact decode_encode P
    have hd1 : (At w 1).decode=S := by rw [hc]; exact decode_encode S
    refine ⟨w,?_,?_,?_⟩
    · intro i; rw [hc]; exact encode_valid _
    · simpa only [hd0,hd1] using hp
    · simpa only [hd1] using hw
end

theorem growth : ∃ (g : ℕ → ℕ) (δ : ℝ) (u₀ : ℕ), 0 < δ ∧ 4 ≤ u₀ ∧
    SF (fun z : Fin 2 → ℕ => z 1=g (z 0)) ∧
    (∀ u, u₀ ≤ u → δ*(Real.log (u:ℝ))^2 < Real.log (g u:ℝ) ∧
      Real.log (g u:ℝ) < (u:ℝ)*Real.log (u:ℝ)) := by
  obtain ⟨T,hT,hfin,⟨f⟩⟩ := CurveRank.rank_one
  let := hT
  let := hfin
  obtain ⟨m,κ,g,δ,u₀,_,_,_,hδ,hu₀,hunique,hgraph,hest⟩ := EllipticModel.growth_model f
  exact ⟨g,δ,u₀,hδ,hu₀,(graph_sf f m κ hunique).congr (fun z => hgraph (z 0) (z 1)),hest⟩
end SingleFold.GrowthCompilation

end OAI
