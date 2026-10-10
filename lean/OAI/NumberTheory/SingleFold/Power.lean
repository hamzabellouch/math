import OAI.NumberTheory.SingleFold.Pell

namespace OAI

namespace SingleFold.PowerEstimate
lemma choose_ell {δ : ℝ} (hδ : 0 < δ) : ∃ ell : ℕ, 1 ≤ ell ∧ 3 < δ*(ell:ℝ)*Real.log 2 := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  obtain ⟨ell,hell⟩ := exists_nat_gt (3/(δ*Real.log 2))
  refine ⟨ell,?_,?_⟩
  · have : (0:ℝ) < ell := lt_trans (div_pos (by norm_num) (mul_pos hδ hlog)) hell
    have hp : 0<ell := by exact_mod_cast this
    omega
  · have hh := (div_lt_iff₀ (mul_pos hδ hlog)).mp hell
    nlinarith

def input (ell u₀ b n c : ℕ) := (c+1)^ell*(n+1)*(b+1)+u₀
lemma input_bounds {ell u₀ b n c : ℕ} (hell : 1≤ell) (h₀ : 4≤u₀) :
    u₀ ≤ input ell u₀ b n c ∧ (c+1)*(n+1)+4 ≤ input ell u₀ b n c ∧
    b < input ell u₀ b n c ∧ n+1 < input ell u₀ b n c-1 := by
  have hp : c+1≤(c+1)^ell := Nat.le_pow hell
  have h1 : 1≤(c+1)^ell*(n+1) := by
    have : 0<(c+1)^ell*(n+1) := by positivity
    omega
  have hn : n+1≤(c+1)^ell*(n+1) := by nlinarith
  have hm := Nat.mul_le_mul_right (n+1) hp
  dsimp [input]
  constructor; omega
  constructor; nlinarith
  constructor
  · nlinarith
  · have hnn : n+1+4≤(c+1)^ell*(n+1)*(b+1)+u₀ := by nlinarith
    omega

lemma growth_nat {g : ℕ → ℕ} {δ : ℝ} {u : ℕ} (hδ : 0 < δ) (hu : 4≤u)
    (hg : δ*(Real.log (u:ℝ))^2 < Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ)) :
    0<g u ∧ g u<u^u := by
  have hu' : (1:ℝ)<u := by exact_mod_cast (show 1<u by omega)
  have hlog : 0<Real.log (u:ℝ) := Real.log_pos hu'
  have hglog : 0<Real.log (g u:ℝ) := lt_trans (mul_pos hδ (sq_pos_of_pos hlog)) hg.1
  have hgp : 0<g u := by
    by_contra h
    have he : g u=0 := by omega
    simp [he] at hglog
  refine ⟨hgp,?_⟩
  have hup : (0:ℝ)<(u:ℝ)^u := pow_pos (by linarith) _
  have hlg : Real.log (g u:ℝ)<Real.log ((u:ℝ)^u) := by simpa only [Real.log_pow] using hg.2
  have hh := (Real.log_lt_log_iff (by exact_mod_cast hgp) hup).mp hlg
  exact_mod_cast hh

lemma cutoff {δ : ℝ} {ell u₀ b n : ℕ} (hδ : 0<δ) (hell : 1≤ell)
    (hell' : 3<δ*(ell:ℝ)*Real.log 2) (h₀ : 4≤u₀) (hb : 2≤b) :
    let u := input ell u₀ b n (b^n)
    Real.log (((2*(b*u))^n:ℕ):ℝ) < δ*(Real.log (u:ℝ))^2 := by
  dsimp only
  let u := input ell u₀ b n (b^n)
  have hbounds := input_bounds (c:=b^n) (b:=b) (n:=n) hell h₀
  have hu : 4≤u := h₀.trans hbounds.1
  have hbu : b<u := hbounds.2.2.1
  have hb' : (2:ℝ)≤b := by exact_mod_cast hb
  have hu' : (2:ℝ)<u := by exact_mod_cast (show 2<u by omega)
  have hbp : (0:ℝ)<b := by linarith
  have hup : (0:ℝ)<u := by linarith
  have hlog : 0<Real.log (u:ℝ) := Real.log_pos (by linarith)
  have hl2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hlb : Real.log (2:ℝ)≤Real.log (b:ℝ) := Real.log_le_log (by norm_num) hb'
  have hpu : (b^n)^ell≤u := by
    have hp : (b^n)^ell≤(b^n+1)^ell := Nat.pow_le_pow_left (by omega) _
    dsimp [u,input]
    have hpn : (b^n+1)^ell≤(b^n+1)^ell*(n+1) := Nat.le_mul_of_pos_right _ (by omega)
    exact hp.trans (hpn.trans ((Nat.le_mul_of_pos_right _ (by omega : 0<b+1)).trans (Nat.le_add_right _ _)))
  have hlogu : (ell:ℝ)*(n:ℝ)*Real.log (b:ℝ)≤Real.log (u:ℝ) := by
    have hp : (0:ℝ)<((b:ℝ)^n)^ell := pow_pos (pow_pos hbp _) _
    have hh : ((b:ℝ)^n)^ell≤(u:ℝ) := by exact_mod_cast hpu
    have hh' := Real.log_le_log hp hh
    simpa only [Real.log_pow,mul_assoc] using hh'
  have hnu : (ell:ℝ)*(n:ℝ)*Real.log 2≤Real.log (u:ℝ) := by
    exact (mul_le_mul_of_nonneg_left hlb (by positivity : 0≤(ell:ℝ)*(n:ℝ))).trans hlogu
  have htriple : Real.log (2*(b:ℝ)*u) ≤ 3*Real.log (u:ℝ) := by
    rw [Real.log_mul (mul_pos (by norm_num) hbp).ne' hup.ne', Real.log_mul (by norm_num) hbp.ne']
    have hh1 := Real.log_le_log (by norm_num : (0:ℝ)<2) hu'.le
    have hh2 := Real.log_le_log hbp (show (b:ℝ)≤u by exact_mod_cast hbu.le)
    linarith
  have hsmall : 3*(n:ℝ) < δ*Real.log (u:ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hnu hδ.le
    by_cases hn : n=0
    · subst n; simpa using mul_pos hδ hlog
    · have hn' : (0:ℝ)<n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have ht := mul_lt_mul_of_pos_right hell' hn'
      nlinarith
  have hl : Real.log (((2*(b*u))^n:ℕ):ℝ)=(n:ℝ)*Real.log (2*(b:ℝ)*u) := by
    push_cast; rw [Real.log_pow]; congr 2; ring
  rw [hl]
  have hh := mul_le_mul_of_nonneg_left htriple (Nat.cast_nonneg n : (0:ℝ)≤n)
  have hh' := mul_lt_mul_of_pos_right hsmall hlog
  nlinarith
end SingleFold.PowerEstimate

namespace SingleFold.PowerSystem
open PowerEstimate

def System (g : ℕ → ℕ) (ell u₀ b n c : ℕ) (w : Fin 9 → ℕ) : Prop :=
  2≤b ∧ w 0=input ell u₀ b n c ∧ w 1=g (w 0) ∧
  (w 2)^2+(w 3)^2=1+(b*w 0)^2*(w 3)^2 ∧
  (w 4)^2+(w 5)^2=1+(w 0)^2*(w 5)^2 ∧
  0<w 3 ∧ w 3<w 1 ∧ 0<w 5 ∧ w 5<w 1 ∧
  w 3=n+1+(b*w 0-1)*w 6 ∧ w 5=n+1+(w 0-1)*w 7 ∧
  w 3=c*w 5+w 8 ∧ w 8<w 5
lemma pell_eq {a X F : ℕ} (ha : 1<a) :
    X^2+F^2=1+a^2*F^2 ↔ X^2=1+(a^2-1)*F^2 := by
  have hh : a^2-1+1=a^2 := Nat.sub_add_cancel (by nlinarith)
  constructor <;> intro h <;> nlinarith

noncomputable def px (a n : ℕ) : ℕ := if ha : 1<a then Pell.xn ha n else 0
noncomputable def py (a n : ℕ) : ℕ := if ha : 1<a then Pell.yn ha n else 0
lemma coords_eq {a : ℕ} (ha : 1<a) (n : ℕ) :
    (Pell.xn ha n)^2+(Pell.yn ha n)^2=1+a^2*(Pell.yn ha n)^2 := by
  have hh := Pell.pell_eq ha n
  change Pell.xn ha n*Pell.xn ha n-(a*a-1)*Pell.yn ha n*Pell.yn ha n=1 at hh
  have hh' : Pell.xn ha n*Pell.xn ha n=1+(a*a-1)*Pell.yn ha n*Pell.yn ha n := by omega
  apply (pell_eq ha).mpr
  simpa only [pow_two,Nat.mul_assoc] using hh'
variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
lemma pinned {b n c : ℕ} {w : Fin 9 → ℕ} (hw : System g ell u₀ b n c w) :
    w 2=px (b*w 0) (n+1) ∧ w 3=py (b*w 0) (n+1) ∧
    w 4=px (w 0) (n+1) ∧ w 5=py (w 0) (n+1) := by
  rcases hw with ⟨hb,hu,hv,hX,hY,hF,hFv,hH,hHv,hq,hq',hdiv,hr⟩
  have hbds := input_bounds (c:=c) (n:=n) (b:=b) hell h₀
  rw [←hu] at hbds
  have hu4 : 4≤w 0 := h₀.trans hbds.1
  have hgu := growth_nat hδ hu4 (hg _ hbds.1)
  have hla : w 0≤b*w 0 := by nlinarith
  have hba : 1<b*w 0 := by nlinarith
  have hua : 1<w 0 := by omega
  have ha := PellSystem.pell_pinned hu4 hla hbds.2.2.2 ((pell_eq hba).mp hX) (by omega) hq
  have hh := PellSystem.pell_pinned hu4 (le_refl (w 0)) hbds.2.2.2 ((pell_eq hua).mp hY) (by omega) hq'
  simpa only [px,py,dite_eq_left hba,dite_eq_left hua] using And.intro ha.1 (And.intro ha.2 hh)
lemma sound {b n c : ℕ} {w : Fin 9 → ℕ} (hw : System g ell u₀ b n c w) : 2≤b ∧ c=b^n := by
  have hp := pinned hδ hell h₀ hg hw
  have hbds := input_bounds (c:=c) (n:=n) (b:=b) hell h₀
  rcases hw with ⟨hb,hu,hv,hX,hY,hF,hFv,hH,hHv,hq,hq',hdiv,hr⟩
  rw [←hu] at hbds
  rw [hp.2.1,hp.2.2.2] at hdiv
  rw [hp.2.2.2] at hr
  have hua : 1<w 0 := by omega
  have hba : 1<b*w 0 := by nlinarith
  simp only [py,dite_eq_left hua,dite_eq_left hba] at hdiv hr
  exact ⟨hb,PellSystem.quotient_sound hb hbds.2.1 hdiv hr⟩
lemma unique {b n c : ℕ} {w w' : Fin 9 → ℕ} (hw : System g ell u₀ b n c w) (hw' : System g ell u₀ b n c w') : w=w' := by
  have hp := pinned hδ hell h₀ hg hw
  have hp' := pinned hδ hell h₀ hg hw'
  rcases hw with ⟨hb,hu,hv,hX,hY,hF,hFv,hH,hHv,hq,hq',hdiv,hr⟩
  rcases hw' with ⟨_,hu',hv',hX',hY',hF',hFv',hH',hHv',hqq,hqq',hdiv',hr'⟩
  have h0 : w 0=w' 0 := hu.trans hu'.symm
  have h1 : w 1=w' 1 := by rw [hv,hv',h0]
  have h2 : w 2=w' 2 := by rw [hp.1,hp'.1,h0]
  have h3 : w 3=w' 3 := by rw [hp.2.1,hp'.2.1,h0]
  have h4 : w 4=w' 4 := by rw [hp.2.2.1,hp'.2.2.1,h0]
  have h5 : w 5=w' 5 := by rw [hp.2.2.2,hp'.2.2.2,h0]
  have hu4 : 4≤w' 0 := by rw [hu']; exact h₀.trans (input_bounds (c:=c) (n:=n) (b:=b) hell h₀).1
  have h6 : w 6=w' 6 := by
    rw [h0,h3] at hq
    have hh : 2≤b*w' 0 := by nlinarith only [hb,hu4]
    apply Nat.eq_of_mul_eq_mul_left (show 0<b*w' 0-1 by omega)
    omega
  have h7 : w 7=w' 7 := by
    rw [h0,h5] at hq'
    apply Nat.eq_of_mul_eq_mul_left (show 0<w' 0-1 by omega)
    omega
  have h8 : w 8=w' 8 := by rw [h3,h5] at hdiv; omega
  funext j; fin_cases j <;> assumption
lemma complete (hell' : 3<δ*(ell:ℝ)*Real.log 2) {b n : ℕ} (hb : 2≤b) :
    ∃ w, System g ell u₀ b n (b^n) w := by
  let c := b^n
  let u := input ell u₀ b n c
  have hbds := input_bounds (c:=c) (n:=n) (b:=b) hell h₀
  have hu4 : 4≤u := h₀.trans hbds.1
  have hua : 1<u := by omega
  have hba : 1<b*u := by nlinarith
  let F := Pell.yn hba (n+1)
  let H := Pell.yn hua (n+1)
  have hF : 0<F := PellPower.y_positive hba (by omega)
  have hH : 0<H := PellPower.y_positive hua (by omega)
  have hH' : (0:ℝ)<H := by exact_mod_cast hH
  have hrati := PellPower.ratio_bounds (show 1<b by omega) hua n
  change (b:ℝ)^n≤(F:ℝ)/H ∧ (F:ℝ)/H≤(b:ℝ)^n*(1+1/(2*(u:ℝ)-1))^n at hrati
  have herr := PellAnalytics.quotient_error (c:=c) hbds.2.1 (le_refl c) hH' hrati.1 hrati.2
  have hle : c*H≤F := by
    have hh := (le_div_iff₀ hH').mp hrati.1
    exact_mod_cast hh
  have hc : (c:ℝ)=(b:ℝ)^n := by simp only [c,Nat.cast_pow]
  have hlt : F<(c+1)*H := by
    have hh : (F:ℝ)/H < (c:ℝ)+1 := by linarith [herr.2]
    have hh' := (div_lt_iff₀ hH').mp hh
    exact_mod_cast hh'
  let r := F-c*H
  have hr : r<H := by
    dsimp [r]
    have hh : F<c*H+H := by nlinarith only [hlt]
    omega
  have hd : F=c*H+r := by dsimp [r]; omega
  obtain ⟨q,hq,_⟩ := PellSystem.residue_exists hba n
  obtain ⟨q',hq',_⟩ := PellSystem.residue_exists hua n
  have hgrowth := hg u hbds.1
  have hgp := (growth_nat hδ hu4 hgrowth).1
  have hcut := PowerEstimate.cutoff (n:=n) hδ hell hell' h₀ hb
  change Real.log (((2*(b*u))^n:ℕ):ℝ)<_ at hcut
  have hbig : (2*(b*u))^n<g u := by
    have hh := lt_trans hcut hgrowth.1
    have hp : (0:ℝ)<((2*(b*u))^n:ℕ) := by exact_mod_cast (show 0<(2*(b*u))^n by positivity)
    exact_mod_cast (Real.log_lt_log_iff hp (by exact_mod_cast hgp)).mp hh
  have hFv : F<g u := lt_of_le_of_lt (PellPower.power_bounds hba n).2 hbig
  have hHv : H<g u := by
    apply lt_of_le_of_lt (PellPower.power_bounds hua n).2
    exact lt_of_le_of_lt (Nat.pow_le_pow_left (by nlinarith only [hb] : 2*u≤2*(b*u)) n) hbig
  refine ⟨![u,g u,Pell.xn hba (n+1),F,Pell.xn hua (n+1),H,q,q',r],?_⟩
  change 2≤b ∧ u=input ell u₀ b n (b^n) ∧ g u=g u ∧
    (Pell.xn hba (n+1))^2+F^2=1+(b*u)^2*F^2 ∧
    (Pell.xn hua (n+1))^2+H^2=1+u^2*H^2 ∧
    0<F ∧ F<g u ∧ 0<H ∧ H<g u ∧ F=n+1+(b*u-1)*q ∧ H=n+1+(u-1)*q' ∧ F=(b^n)*H+r ∧ r<H
  exact ⟨hb,rfl,rfl,coords_eq hba _,coords_eq hua _,hF,hFv,hH,hHv,hq,hq',hd,hr⟩
end SingleFold.PowerSystem

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
lemma reindex (hf : ScalarSF f) {β : Type} (i : α → β) : ScalarSF (fun z => f (z ∘ i)) :=
  MapSF.reindex hf i
lemma sub (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z-g z) := by
  have h := ((proj (Sum.inr ())).add (hg.reindex Sum.inl)).eq
    ((hf.reindex Sum.inl).max (hg.reindex Sum.inl))
  refine SF.congr h ?_
  intro z

  constructor
  · intro hh
    funext j; cases j
    change z (.inr ())=f (z ∘ Sum.inl)-g (z ∘ Sum.inl)
    omega
  · intro hh
    have he := congrFun hh ()
    change z (.inr ())=f (z ∘ Sum.inl)-g (z ∘ Sum.inl) at he
    omega
end SingleFold.Compiler.ScalarSF

namespace SingleFold.PowerCompilation
open Compiler
lemma system_sf (g : ℕ → ℕ) (ell u₀ : ℕ)
    (hg : SF (fun z : Fin 2 → ℕ => z 1=g (z 0))) :
    SF (fun z : Fin 3⊕Fin 9 → ℕ => PowerSystem.System g ell u₀ (z (.inl 0)) (z (.inl 1)) (z (.inl 2)) (z ∘ Sum.inr)) := by
  let α := Fin 3⊕Fin 9
  let a (i : α) : ScalarSF (fun z : α → ℕ => z i) := ScalarSF.proj i
  let b := a (.inl 0)
  let n := a (.inl 1)
  let c := a (.inl 2)
  let u := a (.inr 0)
  let v := a (.inr 1)
  let X := a (.inr 2)
  let F := a (.inr 3)
  let Y := a (.inr 4)
  let H := a (.inr 5)
  let q := a (.inr 6)
  let q' := a (.inr 7)
  let r := a (.inr 8)
  let k (j : ℕ) : ScalarSF (fun _ : α → ℕ => j) := ScalarSF.const j
  have hinput := u.eq (((((c.add (k 1)).pow ell).mul (n.add (k 1))).mul (b.add (k 1))).add (k u₀))
  have hgraph : SF (fun z : α → ℕ => z (.inr 1)=g (z (.inr 0))) :=
    by
      simpa using hg.reindex (fun j => if j=0 then (Sum.inr 0 : α) else Sum.inr 1)
  have heq1 := ((X.pow 2).add (F.pow 2)).eq ((k 1).add (((b.mul u).pow 2).mul (F.pow 2)))
  have heq2 := ((Y.pow 2).add (H.pow 2)).eq ((k 1).add ((u.pow 2).mul (H.pow 2)))
  have hres1 := F.eq ((n.add (k 1)).add (((b.mul u).sub (k 1)).mul q))
  have hres2 := H.eq ((n.add (k 1)).add ((u.sub (k 1)).mul q'))
  exact ((k 2).le b).and (hinput.and (hgraph.and (heq1.and (heq2.and
    (((k 0).lt F).and ((F.lt v).and (((k 0).lt H).and ((H.lt v).and
      (hres1.and (hres2.and ((F.eq ((c.mul H).add r)).and (r.lt H))))))))))))

lemma power_of_growth (g : ℕ → ℕ) (δ : ℝ) (u₀ : ℕ) (hδ : 0<δ) (h₀ : 4≤u₀)
    (hgraph : SF (fun z : Fin 2 → ℕ => z 1=g (z 0)))
    (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ)) :
    SF (fun z : Fin 3 → ℕ => 2≤z 0 ∧ z 2=z 0^z 1) := by
  obtain ⟨ell,hell,hell'⟩ := PowerEstimate.choose_ell hδ
  have h := (system_sf g ell u₀ hgraph).ex (by
    intro z w w' hw hw'
    exact PowerSystem.unique hδ hell h₀ hg hw hw')
  refine h.congr ?_
  intro z
  constructor
  · rintro ⟨w,hw⟩
    exact PowerSystem.sound hδ hell h₀ hg hw
  · rintro ⟨hb,hc⟩
    obtain ⟨w,hw⟩ := PowerSystem.complete hδ hell h₀ hg hell' (n:=z 1) hb
    refine ⟨w, ?_⟩
    change PowerSystem.System g ell u₀ (z 0) (z 1) (z 2) w
    rw [hc]
    exact hw

theorem power : SF (fun z : Fin 3 → ℕ => 2≤z 0 ∧ z 2=z 0^z 1) := by
  obtain ⟨g,δ,u₀,hδ,h₀,hgraph,hg⟩ := GrowthCompilation.growth
  exact power_of_growth g δ u₀ hδ h₀ hgraph hg
end SingleFold.PowerCompilation

end OAI
