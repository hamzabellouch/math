import OAI.Analysis.FourierLLogL.Snapshot.Rec

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Snapshot
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart
variable {M j J : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

namespace Plot

structure Comes (w : Board M) (s : Scene M) (j J : ℕ) (f : Grid M → ℝ) : Prop where
  valid : w.chart.Sound
  stored :
    ∀ q, w.previous=some q →
      Safe q j J f ∧ work q j J f ∧ settled q j ∧
        q.here.lev < M ∧ below s.here q.here ∧
        q.fund=s.fund ∧ q.live=s.live ∧ q.norm=s.norm

lemma vacant_comes (s : Scene M) : Comes (vacant M) s j J f := by
  refine ⟨classic_sound _,?_⟩
  simp [vacant]
lemma comes_down (p : Plot) {s q : Scene M} {l}
    (h : Following j J f (.ran s q l)) {g : Board M}
    (hp : Comes g s j J f) (b) :
    Comes (p.turn g q) (q.smaller b) j J f := by
  have hZ := zoom_spec _ hp.valid p.ix p.main h
  obtain ⟨ha,hb,hc,hv,hE,hk⟩ := h
  refine ⟨hZ.sonic,?_⟩
  intro x hx
  simp only [turn] at hx
  split_ifs at hx with hX hY
  · obtain rfl := Option.some.inj hx
    exact ⟨hc,hv,hE,(rooted _ (hk false)).within.2,child_below _ _,rfl,rfl,rfl⟩
  obtain ⟨ha,hc,hE,h₁,h₂,h₃,h₄,h₅⟩ := hp.stored _ hx
  change _∧_∧_∧_∧below (q.here.child b) _ ∧ x.fund=q.fund ∧ x.live=q.live ∧ x.norm=q.norm
  rw [hb.1.fund,hb.1.flat,hb.1.mode,hb.1.here]
  exact ⟨ha,hc,hE,h₁,below_trans (child_below _ _) h₂,h₃,h₄,h₅⟩

def catches (p : Plot) (s : Scene M) (c : Board M) (j : ℕ) (x : Grid M) :=
    intense p.main s (side p.ix) x ∧ atReach (p.now c s).items (spotLimit s j p.ix p.main) x

def aligned (p : Plot) (s : Scene M) (j : ℕ) (x y : Grid M) :=
    let r := 2*spotLimit s j p.ix p.main
    if p.main then ∃ k, delta s.fund.mood k ≤ sepRad j ∧ rad (x-y-k) ≤ r else rad (x-y) ≤ r

lemma effort_bounds :
    ∀ᶠ j : ℕ in atTop, ∀ p : Plot, (p.main=true → p.ix ≤ mainIx j) →
      64*tolerance j p.ix p.main +20*sharp p.ix ≤ amp p.ix p.main / 2 := by
  filter_upwards [h_large 100000] with j hg p hp
  let b := side p.ix
  have he := side_pos p.ix
  have h6 : b^6 ≤ b^2 := pow_le_pow_of_le_one he.le (side_le _) (by omega)
  have h4 : b^4 ≤ b := by simpa using pow_le_pow_of_le_one he.le (side_le _) (by omega : 1 ≤ 4)
  cases hm : p.main with
  | false =>
    have hb : b^2 ≤ b := by simpa using pow_le_pow_of_le_one he.le (side_le _) (by omega : 1 ≤ 2)
    change 64*(b^4/65536)+20*(b^6/32768) ≤ b/2
    nlinarith [show 0 < b from he]
  | true =>
    change 64*(1/Thermal.H j^40)+20*(b^6/32768) ≤ b^2/2
    have hx := (main_bounds j (show p.ix ≤ testIx j from Nat.le_trans (hp hm) (by unfold testIx; omega))).1
    change _ ≤ b^2/100 at hx
    let a := Thermal.H j
    have hh : a ≤ a^8 := by simpa using pow_le_pow_right₀ (H_ge j) (by omega : 1 ≤ 8)
    have ht : 64*(1/a^40) ≤ b^2/4 := by
      apply le_trans (b:=25*((1/6400)/a^32)) _ (by unfold a; linarith)
      have hp' : 0 < a := H_pos j
      field_simp
      change 100000 ≤ a at hg
      nlinarith
    unfold a at *
    nlinarith [sq_nonneg b]

lemma currently :
    ∀ᶠ j : ℕ in atTop, ∀ (p : Plot), (p.main=true → p.ix ≤ mainIx j) →
    ∀ M J : ℕ, ∀ f : Grid M → ℝ, ∀ s q : Scene M, ∀ l,
      Following j J f (.ran s q l) → ∀ g : Board M, Comes g s j J f →
      cardStep p (turn p g q) → ∀ x, catches p q g j x →
        ∃ v : Scene M, (turn p g q).previous=some v ∧ below q.here v.here ∧
          ∃ y∈net v j p.ix p.main, aligned p q j x y := by
  filter_upwards [effort_bounds] with j h p hp M J f s q l hl c hc hC x hx
  classical
  obtain ⟨ha,hb,hh,hd,hQ,hk⟩ := hl
  obtain ⟨⟨b,hy⟩,v,hv,hD⟩ := hx
  let t := q.smaller b
  let B := p.main
  let r := spotLimit q j p.ix B
  have he₁ := share_small hd
  have hv' := (rooted _ (hk b))
  have hX : ReadyAt t := ⟨hv'.within,hv'.positive⟩
  have hqt : q.here.lev < M := (rooted _ (hk false)).within.2
  have hτ := h p hp
  let V := amp p.ix B
  let L := tolerance j p.ix p.main
  have hD' := share_child q hh.within.1 hqt hh.positive he₁.1 he₁.2 b
  have HX : V ≤ magnitude B t v+64*L := by
    apply le_trans hy
    have H := magnitude_near B t x v hX he₁.1.le 4 hD'
    have HE : 4*(16*t.here.len*rad (x-v)) ≤ 64*L := by
      rw [show t.here.len=q.here.len/2 from child_len _ _]
      have hp := q.here.len_pos; change rad _ ≤ L*q.here.invlen at hD
      calc
        _ ≤ 4*(16*(q.here.len/2)*(L*q.here.invlen)) := by gcongr
        _ = 32*L := by rw [rinv]; field_simp; ring
        _ ≤ 64*L := by linarith [show 0 < L from tolerance_pos _ _ _]
    linarith
  have he : strength B (side (p.ix+1)) ≤ V/2 := by
    unfold V amp; rw [side_succ]
    cases B with
    | false => exact le_rfl
    | true =>
      change (_/_)^2 ≤ _^2/2
      nlinarith [side_pos p.ix]
  have HW (s : Scene M) (hh : below q.here s.here) (hv : s.fund=q.fund)
      (H : intense p.main s (side (p.ix+1)) v) :
        ∃ y∈net s j p.ix p.main, aligned p q j x y := by
    obtain ⟨y,hy,hQ⟩ := (net_spec s j p.ix p.main).2.2 _ H
    have hR : spotLimit s j p.ix p.main ≤ spotLimit q j p.ix p.main :=
      mul_le_mul_of_nonneg_left (scale_below hh) (tolerance_pos _ _ _).le
    refine ⟨y,hy,?_⟩
    dsimp only [aligned]
    unfold adjacent at hQ
    by_cases Hz : p.main=true
    · rw [ite_eq_left Hz] at hQ ⊢
      obtain ⟨k,hk,hv'⟩ := hQ
      refine ⟨k,hv ▸ hk,?_⟩
      have HH := rad_add (x-v) (v-y-k)
      rw [show x-v+(v-y-k)=x-y-k by ring] at HH; linarith
    · rw [ite_eq_right Hz] at hQ ⊢
      have HH := rad_add (x-v) (v-y); rw [sub_add_sub_cancel] at HH; linarith
  rw [prior_step _ _ _ hC]
  change 64*L+20*sharp p.ix ≤ V/2 at hτ
  split_ifs with hF
  · refine ⟨q,rfl,below_refl _,HW q (below_refl _) rfl ⟨b,?_⟩⟩
    change strength B _ ≤ magnitude B t v
    linarith [sharp_pos p.ix]
  unfold freshAt at hF
  cases hA : c.previous with
  | none => simp [hA] at hF
  | some w =>
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := hc.stored w hA
    have he₀ : below q.here w.here := hb.1.here.symm ▸ h5
    have he' : w.fund=q.fund := h6.trans hb.1.fund.symm
    refine ⟨w,rfl,he₀,HW w he₀ he' ?_⟩
    rw [hA] at hF
    have hF' : (zoom q p.ix p.main c.chart).items=c.chart.items ∧ ∀ b,
        p.closer c (q.smaller b) w := by push Not at hF; exact hF
    have ht := share_small h2
    have H : magnitude B t v ≤ magnitude B w v +20*sharp p.ix := by
      have hZ : (turn p c q).chart.items=c.chart.items := hF'.1
      have hE : (now p c q).items=c.chart.items := hF'.1
      apply close_display t w B c.chart.items p.ix p.cap _ _ _ _ hX
        ⟨h1.within,h1.positive⟩ he₁.1.le ht.1.le hD' (ht.2.trans (by norm_num))
      · rw [← hZ]; exact hC
      · rwa [hE] at hv
      exact hF'.2 b
    obtain ⟨c,hq⟩ := sup_children B w h1.within.1 h4 h1.positive ht.1.le v
    exact ⟨c,by change strength B _ ≤ _; linarith⟩


def latency (p : Plot) (j : ℕ) :=
    1000*(1+p.cap+p.ix+ell j)
lemma waiting (p : Plot) (j : ℕ) (s t : Node)
    (h : s.lev+latency p j ≤ t.lev)
    (q : ℕ) (hh : q ≤ rangeIx p.cap) :
    horizon s p.ix q ≤ tolerance j p.ix p.main * t.invlen := by
  let c := p.cap; let i := p.ix
  let n := latency p j
  let k := 16+4*i+40*ell j
  unfold horizon speed band
  have h1 : 1+(q:ℝ) ≤ 2^(c+1) := by
    suffices HH : 1+q ≤ 2^(c+1) by exact_mod_cast HH
    have H : 0 < 2^c := by positivity
    change q ≤ 2^c at hh; rw [pow_succ]; omega
  have h2 : 2*((offset i q:ℝ)+10) ≤ 2^(i+c+10) := by
    suffices HH : 2*(offset i q+10) ≤ 2^(i+c+10) by exact_mod_cast HH
    unfold offset; change q ≤ 2^c at hh
    have H1 : i ≤ 2^(i+c) := Nat.le_trans Nat.lt_two_pow_self.le (Nat.pow_le_pow_right (by omega) (by omega))
    have H2 : q ≤ 2^(i+c) := Nat.le_trans hh (Nat.pow_le_pow_right (by omega) (by omega))
    rw [pow_add]; have H : 0 < 2^(i+c) := by positivity
    norm_num; omega
  have H : (1:ℝ)/2^k ≤ tolerance j i p.main := by
    unfold tolerance
    split
    · unfold sig slow
      push_cast; rw [← pow_mul]
      apply one_div_le_one_div_of_le (by positivity); unfold k; apply pow_le_pow_right₀ (by norm_num) (by omega)
    rw [side_pow_two,inv_pow,← pow_mul]
    rw [one_div,div_eq_mul_inv,← mul_inv]
    unfold k; rw [inv_le_inv₀ (by positivity) (by positivity)]
    rw [show (65536:ℝ)=2^16 by norm_num,← pow_add]; apply pow_le_pow_right₀ (by norm_num) (by omega)
  apply le_trans _ (mul_le_mul_of_nonneg_right H t.invlen_pos.le)
  unfold invlen
  apply le_trans (b:=2^(c+1) * ((2:ℝ)^(s.lev+reach i+10)*2^(i+c+10))) (by gcongr)
  rw [← pow_add,← pow_add,one_div,mul_comm _ ((2:ℝ)^t.lev),←div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0<(2:ℝ)^k)).mpr
  rw [← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  unfold k i c latency reach at *
  omega

end Plot
end FourierLLogL.Dyadic.Procedure.Snapshot

end OAI
