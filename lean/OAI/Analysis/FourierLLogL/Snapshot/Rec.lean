import OAI.Analysis.FourierLLogL.Snapshot.Difference
import OAI.Analysis.FourierLLogL.Snapshot.Near

/-! # Timing of snapshot replacement and local charges -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Snapshot
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart
variable {M j J : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

structure Board (M : ℕ) where
  chart : Chart M
  previous : Option (Scene M)

def vacant (M : ℕ) : Board M := ⟨classic M,none⟩

structure Plot where
  main : Bool
  ix : ℕ
  cap : ℕ
namespace Plot
def closer (a : Plot) (g : Board M) (p q : Scene M) :=
    distance (portrait a.main p g.chart.items a.ix a.cap) (portrait a.main q g.chart.items a.ix a.cap) ≤ sharp a.ix

/-- refresh test. Ignore when breaching the cap. -/
def freshAt (a : Plot) (g : Board M) (x : Scene M) : Prop :=
    match g.previous with
    | none => True
    | some q => (zoom x a.ix a.main g.chart).items ≠ g.chart.items ∨
        ∃ b, ¬ a.closer g (x.smaller b) q

def now (a : Plot) (g : Board M) (s : Scene M) :=
    zoom s a.ix a.main g.chart
def cardStep (a : Plot) (g : Board M) := g.chart.size ≤ rangeIx a.cap

def turn (a : Plot) (g : Board M) (s : Scene M) : Board M :=
    { chart:=a.now g s
      previous:=if cardStep a (⟨a.now g s,none⟩:Board M) then
          if a.freshAt g s then some s else g.previous else none }

lemma turn_chart (a : Plot) (g : Board M) (s : Scene M) :
    (a.turn g s).chart = a.now g s := rfl

lemma prior_step (a : Plot) (g : Board M) (s : Scene M) (h : a.cardStep (a.turn g s)) :
    (a.turn g s).previous= if a.freshAt g s then some s else g.previous := by
  unfold turn; dsimp only
  have hh : cardStep a ⟨a.now g s, none⟩ := h
  rw [ite_eq_left hh]

def deltaC (a : Plot) (g : Board M) (x : Scene M) :=
    match g.previous with
    | none => 0
    | some q => cloud (portrait a.main x g.chart.items a.ix a.cap)
        (portrait a.main q g.chart.items a.ix a.cap)

def birth (a : Plot) (g : Board M) (x : Scene M) := if a.freshAt g x then (1:ℝ) else 0

def marker (a : Plot) := (sharp a.ix)^2 / 16

lemma marker_pos (a : Plot) : 0 < a.marker := div_pos (pow_pos (sharp_pos _) _) (by norm_num)


def soundPrev (g : Board M) :=
    ∀ s, g.previous=some s → ReadyAt s ∧ 0 ≤ s.norm ∧ share s ≤ 2

def creditsC (a : Plot) (g : Board M) : ℝ :=
    ↑(rangeIx a.cap) - (g.chart.size:ℝ)

def slotC (a : Plot) (g : Board M) :=
    a.marker * (a.creditsC g + (if g.previous=none then 1 else 0))

def kObs (a : Plot) (g : Board M) (s : Scene M) := sight s a.main g.chart.items (precision a.ix a.cap)

lemma deltaC_pos (a : Plot) {g : Board M} (h : soundPrev g) (s : Scene M)
    (hp : ReadyAt s) (hv : 0 ≤ s.norm) : 0 ≤ a.deltaC g s := by
  unfold deltaC; cases H : g.previous with
  | none => simp only [le_refl]
  | some q =>
    obtain ⟨h1,h2,h3⟩ := h q H
    exact cloud_nonneg _ _ (nonnegative_hist s hp.2 hv _) (nonnegative_hist q h1.2 h2 _)

lemma costC_pos (a : Plot) {g : Board M} (h : a.cardStep g) : 0 ≤ a.creditsC g := by
  unfold creditsC; exact sub_nonneg.mpr (by exact_mod_cast h)
lemma slot_pos (a : Plot) {g : Board M} (h : a.cardStep g) : 0 ≤ a.slotC g :=
    mul_nonneg a.marker_pos.le (by have h := a.costC_pos h; split_ifs <;> linarith)
lemma turn_prev (a : Plot) {g : Board M} (h : soundPrev g) (s : Scene M)
    (h₁ : ReadyAt s) (h₂ : 0 ≤ s.norm) (h₃ : share s ≤ 2) : soundPrev (a.turn g s) := by
  intro x H; simp only [turn] at H
  split_ifs at H with heq he
  · rw [Option.some.injEq] at H; subst x; exact ⟨h₁,h₂,h₃⟩
  · exact h x H

private lemma changed_point {p : Plot} {g : Board M} {s q : Scene M} {u}
    (h : Following j J f (.ran s q u)) (ht : soundPrev g) (hd : 0 < s.norm)
    (hg : g.chart.Sound) (hk : cardStep p (p.turn g q)) :
    let C := p.turn g q
    p.marker*p.birth g q+
      (uniform Bool).Ex (fun b => p.slotC C + p.deltaC C (q.smaller b))
      ≤ p.slotC g + p.deltaC g s +4*(share s-share q) +8*fisher q (p.kObs C q) := by
  classical
  intro C
  let Q := uniform Bool
  have HV : Widen q p.ix p.main g.chart C.chart := zoom_spec g.chart hg p.ix p.main h
  obtain ⟨ha,hb,hc,hx,hy,hu⟩ := h
  have hs : ReadyAt s := ⟨ha.within,ha.positive⟩
  have hq : ReadyAt q := ⟨hc.within,hc.positive⟩
  obtain ⟨h₁,h₂⟩ := share_small hx
  have hI : q.here.lev < M := (rooted _ (hu false)).within.2
  have ht' (b : Bool) : ReadyAt (q.smaller b) := ⟨child_ok q.here hc.within.1 hI b,hc.positive⟩
  have hY (b : Bool) : share (q.smaller b) ≤ 4 := share_child q hc.within.1 hI hc.positive h₁ h₂ b
  let V (i : Scene M) := portrait p.main i C.chart.items p.ix p.cap
  let k := p.kObs C q
  let F (j : Scene M) (s : Scene M) := cloud (V s) (V j)
  have Hx (t : Scene M) (ht : ReadyAt t) (hv : 0 ≤ t.norm) :
      Q.Ex (fun b => F t (q.smaller b)) ≤ F t q+4*fisher q k :=
    cloud_drift q hc.within.1 hI hc.positive h₁.le k (V t) (nonnegative_hist _ ht.2 hv _)
  have hp : p.creditsC C ≤ p.creditsC g := by
    have hZ : g.chart.size ≤ C.chart.size := Finset.card_le_card HV.extend
    exact sub_le_sub_left (by exact_mod_cast hZ) _
  have hi : 0 ≤ share s-share q := by
    unfold share; rw [hb.1.flat]
    exact sub_nonneg.mpr (div_le_div_of_nonneg_right (hb.1.mass_le ha.positive ha.within) hd.le)
  have hF : 0 ≤ fisher q k := (fisher_range _ hc.within.1 hI hc.positive h₁.le _).1
  have hcN := p.deltaC_pos ht s hs hd.le

  have H {w : Scene M} (hw : g.previous=some w) (heq : C.chart.items=g.chart.items) :
      Q.Ex (fun b => F w (q.smaller b)) ≤ p.deltaC g s + 4*(share s-share q)+4*fisher q k := by
    have hT := ht _ hw
    apply le_trans (Hx _ hT.1 hT.2.1)
    apply add_le_add_left
    have H : p.deltaC g s = cloud (hist s k) (V w) := by
      unfold deltaC; rw [hw]
      unfold V k kObs; rw [heq]
      unfold portrait sight optic; rw [hb.1.fund]
    rw [H]
    exact cloud_kill hb.1 hs hq hd.le k _ (nonnegative_hist _ hT.1.2 hT.2.1 _)
  have hh : C.previous = if p.freshAt g q then some q else g.previous := p.prior_step _ _ hk
  rw [Ex_add (f:=fun _ => slotC p C),Ex_const]
  by_cases he : p.freshAt g q
  · rw [ite_eq_left he] at hh
    have Hs : Q.Ex (fun b => p.deltaC C (q.smaller b)) ≤ 4*fisher q k := by
      have hx := Hx _ hq h₁.le
      have ht (x : Scene M) : p.deltaC C x=F q x := by unfold deltaC; rw [hh]
      simp_rw [ht]
      have hc : F q q = 0 := cloud_same _
      rwa [hc,zero_add] at hx
    rw [birth,ite_eq_left he,mul_one]
    change _ + (_+Q.Ex _) ≤ _+8*fisher q k
    have hSlot : p.slotC C = p.marker*p.creditsC C := by unfold slotC; simp [hh]
    rw [hSlot]
    cases hv : g.previous with
    | none =>
      unfold slotC; rw [ite_eq_left hv,mul_add,mul_one]
      nlinarith [marker_pos p]
    | some w =>
      unfold slotC; rw [ite_eq_right (by rw [hv]; simp),add_zero]
      unfold freshAt at he; rw [hv] at he
      rcases he with he|he
      · have H : C.chart.items≠g.chart.items := he
        have HX : g.chart.items ⊂ C.chart.items := Finset.ssubset_iff_subset_ne.mpr ⟨HV.extend, Ne.symm H⟩
        have hz : p.creditsC C+1 ≤ p.creditsC g := by
          have hi : (g.chart.size:ℝ)+1 ≤ C.chart.size := by exact_mod_cast Finset.card_lt_card HX
          unfold creditsC; linarith
        nlinarith [marker_pos p]
      ·
        by_cases H0 : C.chart.items=g.chart.items
        case neg =>
          have HX : g.chart.items ⊂ C.chart.items := Finset.ssubset_iff_subset_ne.mpr ⟨HV.extend, Ne.symm H0⟩
          have hz : p.creditsC C+1 ≤ p.creditsC g := by
            have hi : (g.chart.size:ℝ)+1 ≤ C.chart.size := by exact_mod_cast Finset.card_lt_card HX
            unfold creditsC; linarith
          nlinarith [marker_pos p]
        obtain ⟨b,hG⟩ := he
        have HV := H hv H0
        have HH : p.marker ≤ Q.Ex (fun b => F w (q.smaller b)) := by
          let l := q.smaller b
          obtain ⟨hN1,hN2,hN3⟩ := ht _ hv
          have hZ (i) : 0 ≤ F w (q.smaller i) := cloud_nonneg _ _
            (nonnegative_hist _ (ht' i).2 h₁.le _) (nonnegative_hist _ hN1.2 hN2 _)
          have hY' : (sharp p.ix)^2 ≤ 6*F w l := by
            have Hv : sharp p.ix ≤ distance (V l) (V w) := by
              unfold V; rw [H0]; exact le_of_not_ge hG
            apply le_trans (pow_le_pow_left₀ (sharp_pos _).le Hv _)
            apply le_trans (distance_cloud _ _ (nonnegative_hist _ (ht' _).2 h₁.le _)
              (nonnegative_hist _ hN1.2 hN2 _))
            have ht : ∑ i,V w i = share w := total_hist w hN1.1 _
            have ht' : ∑ i,V l i = share l := total_hist l (ht' b).1 _
            change ((∑ i, V l i)+ ∑ i,V w i)*F w l ≤ _
            rw [ht,ht']
            apply mul_le_mul_of_nonneg_right (by linarith [show share l ≤ 4 from hY b]) (hZ b)
          unfold Q Ex
          rw [Fintype.sum_bool,uniform_apply,uniform_apply]
          unfold marker; unfold l at *
          cases b <;> simp only [Fintype.card_bool,Nat.cast_ofNat] <;> nlinarith [hZ true,hZ false]
        nlinarith [marker_pos p]

  rw [ite_eq_right he] at hh
  obtain ⟨w,hv⟩ : ∃ w, g.previous=some w := by
    cases hx : g.previous
    · simp [freshAt,hx] at he
    · exact ⟨_,rfl⟩
  have hs : p.birth g q=0 := ite_eq_right he
  have heq : C.chart.items=g.chart.items := by
    unfold freshAt at he; rw [hv] at he; exact Classical.byContradiction (fun H => he (Or.inl H))
  have hS' : p.slotC C=p.slotC g := by simp [slotC,creditsC,Chart.size, hh,heq]
  have hV' (x : Scene M) : p.deltaC C x=F w x := by unfold deltaC; rw [hh,hv]
  rw [hs,mul_zero,hS']; simp_rw [hV']
  have ht := H hv heq
  change _ ≤ _+8*fisher q k
  unfold Q at *; linarith


def coinC (p : Plot) := ((rangeIx p.cap : ℕ):ℝ)*precision p.ix p.cap

def debtC (p : Plot) (g : Board M) (x : Scene M) (j : ℕ) :=
    deficit x (p.kObs g x)+(p.creditsC g*p.coinC+(minimumT j)⁻¹)

private lemma debt_recur (p : Plot) (g : Board M) {s q : Scene M} {k}
    (h : Following j J f (.ran s q k)) (hd : 0 < s.norm) (hg : g.chart.Sound)
    (hk : cardStep p g) (hp : cardStep p (p.turn g q)) :
    let C := p.turn g q
    (uniform Bool).Ex (fun b => share (q.smaller b)*debtC p C (q.smaller b) j)
      + (1/4:ℝ)*fisher q (p.kObs C q)
      ≤ share s * debtC p g s j := by
  intro C
  have hm := pre_pos h
  have hC : Widen q p.ix p.main g.chart C.chart := zoom_spec _ hg _ _ h
  let v := (keep s q).snip
  let U := (step q).probs
  let Q := v.probs
  let Z (c : Board M) := p.kObs c q
  let F := Z g; let W := Z C
  let H (x) := deficit x F
  let E (i) := deficit (q.smaller i) W
  let V (c : Board M) := p.creditsC c*p.coinC+(minimumT j)⁻¹
  have HE : Q.entropy ≤ (minimumT j)⁻¹* Q false := debt_at h
  obtain ⟨ha,hb,hv,hp',ht,hs⟩ := h
  have hT (b : Bool) := hs b
  have hR : q.here.lev < M := (rooted _ (hs false)).within.2
  have hS : ReadyAt s := ⟨ha.within,ha.positive⟩
  have hS' : ReadyAt q := ⟨hv.within,hv.positive⟩
  have hQ := hp'.1.2.2
  have hZ : 0 < q.norm := hb.1.flat.symm ▸ hd
  have hM := keep_true hb.1 hS hS' hm
  have hi₁ : deficit q W+V C ≤ H q+V g := by
    by_cases hi : C.chart.items=g.chart.items
    · unfold W Z H F V kObs creditsC size; rw [hi]; exact le_rfl
    have hG : p.creditsC C+1 ≤ p.creditsC g := by
      have hh : g.chart.items ⊂ C.chart.items := Finset.ssubset_iff_subset_ne.mpr ⟨hC.extend, Ne.symm hi⟩
      have he : (g.chart.size:ℝ)+1 ≤ C.chart.size := by exact_mod_cast Finset.card_lt_card hh
      unfold creditsC; linarith
    have hh1 : 0 ≤ p.coinC := by unfold coinC; positivity
    have h₁ := (sight_budget q p.main g.chart.items (precision p.ix p.cap)).1
    have h₂ := (sight_budget q p.main C.chart.items (precision p.ix p.cap)).2
    change deficit q W ≤ _ at h₂
    change _ ≤ H q at h₁
    have h₃ : (C.chart.items.card :ℝ)* precision p.ix p.cap ≤ p.coinC := by
      unfold coinC
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hp) (by positivity)
    unfold V
    nlinarith
  have hv₀ : (minimumT j)⁻¹ ≤ V g :=
    le_add_of_nonneg_left (mul_nonneg (costC_pos _ hk) (by unfold coinC; positivity))
  have h₂ : Q true*(H q+V g) ≤ H s+V g := by
    have hi (b : Bool) : levels (v.dst b)=levels s := by
      unfold levels; rw [show (v.dst b).here=s.here from keep_here hb.1 _]
    have hz : Q.Ex (fun b => H (v.dst b)) ≤ H s+Q.entropy := by
      have hh := old_entropy_cost v F
      have hh' := conditioned_balance F v hM
      unfold H deficit; simp_rw [hi,Ex_sub (f:=fun _ => levels s),Ex_const]
      change v.probs.Ex _+ _ = s.actor.privateH F at hh'
      unfold Q; linarith
    have hZ : 0 ≤ Q false * H (v.dst false) := by
      rcases eq_or_lt_of_le (Q.nonneg false) with h|h
      · rw [← h,zero_mul]
      have HH := other_ok hb.1 hS
      exact mul_nonneg h.le (deficit_nonneg (v.dst false) HH.1 HH.2 ((true_mass hM).mp h) F)
    have ht₁ : Q true + Q false = 1 := by simpa only [Fintype.sum_bool] using Q.total
    rw [Ex,Fintype.sum_bool] at hz
    rw [show v.dst true=q from rfl] at hz
    nlinarith [mul_le_mul_of_nonneg_right hv₀ (Q.nonneg false),show
      V g*(Q true+Q false)=V g by rw [ht₁]; ring]
  have ht₁ := space_deficit q W hv.within.1 hR hv.positive hQ hZ
  have hx b : debtC p C (q.smaller b) j=E b+V C := rfl
  let D (b : Bool) := E b+V C
  have h₁ :
      (uniform Bool).Ex (fun b => share (q.smaller b)*debtC p C (q.smaller b) j)=
        share q * U.Ex D := by
    have HI (b : Bool) : share (q.smaller b)*debtC p C (q.smaller b) j =
        (q.smaller b).mass * (q.norm⁻¹ * D b) := by rw [hx]; unfold share D; simp only [smaller]; ring
    simp_rw [HI]
    rw [← output_split _ hv.within.1 hR hv.positive hQ (fun b => q.norm⁻¹*D b),
      Ex_lmul]
    unfold share U; ring
  have HZ : share q * ((1/4:ℝ)*(q.norm/q.mass)*fisher q W)=1/4*fisher q W := by
    unfold share; field_simp
  have hEq : share q = share s * Q true := by
    have H := kept_mass hb.1 hS hS' hm
    unfold share
    nth_rw 1 [H,hb.1.flat]
    unfold Q v; ring
  rw [h₁,← HZ,← mul_add]
  unfold D; rw [Ex_add (g:=fun b => V C),Ex_const]
  have hDC : debtC p g s j=H s+V g := by
    unfold debtC H F V Z kObs sight optic
    rw [hb.1.fund]
  have hsq : 0 ≤ share q := div_nonneg hQ.le hZ.le
  calc
    _ ≤ share q * (deficit q W + V C) := by
      change U.Ex E + _ ≤ deficit q W at ht₁
      apply mul_le_mul_of_nonneg_left _ hsq; linarith
    _ ≤ share q*(H q+V g) := mul_le_mul_of_nonneg_left hi₁ hsq
    _ ≤ _ := by
      rw [hEq,mul_assoc,hDC]
      exact mul_le_mul_of_nonneg_left h₂ (div_nonneg hm.le hd.le)

def expenses (p : Plot) (g : Board M) (s : Scene M) (j : ℕ) :=
    p.slotC g + p.deltaC g s + 4*share s + 32*(share s*debtC p g s j)

lemma expenses_nonneg (p : Plot) (g : Board M) (s : Scene M) (j : ℕ) (hg : p.cardStep g)
    (h : ReadyAt s) (hp : soundPrev g) (hv : 0 < s.norm) :
    0 ≤ p.expenses g s j := by
  have hm : 0 ≤ s.mass := avg_nonneg _ fun i _ => h.2 i
  have hsc := deltaC_pos p hp s h hv.le
  have Ht := slot_pos p hg
  unfold expenses; have hS : 0 ≤ share s := div_nonneg hm hv.le
  suffices HH : 0 ≤ share s*debtC p g s j by linarith
  rcases eq_or_lt_of_le hm with H|H
  · unfold share; rw [← H,zero_div,zero_mul]
  apply mul_nonneg hS
  unfold debtC
  have hC := p.costC_pos hg
  exact add_nonneg (deficit_nonneg _ h.1 h.2 H _) (add_nonneg
    (mul_nonneg hC (by unfold coinC; positivity)) (inv_nonneg.mpr (minimum_pos j).le))

/-- number born before cap breach; representatives from these births may be retained for
delayed estimates on further jumps -/
def minted (p : Plot) (g : Board M) : List (Beat M) → ℝ
| [] => 0
| b::l => let c := p.turn g b.post
          if p.cardStep c then birth p g b.post + minted p c l else 0

lemma mint_small (p : Plot) (g : Board M) (s : Scene M) (t : Thread M s)
    (h : Following j J f t) (hp : g.chart.Sound) (hg : soundPrev g) (hv : p.cardStep g)
    (hs : 0 < s.norm) :
    p.marker*(s.here.dice M).Ex (fun x => minted p g (t.stream x)) ≤ expenses p g s j := by
  induction t generalizing g with
  | blank =>
    have h1 := rooted _ h
    simpa only [stream,minted,Ex_const,mul_zero] using
      expenses_nonneg p g _ j hv ⟨h1.within,h1.positive⟩ hg hs
  | ran s q k ih =>
    rw [stream_branch k h (fun l _ => minted p g l)]
    let C := p.turn g q
    by_cases hh : p.cardStep C
    case neg =>
      have h1 := rooted _ h
      dsimp only [C] at hh
      simpa only [minted, ite_eq_right hh, Ex_const,mul_zero] using
        expenses_nonneg p g s j hv ⟨h1.within,h1.positive⟩ hg hs
    have hD := changed_point h hg hs hp hh
    have hF := debt_recur p _ h hs hp hv hh
    have hZ := zoom_spec g.chart hp p.ix p.main h
    obtain ⟨ha,hb,hc,hx,hd,hk⟩ := h
    have hv := turn_prev p hg q ⟨hc.within,hc.positive⟩ (share_small hx).1.le (share_small hx).2
    have hq : (uniform Bool).Ex (fun b => share (q.smaller b))=share q := by
      simp only [Ex,uniform_apply,Fintype.sum_bool,Fintype.card_bool,Nat.cast_ofNat]
      have ht := share_split q; linarith
    let f (i : Bool) := ((q.smaller i).here.dice M).Ex fun x => minted p C ((k i).stream x)
    have HM :
        p.marker*((uniform Bool).Ex f) ≤ (uniform Bool).Ex fun i => expenses p C (q.smaller i) j := by
      rw [← Ex_lmul]; apply Ex_mono; intro i
      exact ih i C (hk i) hZ.sonic hv hh (share_small hx).1
    unfold expenses at *
    simp_rw [Ex_add] at *
    simp_rw [Ex_const,Ex_lmul] at HM hD
    rw [hq] at HM

    have HH : p.cardStep (p.turn g q) := hh
    simp only [minted, ite_eq_left HH]
    simp_rw [Ex_add,Ex_const]
    change p.marker*(p.birth g q+(uniform Bool).Ex f) ≤ _
    dsimp only [C] at *
    nlinarith

end Plot
end FourierLLogL.Dyadic.Procedure.Snapshot

end OAI
