import OAI.Analysis.FourierLLogL.Paths.Run
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Beam
lemma yield_zero : yieldW (0:Paths.Vector M)=0 := by simp [yieldW]
lemma yield_pos (u : Paths.Vector M) : 0 ≤ yieldW u := Finset.sum_nonneg fun _ _ => norm_nonneg _
lemma yield_add (v w : Paths.Vector M) :
    yieldW (v+w) ≤ yieldW v + yieldW w := by
  unfold yieldW; rw [←Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _ => norm_add_le _ _
lemma yield_sub (v w : Paths.Vector M) :
    yieldW (v-w) ≤ yieldW v + yieldW w := by
  unfold yieldW; rw [←Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _ => norm_sub_le _ _

lemma single_yield {x : Grid M} {s : Scene M} {b : Beat M} {l : Path M} (h : Trip x s (b::l)) (u) :
    yieldW (duties x u b) ≤ 2 := by
  have H := h.2.1.climb
  apply le_trans _ H.tight
  rw [← matter_sum H.fit]
  apply Finset.sum_le_sum; intro i _
  rw [duties,norm_scaleC,trip_final h,one_mul]; exact factor_norm H _ _
end Beam

namespace Run.Streak
open Beam Lamp Tray Desk

/-- One parity of output, sum of odd-numbered positions. -/
def weave (x u : Grid M) : Path M → Paths.Vector M
  | [] => 0
  | [b] => duties x u b
  | b::_c::l => duties x u b + weave x u l

def hem (x u : Grid M) : Path M → Paths.Vector M
  | [] => 0
  | _::l => weave x u l
lemma ribbon_eq (x u : Grid M) (l : Path M) :
    weave x u l+hem x u l=subtotal (duties x u) l := by
  induction l with
  | nil => change 0 + (0:Paths.Vector M)=0; rw [add_zero]
  | cons b l ih =>
    have hi : weave x u (b::l)= duties x u b+hem x u l := by
      cases l
      · simp [hem,weave]
      · rfl
    rw [hi,hem,subtotal_cons,← ih]; abel

private lemma count_both (e : Streak M) (w : Paths.Vector M)
    {b c : Beat M} {l : Path M} {s : Scene M} {x : Grid M}
    (h : Trip x s (b::c::l)) :
    carry (aimed e w b.post) b.bit c.bit=w+duties x e.u b := by
  funext z
  change w z + (curl c.bit:ℂ)*((curl b.bit:ℂ)*factor b.post e.u z)=w z+ _
  rw [duties,trip_delay h]; push_cast; ring

lemma write_down (e : Streak M) {s : Scene M}
    {x : Grid M} (l : Path M) (h : Trip x s l) (hp : ∀ b∈l,e.outer b.post)
    (w : Paths.Vector M) :
    ∃ p q : Path M, l=p++q ∧
      yieldW (w+weave x e.u l) ≤
        watt s e.u w e.thick + 2 + e.thick * ((dealer e).tally (bare w) p) +
          subtotal (beamRent e) l := by
  match l with
  | [] =>
    refine ⟨[],[],rfl,?_⟩
    change yieldW (w+0) ≤ _+2+_*0+0
    rw [add_zero]
    linarith [yield_step s e.u w e.thick]
  | [b] =>
    refine ⟨[],[b],rfl,?_⟩
    change yieldW (w+duties x e.u b) ≤ watt s e.u _ _ + 2 + _*0+(beamRent e b+0)
    apply (yield_add _ _).trans
    linarith [single_yield h e.u,rent_nonneg e b h.2.1,yield_step s e.u w e.thick]
  | b::c::l =>
    let w' := carry (aimed e w b.post) b.bit c.bit
    have HE : w'=w+duties x e.u b := count_both e w h
    obtain ⟨rfl,h1,h2,h3,h4⟩ := h
    obtain ⟨p,q,H,HH⟩ := write_down e l h4 (fun z hz => hp z (by simp [hz])) w'
    have hD := light_bill e w b c h1 h3 h2 (hp b (by simp)) (hp c (by simp))
    let v := dealer e
    refine ⟨b::c::p,q,by simp [H],?_⟩
    rw [weave,← add_assoc,← HE,tally,tally,subtotal_cons,subtotal_cons]
    change _ ≤ watt b.pre _ _ _ + e.thick*(v.pay (bare w) b+v.pay (v.stepAt (bare w) b) c)+_+_ at hD
    change watt (winds c) e.u w' e.thick ≤ _ at hD
    change yieldW _ ≤ _ + _*(v.pay (bare w) b+(v.pay (v.stepAt (bare w) b) c+v.tally (bare w') p))+_
    change yieldW (w'+_) ≤ _+_ + _*(v.tally _ p)+_ at HH; linarith

lemma ribbon_pref (e : Streak M) {x : Grid M} (l m : Path M) (h : Trip x s l)
    (hp : ∀ b∈l,e.outer b.post) (t : ℝ) (he : 0 ≤ t)
    (h1 : 2*log ((dealer e).heatW (bare 0) (l++m)) ≤ t)
    (h2 : 2*log ((dealer e).heatW sleep (l++m)) ≤ t) :
    yieldW (subtotal (duties x e.u) l) ≤ 20+2*e.thick*t+2*subtotal (beamRent e) l := by
  let a := e.thick; let u := e.u; let r := e.beamRent
  have ha : 0 < a := e.thick_rate.1
  have hi : a ≤ 1 := e.thick_rate.2.1
  let d := dealer e
  rw [←ribbon_eq]
  apply (yield_add _ _).trans
  have HH₁ : yieldW (weave x u l) ≤ 10+a*t+subtotal r l := by
    obtain ⟨p,q,H,hh⟩ := write_down e l h hp 0
    have heq : l++m=p++(q++m) := by rw [H,List.append_assoc]
    have HV : d.tally (bare 0) p ≤ t := by
      apply ((dealer e).edge_score (bare 0) p (q++m)).trans
      rw [← heq]; exact h1
    rw [zero_add] at hh
    change yieldW (weave x u l) ≤ watt s _ 0 a+2+a*(d.tally _ _)+_ at hh
    apply hh.trans
    linarith [watt_idle (trip_head h).1 u a ha.le hi,mul_le_mul_of_nonneg_left HV ha.le]
  change yieldW (weave x u l)+_ ≤ 20+2*a*t+_
  have HH₂ : yieldW (hem x u l) ≤ 10+a*t+subtotal r l := by
    match l with
    | [] =>
      rw [hem,yield_zero,subtotal_nil]
      nlinarith
    | b::l =>
      obtain ⟨H,hb,hk⟩ := h
      obtain ⟨p,q,H,hh⟩ := write_down e l hk (fun i hi => hp i (by simp [hi])) 0
      have heq : (b::l)++m=(b::p)++(q++m) := by simp [H,List.append_assoc]
      have HV : d.tally (bare 0) p ≤ t := by
        have HX : d.tally sleep (b::p) ≤ t := by
          apply ((dealer e).edge_score sleep (b::p) (q++m)).trans
          rw [← heq]; exact h2
        change single 0 b.bit+d.tally (bare 0) p ≤ t at HX
        simpa only [single,mul_zero,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,zero_div,sub_zero,zero_add] using HX
      rw [zero_add] at hh
      rw [hem,subtotal_cons]
      change yieldW (weave x u l) ≤ watt (winds b) _ 0 a+2+a*(d.tally _ _)+_ at hh
      apply hh.trans
      have HH : 0 ≤ r b := rent_nonneg e b hb
      linarith [watt_idle (trip_head hk).1 u a ha.le hi,mul_le_mul_of_nonneg_left HV ha.le]
  change yieldW _ + yieldW (hem x u l) ≤ 20+2*a*t+2*subtotal r l; linarith

def bling (e : Streak M) (l : Path M) :=
    (rain e).heatW () l+(dealer e).heatW (bare 0) l+(dealer e).heatW sleep l
lemma bling_share (e : Streak M) (l : Path M) :
    let a := (rain e).heatW () l
    let b := (dealer e).heatW (bare 0) l
    let c := (dealer e).heatW sleep l
    let z := e.bling l
    1 ≤ z ∧ 1 ≤ a ∧ a ≤ z ∧ 1 ≤ b ∧ b ≤ z ∧ 1 ≤ c ∧ c ≤ z := by
  intro a b c z
  have H1 : 1 ≤ a := heatW_one _ _ _
  have H2 : 1 ≤ b := heatW_one _ _ _
  have H3 : 1 ≤ c := heatW_one _ _ _
  change 1 ≤ a+b+c ∧ 1 ≤ a ∧ a ≤ a+b+c ∧ 1 ≤ b ∧ b ≤ a+b+c ∧ 1 ≤ c ∧ c ≤ a+b+c
  exact ⟨by linarith,H1,by linarith,H2,by linarith,H3,by linarith⟩
lemma bling_mean (e : Streak M) (v : Thread M s) (h : v.Following j J f) :
    (s.here.dice M).Ex (fun x => bling e (v.stream x)) ≤ 6 := by
  simp_rw [bling,Ex_add]; let d := dealer e
  linarith [heat_bound d v h sleep,heat_bound d v h (bare 0),heat_bound (rain e) v h ()]

lemma ribbon_bound (e : Streak M) {x : Grid M} (l m : Path M) (h : Trip x s l)
    (hp : ∀ b∈l,e.outer b.post)
    (t : ℝ) (he : 2*log (e.bling (l++m)) ≤ t) :
    yieldW (subtotal (duties x e.u) l) ≤
      10^14*(fullFax l+(1+fullKills l+flagged e l)/e.thick+e.thick*t) := by
  let a := e.thick; let u := e.u; let r := e.b
  have ha : 0 < a := e.thick_rate.1
  have hi : a ≤ 1 := e.thick_rate.2.1
  have hx := bling_share e (l++m)
  have hR (x : ℝ) (h : 1 ≤ x) (hf : x ≤ e.bling (l++m)) : 2* log x ≤ t :=
    le_trans (mul_le_mul_of_nonneg_left (log_le_log (by linarith) hf) (by norm_num)) he
  obtain ⟨ha₀,ha₁,ha₂,ha₃,ha₄,ha₅,ha₆⟩ := hx
  have HH : 0 ≤ t := le_trans (mul_nonneg (by norm_num) (log_nonneg ha₀)) he
  apply (ribbon_pref e l m h hp t HH (hR _ ha₃ ha₄) (hR _ ha₅ ha₆)).trans
  rw [rent_total]
  let V := showers e l; let K := fullKills l; let E := flagged e l; let J := fullFax l
  have hJ : 0 ≤ J := trip_fax h; have hK : 0 ≤ K := trip_K h; have hE : 0 ≤ E := flagged_pos e h
  have hM := e.cave_whole h hp
  have HE := ((rain e).edge_score () l m).trans (hR _ ha₁ ha₂)
  have hV : V ≤ 2*(4+8*K+4*E+r*J+10^5*r*t) := by
    have HR : 0 < r := e.rate.1
    change V/2 ≤ _-energy s u+8*K+4*E+r*J+10^5*r*_ at hM
    nlinarith [(energy_small (trip_head h).1 u).1]
  have heq : a^2=r := thick_rate e |>.2.2
  change 20+2*a*t+2*(10^6*(J+(K+E+V)/a)) ≤ 10^14*(J+(1+K+E)/a+a*t)
  apply le_of_mul_le_mul_left _ ha
  have HD (x y z : ℝ) : a*(x*(y+z/a))=x*(a*y+z) := by field_simp
  simp_rw [mul_add]
  have HG (x k : ℝ) : a*(x*(k/a))=x*k := by field_simp

  field_simp
  nlinarith [mul_nonneg ha.le HH,show a*a*J ≤ a*J from by exact mul_le_mul_of_nonneg_right (by nlinarith) hJ,
    show a*(a*t)=r*t by rw [← heq]; ring]

end Run.Streak


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
