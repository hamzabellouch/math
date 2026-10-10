import OAI.Analysis.FourierLLogL.Paths.Tilt
import OAI.Analysis.FourierLLogL.Paths.Wager
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


open Desk

namespace Lens

def quest (g : Lens M) : Desk M Unit where
  stake _ _ s := -(g.swing s)/(2000*g.rate)
  stepAt _ _ := ()
def dusk (g : Lens M) (l : Path M) :=
    subtotal (fun i => (g.coin i.post)^2) l

lemma stipend (g : Lens M) {b : Beat M} (h : Ideal b.pre b.post) (hp : 0 < g.rate) :
    let r := g.rate
    (g.coin b.post)^2/2 ≤
      g.hero (winds b)-g.hero b.pre+30*r*killed b+2000*r*((quest g).pay () b) := by
  intro r
  rw [winds,g.hero_walk]
  let x := g.swing b.post; let l := 2000*r
  have hi : 0 < r := hp
  have hh : 0 < l := by unfold l; positivity
  have hD := coin_flow g hp.le h.climb
  have hF := swing_flow g hp.le h.climb
  change x^2 ≤ 900*r*_ at hF
  have hx : l* (g.quest.pay () b) = -curl b.bit*x - x^2/(2*l) := by
    change l* (curl b.bit*(-x/l)-(-x/l)^2/2)=_
    field_simp
  have hE : x^2/(2*l) ≤ g.flow b.post/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have HG : 0 ≤ g.flow b.post := le_trans (sq_nonneg _) hD.1
    unfold l
    nlinarith [mul_nonneg hi.le HG]
  have HW := (abs_le.mp (hero_drain g hi.le h)).2
  change _ ≤ _+curl b.bit*x - g.hero b.pre + 30*r*killed b + l*_
  rw [hx]; change _ ≤ 30*r *_ at HW
  linarith [hD.1]

lemma dusk_tally (g : Lens M) {x : Grid M} {l : Path M} (h : Trip x s l) (hp : 0 < g.rate) :
    g.dusk l /2 ≤ 120*g.rate-g.hero s+30*g.rate*fullKills l + 2000*g.rate*(g.quest.tally () l) := by
  induction l generalizing s with
  | nil =>
    have H := (g.hero_limit hp.le (trip_head h).1).2
    change 0/2 ≤ _-hero g s+_*0+_*0; linarith
  | cons b l ih =>
    obtain ⟨rfl,ha,hb⟩ := h
    have hh := ih hb
    have hi := stipend g ha hp
    change _ ≤ _-g.hero b.pre+_+_ at hi
    change ((g.coin b.post)^2+g.dusk l)/2 ≤ _+ _*(killed b+fullKills l)+_*(g.quest.pay () b+g.quest.tally () l)
    linarith

def ease (g : Lens M) := √g.rate
def shifted (g : Lens M) : Desk M ℝ where
  stake t _ _ := t / g.ease
  stepAt _ b := curl b.bit * g.coin b.post
def enters (c : ℝ) : Path M → ℝ
| [] => 0
| b::_ => curl b.bit*c

lemma last_lag (g : Lens M) {x : Grid M} {l : Path M} (h : Trip x s l)
    (hp : 0 < g.rate) (c : ℝ) :
    let a := g.ease
    enters c l + part g.face (subtotal (frosty x g.focus g.rate) l) ≤
      a*(g.shifted.tally c l)+(g.dusk l+c^2)/(2*a)+10*g.rate := by
  intro a
  have he : 0 < a := Real.sqrt_pos.2 hp
  induction l generalizing s c with
  | nil =>
    change 0+part g.face 0 ≤ _*0 + (0+c^2)/(2*a)+10*g.rate
    rw [part_zero]; have hh : 0 ≤ (0+c^2)/(2*a) := by positivity
    linarith
  | cons b l ih =>
    let k := g.coin b.post; let t := curl b.bit*k
    have HE : a*g.shifted.pay c b = curl b.bit*c-c^2/(2*a) := by
      change a*((curl _)*(c/a)-(c/a)^2/2)=_
      field_simp
    rw [subtotal_cons,part_add]
    rw [frosty,part_mul]
    rw [Desk.tally,mul_add,HE]
    let A := frosty x g.focus g.rate
    change curl b.bit*c+(blow x b*k+part g.face (subtotal A l)) ≤
      curl b.bit*c-c^2/(2*a)+a*g.shifted.tally t l +(k^2+g.dusk l+c^2)/(2*a)+10*g.rate
    rw [add_div]
    cases l with
    | nil =>
      have hi : |blow x b*k| ≤ 10*g.rate := by
        rw [abs_mul,trip_final h,one_mul]; exact (part_bounded _ _).trans (prize_norm hp.le _ _)
      have hh : 0 ≤ (k^2+0)/(2*a) := by positivity
      rw [subtotal_nil,part_zero,tally]
      rw [show g.dusk []=0 from rfl]
      linarith [(abs_le.mp hi).2]
    | cons d l =>
      have hh := ih h.2.2 t
      have hH : enters t (d::l)=blow x b*k := by rw [trip_delay h]; unfold enters t; ring
      have hE : t^2=k^2 := by unfold t; rw [mul_pow,curl_sq,one_mul]
      rw [hH,hE,add_comm (g.dusk _)] at hh; change _+part g.face (subtotal A _) ≤ _ at hh
      linarith

lemma face_fire (g : Lens M) {x : Grid M} (l m : Path M) (h : Trip x s l)
    (hp : 0 < g.rate) (he : g.rate ≤ 1) (t : ℝ)
    (ht : 0 ≤ t)
    (h1 : 2*log (g.quest.heatW () (l++m)) ≤ t) (h2 : 2*log (g.shifted.heatW 0 (l++m)) ≤ t) :
    part g.face (subtotal (frosty x g.focus g.rate) l) ≤ 3000*g.ease*(1+fullKills l+t) := by
  let r := g.rate; let a := g.ease; let K := fullKills l
  let V := g.dusk l
  have HI := last_lag g h hp 0
  have h3 : 0 < a := Real.sqrt_pos.2 hp
  have h4 : a^2=r := Real.sq_sqrt hp.le
  change r ≤ _ at he
  change _ ≤ a*_+(V+0^2)/(2*a)+10*r at HI
  have hx := (g.quest.edge_score () l m).trans h1
  have hx' := (g.shifted.edge_score 0 l m).trans h2
  rw [show enters 0 l=0 by cases l <;> simp [enters]] at HI
  have HH := dusk_tally g h hp
  have hw := g.hero_limit hp.le (trip_head h).1
  have HS : V/(2*a) ≤ a*(120+30*K+2000*t) := by
    apply (div_le_iff₀ (by positivity)).mpr
    have HB : a*(120+30*K+2000*t)*(2*a) = 2*r*(120+30*K+2000*t) := by rw [← h4]; ring
    rw [HB]
    change V/2 ≤ 120*r-hero g s+30*r*K+2000*r*_ at HH
    change 0 < r at hp
    nlinarith [hw.1]
  have h6 : a ≤ 1 := by nlinarith
  have h8 : r ≤ a := by nlinarith
  have HQ : 0 ≤ K := trip_K h
  change _ ≤ 3000*a*(1+K+t)
  rw [show V+0^2=V by ring] at HI
  nlinarith

end Lens

def coldScore (u : Grid M) (b : ℝ) (l : Path M) :=
    1 + ∑ d : Face, let g := Lens.mk u b d; g.quest.heatW () l+g.shifted.heatW 0 l

private lemma cold_share (u : Grid M) (b : ℝ) (l : Path M) (d : Face) :
    let g := Lens.mk u b d; g.quest.heatW () l + g.shifted.heatW 0 l ≤ coldScore u b l := by
  intro g
  unfold coldScore
  rw [add_comm (1:ℝ)]
  apply le_trans _ (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 1))
  apply Finset.single_le_sum (f:=fun d : Face => (Lens.mk u b d).quest.heatW () l+
    (Lens.mk u b d).shifted.heatW 0 l) _ (Finset.mem_univ d)
  intro x hx; apply add_nonneg
  · linarith [(Lens.mk u b x).quest.heatW_one () l]
  · linarith [(Lens.mk u b x).shifted.heatW_one 0 l]

lemma cold_one (u : Grid M) (b : ℝ) (l : Path M) : 1 ≤ coldScore u b l := by
  let g := Lens.mk u b (false,false)
  have H := cold_share u b l (false,false)
  change g.quest.heatW () l + g.shifted.heatW 0 l ≤ _ at H
  linarith [g.shifted.heatW_one 0 l,g.quest.heatW_one () l]

lemma cold_mean (u : Grid M) (b : ℝ) (t : Thread M s) (h : t.Following j J f) :
    (s.here.dice M).Ex (fun x => coldScore u b (t.stream x)) ≤ 20 := by
  unfold coldScore; rw [Ex_add _ (f:=fun _ => _),Ex_const,Ex_finset_sum]
  let U (d : Face) := Lens.mk u b d
  let P := s.here.dice M
  let F (d) := P.Ex fun x => (U d).quest.heatW () (t.stream x)+(U d).shifted.heatW 0 (t.stream x)
  change 1+∑ d,F d ≤ _
  have H (d) : F d ≤ 4 := by
    unfold F; rw [Ex_add]
    have HH : P.Ex (fun x => (U d).quest.heatW () (t.stream x)) ≤ 2 :=
      heat_bound _ t h _
    have HI : P.Ex (fun x => (U d).shifted.heatW 0 (t.stream x)) ≤ 2 :=
      heat_bound _ t h _
    linarith
  have HH : ∑ d,F d ≤ ∑ _d : Face,(4:ℝ) := Finset.sum_le_sum fun i _ => H i
  norm_num [Face] at HH
  linarith

private lemma fire_pref {x : Grid M} (u : Grid M) {b : ℝ} (hb : 0 < b) (hi : b ≤ 1)
    (l m : Path M) (h : Trip x s l) (t : ℝ) (ht : 2*log (coldScore u b (l++m)) ≤ t) :
    ‖subtotal (frosty x u b) l‖ ≤ 6000*√b*(1+fullKills l+t) := by
  let v := subtotal (frosty x u b) l; let a := 3000*√b*(1+fullKills l+t)
  let score := coldScore u b (l++m)
  have H (d : Face) : part d v ≤ a := by
    let g := Lens.mk u b d
    have h1 : 1 ≤ g.shifted.heatW 0 (l++m) := heatW_one _ _ _
    have h2 : 1 ≤ g.quest.heatW () (l++m) := heatW_one _ _ _
    have h3 : g.quest.heatW () (l++m) + g.shifted.heatW 0 (l++m) ≤ score := cold_share _ _ _ d
    have H (x : ℝ) (h : 1 ≤ x) (hh : x ≤ score) : 2*log x ≤ t :=
      le_trans (mul_le_mul_of_nonneg_left (log_le_log (by linarith) hh) (by norm_num)) ht
    apply g.face_fire l m h hb hi
    · exact le_trans (mul_nonneg (by norm_num) (log_nonneg (cold_one _ _ _))) ht
    · exact H _ h2 (by linarith)
    · exact H _ h1 (by linarith)
  have h1 : |v.re| ≤ a := by
    rw [abs_le]
    have He := H (false,true); have Hf := H (false,false); simp only [part,curl,↓reduceIte,
      Bool.false_eq_true,neg_mul,one_mul] at He Hf
    constructor <;> linarith
  have h2 : |v.im| ≤ a := by
    rw [abs_le]
    have He := H (true,true); have Hf := H (true,false); simp only [part,curl,↓reduceIte,
      Bool.false_eq_true,neg_mul,one_mul] at He Hf
    constructor <;> linarith
  change ‖v‖ ≤ _
  unfold a at *; linarith [Complex.norm_le_abs_re_add_abs_im v]

lemma frosty_portion {x : Grid M} (u : Grid M) {b : ℝ} (hb : 0 < b) (hi : b ≤ 1)
    (l r m : Path M) (h : Trip x s (l++r++m)) (t : ℝ)
    (ht : 2*log (coldScore u b (l++r++m)) ≤ t) :
    ‖subtotal (frosty x u b) r‖ ≤ 12000*√b*(1+fullKills (l++r++m)+t) := by
  obtain ⟨ha,w,hc⟩ := trip_cut h
  obtain ⟨hd,v,he⟩ := trip_cut ha
  have H := fire_pref u hb hi _ _ ha t ht
  rw [List.append_assoc] at ht
  have HE := fire_pref u hb hi _ _ hd t ht
  let F := frosty x u b
  rw [show subtotal (frosty x u b) r=subtotal F (l++r)-subtotal F l by rw [subtotal_app]; abel]
  apply (norm_sub_le _ _).trans
  have HH : fullKills (l++r++m)=fullKills l+fullKills r+fullKills m := by simp [fullKills,subtotal_app,add_assoc]
  have HI : fullKills (l++r)=fullKills l+fullKills r := by simp [fullKills,subtotal_app]
  rw [HH]; rw [HI] at H; unfold F
  nlinarith [trip_K hc,trip_K he,sqrt_pos.2 hb]


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
