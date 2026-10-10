import OAI.Analysis.FourierLLogL.Paths.Upkeep
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace Run.Streak

abbrev Tide := Option ℝ
structure Tick where
  alpha : Bool
  tick : Bool
  next : Tide

def idle : Tick := ⟨false,false,none⟩
def going (first meter : Bool) (x : ℝ) : Tick := ⟨first,meter,some x⟩
def rightNow (e : Streak M) (s : Scene M) : Tide → Tick
  | none => if e.innerV s then going true false (fax s) else idle
  | some x => if e.outer s then
      if 1 ≤ x then going false true (fax s) else going false false (x+fax s)
    else idle

def events (e : Streak M) (fresh : Bool) (t : Tide) : Path M → ℝ
  | [] => 0
  | b::l =>
    let k := e.rightNow b.post t
    (if (if fresh then k.alpha else k.tick) then 1 else 0) + events e fresh k.next l

def sumbling (e : Streak M) (t : Tide) : Path M → ℝ
  | [] => 1
  | b::l =>
    let k := e.rightNow b.post t
    (if k.alpha ∨ k.tick then e.bling (b::l) else 0) + sumbling e k.next l

lemma sumbling_one (e : Streak M) (t : Tide) (l : Path M) :
    1 ≤ e.sumbling t l := by
  induction l generalizing t with
  | nil => exact le_rfl
  | cons b l ih =>
    rw [sumbling]; split
    · linarith [(bling_share e (b::l)).1,ih (rightNow e b.post t).next]
    rw [zero_add]; exact ih _

lemma spark_mean (e : Streak M) {s : Scene M} (v : Thread M s) (t : Tide)
    (h : Following j J f v) :
    stats v (e.sumbling t) ≤ 1+6*(stats v (e.events true t)+stats v (e.events false t)) := by
  induction v generalizing t with
  | blank => rw [stats_nil,stats_nil,stats_nil]; change (1:ℝ) ≤ 1+6*(0+0); norm_num
  | ran s q k ih =>
    rw [stats_cons h,stats_cons h,stats_cons h]
    let m := rightNow e q t
    let U := uniform Bool
    let A := m.next
    have hh (b : Bool) :
        stats (k b) (e.sumbling A) ≤ 1+6*(stats (k b) (e.events true A) + stats (k b) (e.events false A)) :=
      ih b A (h.2.2.2.2.2 b)
    have H := U.Ex_mono hh
    rw [Ex_add (f:=fun _ => _),Ex_const, Ex_lmul, Ex_add] at H
    have HH := bling_mean e (ran s q k) h
    change stats (ran s q k) (bling e) ≤ _ at HH
    rw [stats_cons h] at HH
    simp_rw [sumbling,events]
    by_cases h1 : (rightNow e q t).alpha=true <;>
      by_cases h2 : (rightNow e q t).tick=true <;>
      simp only [h1,h2,or_true,true_or,Bool.false_eq_true,false_or,↓reduceIte] <;>
      (try simp_rw [stats_plus _ (f:=fun _ => _),Ex_add _ (f:=fun _ => _)])
    all_goals

      unfold A m U at H
      unfold stats at *
      try simp_rw [Ex_add _ (f:=fun _ => _)]
      simp_rw [Ex_const]
      linarith

def powerOf (t : Tide) := t.getD 0

lemma checkpoints (e : Streak M) (t : Tide) {s : Scene M} {l : Path M}
    {x : Grid M} (h : Trip x s l) (ht : 0 ≤ powerOf t) :
    events e false t l ≤ powerOf t+fullFax l := by
  induction l generalizing s t with
  | nil => change 0 ≤ powerOf t+0; linarith
  | cons b l ih =>
    have HH := (fax_floor h.2.1.climb).1
    have H (t : Tide) (hh : 0 ≤ powerOf t) := ih t h.2.2 hh
    rw [events]
    change (if (rightNow e b.post t).tick then 1 else 0)+_
      ≤ powerOf t+(fax b.post+fullFax l)
    cases t with
    | none =>
      split_ifs with h₁
      all_goals by_cases hx : e.innerV b.post
      all_goals simp only [rightNow,hx,↓reduceIte,idle,going] at h₁ ⊢
      all_goals
        first | contradiction |
          (have hi := H (some (fax b.post)) HH
           simp only [powerOf,Option.getD] at *; linarith) |
          (have hi := H none (by change (0:ℝ) ≤ 0; norm_num)
           simp only [powerOf,Option.getD] at *; linarith)
    | some z =>
      change 0 ≤ z at ht
      by_cases h₁ : e.outer b.post
      · by_cases h₂ : 1 ≤ z
        · have hi := H (some (fax b.post)) HH
          simp only [rightNow,going,h₁,h₂,↓reduceIte,powerOf,Option.getD] at hi ⊢; linarith
        have hi := H (some (z+fax b.post)) (add_nonneg ht HH)
        simp only [rightNow,going,h₁,h₂,↓reduceIte,Bool.false_eq_true,powerOf,Option.getD] at *
        linarith
      · have hi := H none (by change (0:ℝ) ≤ 0; norm_num)
        simp only [powerOf,rightNow,idle,h₁,Bool.false_eq_true,↓reduceIte,Option.getD] at *; linarith

def slackOf (e : Streak M) (s : Scene M) (t : Tide) :=
    if t.isSome then energy s e.u else 128*e.b^2
def breakFare (e : Streak M) (b : Beat M) :=
    shower e.u b.post+8*killed b+4*flag e b.post
def quota (e : Streak M) := 64*e.b^2

lemma slack_nonneg (e : Streak M) (s : Scene M) (h : Fit s) (t : Tide) :
    0 ≤ slackOf e s t := by
  unfold slackOf; split; exact (energy_small h e.u).1; positivity

lemma fare_step (e : Streak M) (s q : Scene M) (h : Ideal s q) (t : Tide) :
    let T := rightNow e q t
    (uniform Bool).Ex (fun b => slackOf e (q.smaller b) T.next)
       + (if T.alpha then e.quota else 0) ≤ slackOf e s t + breakFare e ⟨s,q,false⟩ := by
  intro T
  let v := fun b => energy (q.smaller b) e.u
  let g := shower e.u q
  let K := killed (Thread.Beat.mk s q false)
  let Q := e.b^2
  have he : (v false+v true)/2=energy q e.u+g := wet_average q h.climb e.u
  have hH (b) : 0 ≤ v b ∧ v b ≤ 4 :=
    let H := energy_small (h.climb.child b) e.u
    ⟨H.1,H.2.trans (h.climb.child b).lift⟩
  have hq : 0 ≤ Q := sq_nonneg _
  have hz : 0 ≤ K := Ideal.kill_nonneg (B:=⟨s,q,false⟩) h
  have hG : 0 ≤ g := shower_nonneg h.climb
  have hf := flag_nonneg e q
  have HH : |energy s e.u-energy q e.u| ≤ 8*K := energy_drain (b:=⟨s,q,false⟩) h e.u
  let B := g+8*K+4*flag e q
  change _+(if T.alpha=true then 64*Q else 0) ≤ _+B
  cases t with
  | none =>
    by_cases hp : innerV e q
    · rw [show T=going true false (fax q) from ite_eq_left hp, fair_av]
      change _ + _ ≤ 128*Q+B
      simp only [slackOf,going,Option.isSome_some,↓reduceIte]
      change (v false+v true)/2+64*Q ≤ _
      rcases hp with h1|h1
      · unfold B
        rw [show flag e q=1 from ite_eq_left h1]; linarith [(hH false).2,(hH true).2]
      · have hx (b) : v b ≤ 64*Q := h1 b
        unfold B; linarith [hx false,hx true]
    · rw [show T=idle from ite_eq_right hp]
      rw [show (uniform Bool).Ex (fun b => slackOf e (q.smaller b) idle.next) =128*Q from Ex_const (uniform Bool) (128*Q)]
      simp only [idle,Bool.false_eq_true,↓reduceIte]
      change _ ≤ 128*Q+B; unfold B; linarith
  | some x =>
    by_cases hp : outer e q
    · have HE : T.next.isSome=true ∧ T.alpha=false := by
        simp only [T,rightNow,ite_eq_left hp]; split <;> simp [going]
      rw [fair_av]
      simp only [slackOf,HE.1,HE.2,Bool.false_eq_true,Option.isSome_some,↓reduceIte]
      change (v false+v true)/2+_ ≤ _+B; unfold B
      linarith [(abs_le.mp HH).1]
    · rw [show T=idle from ite_eq_right hp]
      rw [show (uniform Bool).Ex (fun b => slackOf e (q.smaller b) idle.next) =128*Q from Ex_const (uniform Bool) (128*Q)]
      simp only [idle,Bool.false_eq_true,↓reduceIte]
      have hi : ¬ ∀ b, v b ≤ 256*Q := fun HH => hp (Or.inr HH)
      push Not at hi
      obtain ⟨b,hb⟩ := hi
      change _ ≤ energy s e.u+B; unfold B
      cases b <;> linarith [(hH true).1,(hH false).1,(abs_le.mp HH).1]

lemma fare_total (e : Streak M) {s : Scene M} (v : Thread M s) (t : Tide)
    (h : Following j J f v) (hp : Fit s) :
    e.quota*stats v (e.events true t) ≤ slackOf e s t+stats v (subtotal (breakFare e)) := by
  induction v generalizing t with
  | blank s =>
    rw [stats_nil,stats_nil]
    change _*0 ≤ _+0
    linarith [slack_nonneg e s hp t]
  | ran s q k ih =>
    have HH := jump_ideal h hp.lift
    rw [stats_cons h,stats_cons h]
    let T := rightNow e q t
    let A := if T.alpha=true then (1:ℝ) else 0
    let B := breakFare e (Thread.Beat.mk s q false)
    change e.quota*_ ≤ _+_
    have HF (b : Bool) : breakFare e ⟨s,q,b⟩=B := rfl
    simp_rw [events,subtotal_cons,HF]
    have HE (b : Bool) := ih b T.next (h.2.2.2.2.2 b) (HH.climb.child _)
    have HI := (uniform Bool).Ex_mono HE
    have HC := e.fare_step s q HH t
    have H0 : e.quota*A=if T.alpha=true then e.quota else 0 := by unfold A; split <;> ring
    unfold stats at *
    simp_rw [Ex_add _ (f:=fun _ => _),Ex_const]
    rw [Ex_add,Ex_lmul] at HI
    change _+(if T.alpha then _ else _) ≤ _+B at HC
    rw [← H0] at HC
    unfold A T at *
    simp only [↓reduceIte]
    linarith

lemma expected_bling :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s q : Scene M,
      ∀ f : Grid M → ℝ, ∀ k, Following j J f (ran s q k) → Fit s → q.live=true →
      (∀ x, f x ≤ exp (height j)) →
      ∀ e : Streak M, e.i ≤ mainIx j →
        stats (ran s q k) (e.sumbling none) ≤ 10^30*(height j)^3 := by
  filter_upwards [sum_budget_run,hpoly 12800 32] with j hj hs M J s q f k h hh hq hF e he
  let v := ran s q k
  obtain ⟨h1,h2,h3,h4⟩ := hj M J f s q k h hh hq hF e
  let x := stats v (e.events true none); let y := stats v (e.events false none)
  let b := e.b^2; let d := height j
  have hi : 1 ≤ d := by nlinarith [H_ge j,show (1:ℝ) ≤ Thermal.H j^32 from one_le_pow₀ (H_ge j)]
  have HE : 1 ≤ d*b := by
    have hh1 := (main_bounds j (show e.i ≤ testIx j by unfold testIx; omega)).1
    have hE := Thermal.H_pos j
    rw [div_le_iff₀ (by positivity)] at hh1
    change 1/6400 ≤ b/100*Thermal.H j^32 at hh1
    have HB : 0 ≤ b := sq_nonneg _
    change _ ≤ d at hs
    nlinarith
  have hb : 0 < b := pow_pos e.rate.1 _; have hh' : b ≤ 1 := pow_le_one₀ e.rate.1.le e.rate.2
  have HR := spark_mean e v none h
  apply HR.trans
  change 1+6*(x+y) ≤ 10^30*d^3
  have HV : y ≤ stats v fullFax := by
    apply Ex_mono_mem
    intro i hi
    have hL : i∈s.here.block M := (dice_positive hh.ready.1).1 hi
    have HE := checkpoints e none (trip_stream v h hh hL)
      (by change (0:ℝ) ≤ 0; norm_num)
    rw [show powerOf none=0 from rfl, zero_add] at HE; exact HE
  let z := stats v e.flagged
  change stats v _ ≤ _ at h1 h2 h3
  change b*z ≤ 10^6*d at h4
  have hz : z ≤ 10^6*d^2 := by
    by_contra! HH
    nlinarith [mul_le_mul_of_nonneg_left HE (show 0 ≤ 10^6*d by positivity)]
  have hh0 := fare_total e v none h hh
  have hx : stats v (subtotal (breakFare e)) =
      stats v (e.showers) + 8*stats v fullKills + 4*z := by
    have HI (l : Path M) : subtotal (breakFare e) l = e.showers l+8*fullKills l+4*e.flagged l := by
      induction l with
      | nil => change (0:ℝ)=0+_*0+_*0; ring
      | cons b l ih =>
        rw [subtotal_cons,ih]
        change shower e.u b.post+8*killed b+4*flag e b.post+_=
          shower e.u b.post+e.showers l+8*(killed b+fullKills l)+4*(flag e b.post+e.flagged l)
        ring
    unfold z stats
    simp_rw [HI,Ex_add,Ex_lmul]
  rw [hx] at hh0
  change 64*b*x ≤ 128*b+_ at hh0
  have HC : 64*b*x ≤ 10^7*d^2 := by nlinarith
  have HQ : x ≤ 10^7*d^3 := by
    by_contra! hx
    nlinarith [mul_le_mul_of_nonneg_left HE (show 0 ≤ 10^7*d^2 by positivity)]
  change stats v fullFax ≤ 10^26*d at h3
  nlinarith

end Run.Streak


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
