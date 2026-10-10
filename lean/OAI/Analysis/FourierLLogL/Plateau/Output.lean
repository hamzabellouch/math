import OAI.Analysis.FourierLLogL.Plateau.Thread

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Thread
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse
variable {M J j : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical

def other (s q : Scene M) := {s with wage := s.wage-q.wage}
def keep (s q : Scene M) : TossUp s where
  dst := fun b => if b then q else other s q
  coord := fun x => decide (0 < q.wage x)

lemma keep_here (h : Less s q) (b) : ((keep s q).dst b).here=s.here := by cases b; rfl; exact h.here

lemma other_ok (h : Less s q) (he : ReadyAt s) : ReadyAt (other s q) :=
  ⟨he.1,sub_nonneg.mpr (h.antitone he.2)⟩

lemma keep_true (h : Less s q) (hs : ReadyAt s) (ht : ReadyAt q) (hm : 0 < s.mass) :
    (keep s q).snip.TrueLaw := by
  refine ⟨weight_pos.mpr hm,?_⟩
  intro b x
  have HR := actor_weight (s:=s) hs.1 hs.2 x
  have HQ := actor_weight (s:=q) ht.1 ht.2 x
  have he := other_ok h hs
  have HE := actor_weight (s:=other s q) he.1 he.2 x
  rw [show (keep s q).snip.src=s from rfl,HR]
  cases b
  case true =>
    change q.weight* q.actor x = _
    rw [HQ]; unfold insideW; rw [h.here]
    by_cases HH : 0 < q.wage x
    · have hx := (h.coins x).resolve_right HH.ne'
      simp only [TossUp.snip,keep,decide_eq_true HH,ite_true]; rw [hx]
    have hx : q.wage x = 0 := by linarith [show 0 ≤ q.wage x from ht.2 x]
    simp only [TossUp.snip,keep,hx]; simp
  case false =>
    change (other s q).weight*(other s q).actor x = _
    rw [HE]; unfold insideW
    by_cases HH : 0 < q.wage x
    · have hx := (h.coins x).resolve_right HH.ne'
      simp only [TossUp.snip,keep,other,decide_eq_true HH,Pi.sub_apply]; rw [hx]; simp
    have hx : q.wage x=0 := by linarith [show 0 ≤ q.wage x from ht.2 x]
    simp only [TossUp.snip,keep,other,Pi.sub_apply,hx,sub_zero]; simp

/-- law before membership pays q proportionally -/
lemma kept_mass (h : Less s q) (hs : ReadyAt s) (ht : ReadyAt q) (hm : 0 < s.mass) :
    q.mass = (keep s q).snip.probs true*s.mass := by
  have H := balance (keep_true h hs ht hm) true
  apply mul_left_cancel₀ s.here.len_pos.ne'
  change q.here.len*q.mass=s.here.len*s.mass*_ at H
  rw [h.here] at H; rw [H]; ring

lemma pre_pos {t : ∀ b, Thread M (q.smaller b)}
    (h : Following j J f (.ran s q t)) : 0 < s.mass :=
  lt_of_lt_of_le h.2.2.2.1.1.2.2 (h.2.1.1.mass_le h.1.positive h.1.within)

def splice (s q : Scene M) (k : ∀ b, Wire M (q.smaller b)) :=
    Wire.spot s (keep s q) fun b => match b with
    | false => extra (other s q) (M-s.here.lev)
    | true => link q true k

def unfoldW {s : Scene M} (t : Thread M s) : Wire M s :=
    match t with
    | blank s => extra s (M-s.here.lev)
    | ran s q k => splice s q fun b => unfoldW (k b)

lemma splice_valid (t : Thread M s) (h : Following j J f t) : (unfoldW t).Valid true := by
  have H (s : Scene M) (h : Safe s j J f) : ReadyAt s := ⟨h.within,h.positive⟩
  induction t with
  | blank =>
    exact extra_ok _ _ true (H _ h) (Nat.add_sub_of_le (H _ h).1.2)
  | ran s q k ih =>
    obtain ⟨ha,hb,hc,hd,he,hk⟩ := h
    have hx : q.here.lev < M := (rooted _ (hk false)).within.2
    have hU := other_ok hb.1 (H _ ha)
    refine ⟨H _ ha,keep_here hb.1,keep_true hb.1 (H _ ha) (H _ hc),?_⟩
    intro b; cases b
    · exact extra_ok _ _ true hU (Nat.add_sub_of_le (H _ ha).1.2)
    exact ⟨H _ hc,hx,id,fun b => ih _ (hk b)⟩

/-- `massLift` true-recursion accumulator pays post costs selected at Jump nodes -/
def massLift {s : Scene M} (t : Thread M s) (f : Scene M → Scene M → ℝ) : ℝ := match t with
| .blank _ => 0
| .ran s q k =>
    (keep s q).snip.probs true*(f s q+ (step q).probs.Ex (fun b => massLift (k b) f))

private lemma die_average (Q : Law Bool) (f : Bool → ℝ) : Q.Ex f = Q true*f true + Q false*f false := by
  simp [Ex]

lemma output_split (q : Scene M) (hv : q.here.valid) (hh : q.here.lev < M)
    (hp : 0 ≤ q.wage) (hm : 0 < q.mass) (f : Bool → ℝ) :
    q.mass * (step q).probs.Ex f = (uniform Bool).Ex fun b => (q.smaller b).mass*f b := by
  have H := step_true hv hh hp hm
  rw [die_average,die_average]
  simp only [step_mass H,uniform_apply,Fintype.card_bool,Nat.cast_ofNat]
  ring

lemma output_rule (t : Thread M s) (g : Scene M → Scene M → ℝ) (h : Following j J f t) :
    s.mass * t.massLift g =
      t.fee fun b => b.post.mass*g b.pre b.post := by
  classical
  induction t with
  | blank => simp [fee,Thread.massLift,stream,Ex_const]
  | ran s q k ih =>
    rw [fee_ran k h]
    obtain ⟨ha,hb,hc,hd,he,hk⟩ := h
    have hm' := hd.1.2.2
    have hM : 0 < s.mass := hm'.trans_le (hb.1.mass_le ha.positive ha.within)
    have hm := kept_mass hb.1 ⟨ha.within,ha.positive⟩ ⟨hc.within,hc.positive⟩ hM
    have Hi : q.here.lev < M := (rooted _ (hk false)).within.2
    have H := output_split q hc.within.1 Hi hc.positive hm' fun b => (k b).massLift g
    rw [Thread.massLift,←mul_assoc,mul_comm s.mass,← hm,mul_add,H]
    have hh (b : Bool) := ih b (hk b)
    simp only [hh,Ex_add (uniform Bool) (f:=fun _ => q.mass*g s q),Ex_const]

lemma spliced_cost (p : Policy M) (b : Bool) (t : Thread M s) (h : Following j J f t)
    (hm : 0 < s.mass) :
    (unfoldW t).expenditure (toll p b)=
      t.massLift fun _ q => q.norm/q.mass * surcharge q b (p q) := by
  induction t with
  | blank s =>
    exact extra_bill _ _ _ (fun i hi => by simp [toll,hi]) (Valid.atSrc (splice_valid _ h))
      hm (Nat.add_sub_of_le (Valid.atSrc (splice_valid _ h)).1.2)
  | ran s q k ih =>
    obtain ⟨ha,hb,hc,hd,he,hk⟩ := h
    let S := keep s q
    let P := S.snip.probs
    let l (b : Bool) := unfoldW (k b)
    have hs : ReadyAt s := ⟨ha.within,ha.positive⟩
    have ht := keep_true hb.1 hs (show ReadyAt q from ⟨hc.within,hc.positive⟩) hm
    let v := S.snip
    unfold unfoldW splice; rw [fee_spot (keep s q) _ _ ht]
    have hp : q.here.lev < M := (rooted _ (hk false)).within.2
    have hf := step_true hc.within.1 hp hc.positive hd.1.2.2
    let g := fun (s q : Scene M) => q.norm/q.mass * surcharge q b (p q)
    have H : expenditure (link q true l) (toll p b) =
        g s q+(step q).probs.Ex fun b => (k b).massLift g := by
      rw [fee_link _ _ _ hf,Ex_add]
      have hh := hd.2.2
      simp only [toll,true_and, ite_eq_left hh,Ex_const]
      congr 1
      apply Ex_congr_mem
      intro i hi
      exact ih i (hk _) ((true_mass hf).mp hi)
    rw [die_average]
    let L := expenditure (extra (other s q) (M-s.here.lev)) (toll p b)
    change P true * expenditure (link q true l) (toll p b) + P false*L = _
    rw [H]
    have HX : P false*L=0 := by
      rcases eq_or_lt_of_le (P.nonneg false) with hi|hi; rw [←hi,zero_mul]
      have He : L=0 := extra_bill _ _ _ (fun i hi => by simp [toll,hi]) (other_ok hb.1 hs)
        ((true_mass ht).mp hi) (Nat.add_sub_of_le ha.within.2)
      rw [He,mul_zero]
    rw [HX,add_zero]
    rfl

lemma surcharge_wire (p : Policy M) (b : Bool) (t : Thread M s) (h : Following j J f t)
    (hm : 0 < s.mass) (hp : 0 < s.norm) :
    t.fee (fun i => surcharge i.post b (p i.post)) =
      s.mass / s.norm * (unfoldW t).expenditure (toll p b) := by
  rw [spliced_cost _ _ _ h hm]
  apply mul_left_cancel₀ hp.ne'
  let g (i : Beat M) := surcharge i.post b (p i.post)
  let F (x y : Scene M) := y.norm/y.mass * surcharge y b (p y)
  have H (s : Scene M) (t : Thread M s) (h : Following j J f t) :
      s.norm*t.fee g = t.fee fun i => i.post.mass*F i.pre i.post := by

    induction t with
    | blank => simp [fee,stream,Ex_const]
    | ran s q k ih =>
      rw [fee_ran k h,fee_ran k h,← Ex_lmul]
      obtain ⟨ha,hb,hc,hd,he,hk⟩ := h
      have Hq := hd.1.2.2
      congr 1; funext i; rw [mul_add]
      rw [← hb.1.flat]
      have HE := ih i (hk i)
      change q.norm*g _+ (q.smaller i).norm*_=_
      rw [HE]
      dsimp only [g,F]
      rw [show q.mass*(q.norm/q.mass* surcharge q b (p q))= q.norm * surcharge q b (p q) by field_simp]
  rw [H _ t h,← output_rule t _ h]
  change s.mass*t.massLift F = s.norm*(s.mass/s.norm*t.massLift F)
  generalize massLift t F = x
  field_simp

end FourierLLogL.Dyadic.Procedure.Thread

end OAI
