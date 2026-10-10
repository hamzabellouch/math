import OAI.Analysis.FourierLLogL.Edges.Charge

/-! # Full extensions and their bill -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Wire
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Pulse
variable {M J j : ℕ} {s : Scene M}
open scoped Classical

/-- Additional unlabelled steps after exit, continuing with a piece frozen. -/
def extra (s : Scene M) : ℕ → Wire M s
  | 0 => term s
  | n+1 => link s false fun b => extra (s.smaller b) n

lemma extra_ok (s : Scene M) (n : ℕ) (a : Bool) (h : ReadyAt s) (hn : s.here.lev+n=M) :
    Valid (extra s n) a := by
  induction n generalizing s a with
  | zero => exact ⟨h,hn⟩
  | succ n ih =>
    have hp : s.here.lev < M := by omega
    refine ⟨h,hp,fun he => False.elim (by simp at he),fun b => ih _ _ ?_ ?_⟩
    · exact ⟨child_ok _ h.1.1 hp b,h.2⟩
    have hh := child_depth s.here b
    change (s.here.child b).lev+n=M; omega

/-- Total entropy cost of non-spatial branching. -/
def spotDebt {s : Scene M} (t : Wire M s) : ℝ := match t with
| .stay _ _ k => k.spotDebt
| .spot _ u k =>
    u.snip.probs.entropy + u.snip.probs.Ex (fun b => (k b).spotDebt)
| .link s _ k => (step s).probs.Ex (fun b => (k b).spotDebt)
| .term _ => 0

lemma extraDebt (s : Scene M) (n : ℕ) : spotDebt (extra s n) = 0 := by
  induction n generalizing s with
  | zero => simp [extra,spotDebt]
  | succ n ih => simp [extra,spotDebt,ih,Ex_const]

lemma due_all (t : Wire M s) (a : Bool) (h : Valid t a) (hm : 0 < s.mass) :
    t.expenditure (due 0) ≤ levels s - s.actor.entropy + t.spotDebt := by
  let unit := fun _ : Grid M => uniform Unit
  have h1 (v : Fork M) (ht : v.TrueLaw) :
      v.probs.Ex (fun b => (v.dst b).actor.entropy) =
        v.src.actor.entropy - v.probs.entropy := by
    have he := conditioned_balance unit v ht
    have hx : sideH v unit = v.probs.entropy := by
      let P := v.src.actor.tensorP (uniform Unit)
      let q := fun i : Grid M × Unit => v.bit i.1
      have HS : P.send q = v.probs := by
        have HH := P.send_send Prod.fst v.bit
        rw [send_fst_tensorP] at HH; exact HH.symm
      have hh : (Prod.snd : Grid M × Unit → Unit)=fun _ => () := rfl
      change P.Hcond q Prod.snd=_
      rw [Hcond_right_partition (Z:=fun _ => ()) _ _ (fun i j => by simp)]
      rw [Hcond_constant, Law.H, HS]
    simp only [unit, privateH_const] at he
    unfold unit at hx; linarith
  induction t generalizing a with
  | term =>
    simp only [spotDebt,expenditure,read,List.map_nil,List.sum_nil,Ex_const]
    have hx := cap_entropy _ h.1.1 h.1.2 hm
    linarith
  | stay s v k ih =>
    rw [fee_stay]
    cases v <;> exact ih _ h.2 hm
  | spot s u k ih =>
    obtain ⟨hs,hS,hv,h⟩ := h
    let v := u.snip
    have hb := hv hm
    rw [fee_spot _ _ _ hb,spotDebt]
    have Hx (b : Bool) (hx : 0 < v.probs b) := ih b _ (h _) ((true_mass hb).mp hx)
    have HH := v.probs.Ex_mono_mem Hx
    have hl (b) : levels (u.dst b)=levels s := by unfold levels; rw [hS]
    rw [Ex_add,Ex_sub] at HH
    simp_rw [hl,Ex_const] at HH
    have h1 := h1 v hb
    change v.probs.Ex (fun b => (u.dst b).actor.entropy) =s.actor.entropy-v.probs.entropy at h1
    unfold v at *; linarith
  | link s v k ih =>
    obtain ⟨hs,hS,hv,h⟩ := h
    let U := step s
    have hb := step_true hs.1.1 hS hs.2 hm
    rw [fee_link v k _ hb,spotDebt]
    have Hx (b : Bool) (hx : 0 < U.probs b) := ih b _ (h _) ((true_mass hb).mp hx)
    have Hh := U.probs.Ex_mono_mem Hx
    simp_rw [due,true_or, ite_true]
    rw [Ex_add]
    simp_rw [signal,Ex_const]
    rw [Ex_add,Ex_sub] at Hh
    simp_rw [levels_child _ hS,Ex_const] at Hh
    have hh := h1 U hb
    change U.probs.Ex (fun b => (s.smaller b).actor.entropy)=s.actor.entropy-U.probs.entropy at hh
    unfold pitch; unfold U at *
    linarith

def Turn.up {s : Scene M} (u : Update j M s.here) : TossUp s := ⟨(toss s u).bit,(toss s u).dst⟩
lemma fork_up (u : Update j M s.here) : (Turn.up u).snip = toss s u := rfl

/-- Every input experiment extended to full spatial resolution -/
def tape {s : Scene M} (t : Road j M s) : Wire M s := match t with
| .finish s _ => extra s (M-s.here.lev)
| .push s v k => stay s v (tape k)
| .fork s v k =>
    match v with
    | .ask u => spot s (Turn.up u) fun b => tape (k b)
    | .move => link s true fun b => tape (k b)

lemma tape_ok (t : Road j M s) {f : Grid M → ℝ} (h : Trusted J f t) :
    (tape t).Valid true := by
  have he (s : Scene M) (h : s.Safe j J f) : ReadyAt s := ⟨h.within,h.positive⟩
  induction t with
  | finish =>
    exact extra_ok _ _ _ (he _ h.1) (by rw [Nat.add_sub_of_le h.1.within.2])
  | push s v k ih => exact ⟨he _ h.1,ih h.2.2.2⟩
  | fork s v k ih =>
    have H := branchTrusted h
    obtain ⟨hs,hb,hv,h⟩ := h
    cases v with
    | ask u => exact ⟨he _ hs,fun b => by cases b <;> rfl,fun _ => H,fun b => ih b (h _)⟩
    | move => exact ⟨he _ hs,(rootSafe (h false)).within.2,id,fun b => ih b (h _)⟩

lemma debt_like (t : Road j M s) {f : Grid M → ℝ} (h : Trusted J f t) (hm : 0 < s.mass) :
    (tape t).spotDebt = t.flatFee memFee := by
  induction t with
  | finish s b => rw [flat_finish]; exact extraDebt _ _
  | push s v k ih =>
    rw [flat_push]; simp only [memFee,winFee,failFee,zero_add]; apply ih h.2.2.2
    rw [pace_mass]; exact hm
  | fork s v k ih =>
    have hh := flat_fork v k h memFee
    have H := branchTrusted h
    have ht : v.fork.probs.Ex (fun b => (tape (k b)).spotDebt) =
        v.fork.probs.Ex (fun b => (k b).flatFee memFee) :=
        Ex_congr_mem _ fun b hb => ih b (h.2.2.2 b) ((true_mass H).mp hb)
    rw [hh,Ex_add,← ht]
    cases v with
    | move => simp [tape,spotDebt,memFee,winFee,failFee,Turn.fork,Ex_const]; rfl
    | ask u =>
      let P := (toss s u).probs; let v : Procedure.Turn j s := .ask u
      have HE : P.Ex (fun b => memFee (.march s v b))=P.entropy := by
        unfold entropy crossE; congr 1; funext b; cases b <;> simp [memFee,winFee,failFee,surprise,v] <;> rfl
      change P.entropy + P.Ex _ = P.Ex (fun b => memFee (.march s v b))+P.Ex _
      rw [HE]; rfl


lemma extra_bill (s : Scene M) (n : ℕ) (f : Pulse M → ℝ) (h : ∀ e : Pulse M, e.active=false → f e=0)
    (hs : ReadyAt s) (_hm : 0 < s.mass) (hn : s.here.lev+n = M) :
    expenditure (extra s n) f = 0 := by
  let t := extra s n
  unfold expenditure
  have he (x : Grid M) :
      ((t.read x).map f).sum=0 := by
    have h1 := faded _ (fades _ (extra_ok s n false hs hn) x)
    apply List.sum_eq_zero
    intro i hi; obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi; exact h _ (h1 _ hj)
  change _ = _
  change s.actor.Ex (fun x => _) = _
  simp_rw [show (fun x : Grid M => ((read (extra s n) x).map f).sum)=(fun _ => 0) from funext he]
  rw [Ex_const]

lemma active_charge (F : Pulse M → ℝ) (hF : ∀ i : Pulse M, i.active=false → F i=0)
    (g : Event j M → ℝ) (ha : ∀ s v, g (Event.pace s v)=0)
    (hb : ∀ (s : Scene M) (u : Update j M s.here) b, g (.march s (.ask u) b)=0)
    (hg : ∀ s, 0 < s.mass →
      (step s).probs.Ex (fun b => g (.march s .move b)) =
        (step s).probs.Ex (fun b => F ⟨s,true,b⟩))
    (t : Road j M s) {f : Grid M → ℝ} (h : Trusted J f t) (hm : 0 < s.mass) :
    (tape t).expenditure F=t.flatFee g := by
  induction t with
  | finish =>
    rw [flat_finish]
    exact extra_bill _ _ F hF (Valid.atSrc (tape_ok _ h)) hm (by rw [Nat.add_sub_of_le h.1.within.2])
  | push s v k ih =>
    rw [flat_push,ha,zero_add]
    rw [tape,fee_stay]; exact ih h.2.2.2 (by rw [pace_mass]; exact hm)
  | fork s v k ih =>
    have ht := branchTrusted h
    rw [flat_fork _ _ h,Ex_add]
    have HH : v.fork.probs.Ex (fun b => expenditure (tape (k b)) F) =
        v.fork.probs.Ex fun b => (k b).flatFee g :=
      Ex_congr_mem _ fun i hi => ih i (h.2.2.2 i) ((true_mass ht).mp hi)
    cases v with
    | ask u =>
      change expenditure (.spot s (Turn.up u) _) F = _
      rw [fee_spot (Turn.up u) _ _ ht]
      simp_rw [hb,Ex_const,zero_add]
      exact HH
    | move =>
      change expenditure (.link s true _) F =
        (step s).probs.Ex (fun b => g (.march s .move b))+ _
      rw [fee_link _ _ _ ht,Ex_add,hg s hm]
      congr 1

end FourierLLogL.Dyadic.Procedure.Wire

end OAI
