import OAI.Analysis.FourierLLogL.Capture.Criterion
/-! # Entropy relative to the adaptive product -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Capture
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread

variable {M : ℕ} {s q : Scene M}
open scoped Classical

abbrev ProductRef (M : ℕ) := Grid M → Grid M → ℝ
def normQ (s : Scene M) (f : ProductRef M) (z : Grid M) :=
    (s.here.dice M).Ex (f z)

lemma normQ_pos (s : Scene M) (f : ProductRef M) (h : ∀ i j, 0 < f i j) (z) :
    0 < normQ s f z := by
  let Q := s.here.dice M
  obtain ⟨i,hi,he⟩ := Q.exists_le_Ex (f z)
  exact lt_of_lt_of_le (h z i) he

def flex (s : Scene M) (main : Bool) (Q : ProductRef M) :=
    deficit s (channel (optic s main)) +
      (tracker s main).Ex (fun i => log (normQ s Q i.2)-log (Q i.2 i.1))

lemma flex_nonneg (s : Scene M) (h : ReadyAt s) (hm : 0 < s.mass)
    (main : Bool) (f : ProductRef M) (hP : ∀ z y, 0 < f z y) :
    0 ≤ flex s main f := by
  let A := optic s main
  let k := channel A
  let Q := s.actor.withNext k
  let P := s.here.dice M
  have hh (z : Grid M) : 0 < ∑ i, P i * f z i := normQ_pos s _ hP z
  let Hq (z : Grid M) : Law (Grid M) := proportional (fun i => P i*f z i)
    (fun i => mul_nonneg (P.nonneg _) (hP _ _).le) (hh z)
  have hz (i z : Grid M) : Hq z i = P i*f z i / normQ s f z := rfl
  have HV (x : Grid M × Grid M) (hx : 0 < Q x) : 0 < P x.1 := by
    apply (dice_positive h.1).mpr
    apply piece_support h.1 (actor_def h.1 h.2 hm)
    exact pos_of_mul_pos_left hx ((k _).nonneg _)
  have hi := Hcond_compare Q Prod.fst Prod.snd Hq (fun i hi => by
    rw [hz]; exact div_pos (mul_pos (HV i hi) (hP _ _)) (normQ_pos s _ hP _))
  have he (i) (hx : 0 < Q i) :
      -log (Hq i.2 i.1) = levels s+(log (normQ s f i.2)-log (f i.2 i.1)) := by
    rw [hz,Real.log_div (mul_pos (HV i hx) (hP _ _)).ne' (normQ_pos s _ hP _).ne',
        Real.log_mul (HV i hx).ne' (hP _ _).ne']
    have HE := (dice_positive h.1).mp (HV i hx)
    unfold levels P
    rw [dice_apply h.1,ite_eq_left HE,Real.log_mul (side_pos _).ne'
      (inv_pos.mpr s.here.len_pos).ne']
    unfold len; simp_rw [side_pow_two,log_inv,log_pow]
    rw [Nat.cast_sub h.1.2]
    ring
  rw [Ex_congr_mem _ he, Ex_add (f:=fun _ => levels s), Ex_const] at hi
  change 0 ≤ levels s -Q.Hcond Prod.fst Prod.snd + Q.Ex _
  linarith

lemma flex_one (s : Scene M) (main : Bool) :
    flex s main (fun _ _ => 1) = deficit s (channel (optic s main)) := by
  simp_rw [flex,normQ,Ex_const,log_one,sub_zero,add_zero]


lemma track_shift {s : Scene M} (main : Bool) {v : Fork M} (he : v.src = s)
    (h : v.TrueLaw) (k : ∀ i, optic (v.dst i) main = optic s main)
    (g : Bool → Grid M × Grid M → ℝ) :
    v.probs.Ex (fun i => (tracker (v.dst i) main).Ex (g i)) =
    (tracker s main).Ex (fun x => g (v.bit x.1) x) := by
  subst s
  unfold tracker
  simp_rw [k,Ex_withNext]
  exact expect_bit h (fun i x => (channel _ x).Ex (fun y => g i (x,y)))

lemma flex_keep (main : Bool) {s q : Scene M} (h : Less s q) (hh : ReadyAt s)
    (hp : ReadyAt q) (hm : 0 < s.mass)
    (f : ProductRef M) (hF : ∀ i j, 0 < f i j) :
    let P := (keep s q).snip.probs
    P true * flex q main f ≤ flex s main f + P.entropy := by
  intro P
  let v := (keep s q).snip
  have he := keep_true h hh hp hm
  let A := optic s main; let k := channel A
  have hX (i : Bool) : optic (v.dst i) main = A := by
    cases i
    · rfl
    change optic q main=optic s main; simp [optic,h.fund]
  have hi (i) : (v.dst i).here=s.here := keep_here h _
  let Z (i : Grid M × Grid M) := log (normQ s f i.2)-log (f i.2 i.1)
  have hv : P.Ex (fun i => flex (v.dst i) main f) ≤ flex s main f + P.entropy := by
    have hi' := track_shift main (v:=v) rfl he hX (fun _ => Z)
    have heq (i z) : normQ (v.dst i) f z = normQ s f z := by unfold normQ; rw [hi]
    have hE' : P.Ex (fun i => deficit (v.dst i) k) ≤ deficit s k + P.entropy := by
      have he := conditioned_balance k v he
      unfold deficit; rw [Ex_sub]; have hz (b) : levels (v.dst b)=levels s := by unfold levels; rw [hi]
      simp_rw [hz,Ex_const]
      have HE := old_entropy_cost v k
      change _+_= s.actor.privateH k at he
      unfold P v at *
      linarith
    have hF (i) : flex (v.dst i) main f =
        deficit (v.dst i) k + (tracker (v.dst i) main).Ex Z := by
      unfold flex; simp_rw [heq,hX]; rfl
    simp_rw [hF,Ex_add]
    change P.Ex _ + v.probs.Ex _ ≤ deficit s k + (tracker s main).Ex Z + _
    rw [hi']
    change _ + (tracker s main).Ex Z ≤ _
    linarith
  rw [Ex,Fintype.sum_bool] at hv
  have hE : 0 ≤ P false * flex (v.dst false) main f := by
    rcases eq_or_lt_of_le (P.nonneg false) with H|H; rw [← H,zero_mul]
    exact mul_nonneg H.le <| flex_nonneg _ (other_ok h hh)
      ((true_mass he).mp H) _ _ hF
  exact (le_add_of_nonneg_right hE).trans hv

lemma flex_down (main : Bool) (s : Scene M) (hp : s.here.valid) (hh : s.here.lev < M)
    (ha : 0 ≤ s.wage) (hm : 0 < s.mass)
    (f : ProductRef M) (hF : ∀ i j, 0 < f i j) :
    (step s).probs.Ex (fun i => flex (s.smaller i) main f) ≤ flex s main f := by
  let P := tracker s main; let v := step s
  let k := channel (optic s main)
  have hx (i : Bool) : channel (optic (s.smaller i) main) = k := rfl
  let g (x : Grid M × Grid M) := v.bit x.1
  have H := step_true hp hh ha hm
  let q (z : Grid M) (b : Bool) : ℝ := normQ (s.smaller b) f z/(2*normQ s f z)
  have HQ (z i) : 0 < q z i := div_pos (normQ_pos _ _ hF _) (by have := normQ_pos s f hF z; positivity)
  let Q (z : Grid M) : Law Bool :=
    ⟨q z,fun i => (HQ z i).le,by
      rw [Fintype.sum_bool]
      have HE :
          normQ s f z=(normQ (s.smaller false) f z+normQ (s.smaller true) f z)/2 :=
        s.here.dice_child hp hh _
      have hh := normQ_pos s f hF z
      simp only [q]; field_simp; linarith⟩
  have he := Hcond_compare P g Prod.snd Q (fun i _ => HQ _ _)
  have hl (i : Grid M × Grid M) : -log (Q i.2 (g i)) =
      log 2+log (normQ s f i.2)-log (normQ (s.smaller (g i)) f i.2) := by
    change -log (q _ _) = _
    unfold q; have hx := normQ_pos s f hF i.2
    rw [log_div (normQ_pos _ _ hF _).ne' (by positivity),log_mul (by norm_num) hx.ne']; ring
  rw [funext hl] at he
  let D (b : Bool) (x : Grid M × Grid M) :=
    log (normQ (s.smaller b) f x.2)-log (f x.2 x.1)
  have hi : P.Hcond g Prod.snd = sideH v k := rfl
  rw [hi] at he
  have hT :
      v.probs.Ex (fun i => (tracker (s.smaller i) main).Ex (D i)) = P.Ex fun x => D (g x) x :=
    track_shift main (v:=v) rfl H (fun _ => rfl) D
  have hhE : v.probs.Ex (fun b => (s.smaller b).actor.privateH k) =
      s.actor.privateH k-sideH v k := by
    have Hh := conditioned_balance k v H
    change v.probs.Ex (fun b => (s.smaller b).actor.privateH k)+_=s.actor.privateH k at Hh
    linarith
  change v.probs.Ex (fun b => deficit _ k + (tracker _ _).Ex (D b)) ≤ _
  unfold flex deficit
  simp_rw [levels_child s hh, Ex_add v.probs]
  rw [show v.probs.Ex (fun x => _-_) = levels s-log 2-v.probs.Ex
      (fun b => (s.smaller b).actor.privateH k) by rw [Ex_sub (f:=fun _ => levels s-log 2),Ex_const],hT,hhE]
  unfold D at *
  simp_rw [Ex_sub] at *
  change _ ≤ levels s-s.actor.privateH k+(P.Ex _-P.Ex _)
  rw [Ex_add (f:=fun _=>log 2),Ex_const] at he
  linarith

end FourierLLogL.Dyadic.Procedure.Capture

end OAI
