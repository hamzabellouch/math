import OAI.Analysis.FourierLLogL.Procedure.Score

/-! # The score includes sizeable payments even conditional on the actual input -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Memory
variable {M J j : ℕ} {s : Scene M}
open scoped Classical

namespace Road

/-- Require each batch's total own-energy below temp; at success the available past
temp is expanded. -/
def tempered (m : Memory M) (j : ℕ) (s : Scene M) (x : Grid M) :=
    sumE m.profile x ≤ s.fund.uses* temp j

lemma temperature (m : Memory M) {f : Grid M → ℝ} (s : Scene M)
    (h : s.Safe j J f) (x : Grid M) (hh : tempered m j s x) :
    sumE m.profile x ≤ cushion j := by
  have hi : 0 < capA*H j := mul_pos (by norm_num [capA]) (H_pos _)
  have hp : 0 ≤ cushion j := by unfold cushion; have := d_pos j; positivity
  calc
    _ ≤ s.fund.uses*temp j := hh
    _ ≤ (capA*H j)*temp j := mul_le_mul_of_nonneg_right h.capital.under (div_nonneg hp hi.le)
    _ = cushion j := by unfold temp; rw [mul_comm,div_mul_cancel₀ _ hi.ne']

private lemma good_payment :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ m : Memory M, ∀ x : Grid M,
      ∀ f : Grid M → ℝ, ∀ u : Update j M s.here, Safe s j J f → Safe (s.win u) j J f →
      u.Good capA s.fund.mood s.actor →
      Ready m j s.fund → x∈s.here.block M → u.take s.fund.mood x → tempered m j s x →
      1/2 ≤ (fresh s.fund.mood (u.next s.fund.mood) j x).prob (fun w => gate m s u w ∧
        tempered (stash m s.fund.mood (u.next s.fund.mood) w) j (s.win u) x) := by
  filter_upwards [Memory.batch_scale,Update.quiet_scale capA cap_ok,h_large 16]
    with j hj hl hp M J s m x f u hs hw hu hm hx he ht
  let A := s.fund.mood; let B := u.next A
  let Q := fresh A B j x
  let E (w : Clutch j M) := temp j < loadE A B w x
  let L (w : Clutch j M) := u.regular=true ∧ Update.quiet u w
  have hE : Q.prob E ≤ 1/4 := hj M J s f x u hs hw
  have hL : Q.prob L ≤ 1/4 := by
    by_cases h : u.regular=true
    · have H : L= u.quiet := by simp [L,h]
      rw [H]
      refine le_trans (hl _ _ _ _ u hu h _ he) ?_
      have hh : Thermal.H j ≤ Thermal.H j ^40 := by
        have ht := pow_le_pow_right₀ (H_ge j) (show 1 ≤ 40 by omega)
        simpa using ht
      field_simp; linarith
    unfold prob L; simp [h, Ex_const]
  let p (w : Clutch j M) := gate m s u w ∧ tempered (stash m A B w) j (s.win u) x
  have HA := hs.capital.effects.nonneg
  have hStash w : Ready (stash m A B w) j (s.win u).fund := stash_ready m hm u hu.positive HA _
  have hR : ∀ i∈m.profile, 0 ≤ i.1 := fun i hi => (hm.ordered i hi).1
  have hU (w) (hh : ¬ E w ∧ ¬ L w) : p w := by
    let m' := stash m A B w
    have he' : tempered m' j (s.win u) x := by
      unfold tempered at *
      have Hg : loadE A B w x ≤ temp j := not_lt.mp hh.1
      unfold m'; rw [sumE_stash]
      change _+_ ≤ ((s.fund.uses+1:ℕ):ℝ)*_
      push_cast; linarith
    refine ⟨?_,he'⟩
    unfold gate; split
    case isTrue h1 =>
      have HX := temperature m s hs x ht
      refine ⟨⟨x,hx,HX⟩,Update.consistent_triangle u HA (y:=x) ?_ ?_
        (fun H => hh.2 ⟨h1,H⟩)⟩
      · apply le_trans _ HX
        exact form_in_past m (A,m.current) hR hm.has x
      intro i
      apply le_trans _ (temperature m' (s.win u) hw x he')
      have hz := hStash w
      apply form_in_past m' (A,w.2 i) (fun i hi => (hz.ordered i hi).1) ?_ x
      simp only [m',stash,piece,List.mem_append,List.mem_cons,List.mem_ofFn]
      exact Or.inl (Or.inr ⟨i,rfl⟩)
    trivial
  change 1/2 ≤ Q.prob p
  have H : Q.prob (fun w => ¬ p w) ≤ 1/4+1/4 := by
    apply le_trans (b:=Q.prob (fun w => E w ∨ L w))
    · exact Q.prob_mono _ _ fun w hi => by by_contra! ht; exact hi (hU _ ht)
    apply le_trans (prob_union Q E L) (add_le_add hE hL)
  rw [prob_compl] at H; linarith

def rating (s : Scene M) (l : Journal j M) : ℝ :=
    (l.done.fund.bank-s.fund.bank)/8 - l.membership - l.fee count

lemma stake_lower :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ t : Road j M s, Trusted J f t → ∀ (m : Memory M), Ready m j s.fund →
      0 < s.mass → ∀ x : Grid M, 0 < s.actor x → tempered m j s x →
        exp (rating s (t.hike x)) ≤ t.score m x := by
  filter_upwards [good_payment] with j hj M J s f t h m ht hm x hx he
  induction t generalizing m with
  | finish s b => simp [hike,rating,membership,fee,score]
  | push s v t ih =>
    obtain ⟨ha,hb,hc,hd⟩ := h
    have hS : (s.pace v).fund=s.fund := by cases v <;> rfl
    have Hi := ih hd m (by rw [hS]; exact ht) (by rw [pace_mass]; exact hm)
      (by rw [pace_actor]; exact hx) (by unfold tempered;rw [hS]; exact he)
    rw [show rating s ((push s v t).hike x) = rating (s.pace v) (t.hike x) by
      simp [rating,hike,prepend,membership,fee,count,hS,memFee,failFee,winFee]]
    exact Hi
  | fork s v t ih =>
    have hB := branchTrusted h
    obtain ⟨hx1,hx2⟩ := Fork.branch_pos hB (x:=x) (by rw [v.source]; exact hx)
    have hx3 := (true_mass hB).mp hx1
    obtain ⟨ha,hb,hc,hd⟩ := h
    cases v with
    | move =>
      let b := (step s).bit x
      have Hi := ih b (hd b) m ht hx3 hx2 he
      change exp (rating s (((t b).hike x).prepend (.march s .move b))) ≤ _
      apply le_trans _ Hi
      dsimp only [rating]
      simp [prepend,membership,fee, count, memFee,failFee,winFee,Turn.fork,step,smaller]
    | ask u =>
      let v : Turn j s := .ask u
      let T := toss s u
      let A := s.fund.mood
      let B := u.next A
      let P := T.probs
      let Z := fresh A B j x
      have Hx (b : Bool) (hv : v.fork.bit x=b) :
          exp (rating s ((fork s v t).hike x)) =
            P b * exp (rating (v.fork.dst b) ((t b).hike x) + (if b then u.bill/8-1 else 0)) := by
        change 0 < P (v.fork.bit x) at hx1
        rw [hv] at hx1
        let w := (t b).hike x
        have Hz (b : Bool) : memFee (.march s v b) = -log (P b) := by
          cases b <;> simp only [memFee,v,winFee,failFee,surprise,zero_add,add_zero] <;> rfl
        have Heq (q : Journal j M) (b) :
            rating s (q.prepend (.march s v b)) =
              log (P b)+ (rating (v.fork.dst b) q + if b then u.bill/8-1 else 0) := by
          unfold rating membership
          rw [fee_pre,fee_pre,Hz]
          cases b
          · change (q.done.fund.bank-s.fund.bank)/8 - (- log (P false) + _) - (0+q.fee _) =
              log (P false)+((q.done.fund.bank-s.fund.bank)/8-_-_+0)
            ring
          · change (q.done.fund.bank-s.fund.bank)/8 - (- log (P true) + _) - (1+q.fee _) =
              log (P true)+((q.done.fund.bank-(s.fund.bank+u.bill))/8-_-_+(u.bill/8-1))
            ring
        have H1 :
            (fork s v t).hike x = w.prepend (.march s v b) := by
          unfold w
          let F (b : Bool) := ((t b).hike x).prepend (.march s v b)
          change F (v.fork.bit x)=F b
          exact congrArg _ hv
        rw [H1,Heq,exp_add,exp_log hx1]
      by_cases H : u.take A x
      · have hb' : v.fork.bit x=true := decide_eq_true H
        have hu' : u.Good capA A s.actor := hc.2
        have HY : x∈s.here.block M :=
          piece_support ha.within (actor_def ha.within ha.positive hm) _ hx
        let Q (w : Clutch j M) := gate m s u w ∧ tempered (stash m A B w) j (s.win u) x
        have HHq : 1/2 ≤ Z.prob Q := hj M J s m x f u ha (rootSafe (hd true)) hu' ht HY H he
        let d := exp (rating (s.win u) ((t true).hike x))
        let W (w : Clutch j M) := stash m A B w
        have HN (w) (hw : Q w) : d ≤ score (t true) (W w) x := by
          change 0 < (v.fork.dst (v.fork.bit x)).mass at hx3
          change 0 < (v.fork.dst (v.fork.bit x)).actor x at hx2
          rw [hb'] at hx3 hx2
          exact ih _ (hd _) _ (stash_ready m ht u hu'.positive ha.capital.effects.nonneg w)
            hx3 hx2 hw.2
        let M' (w : Clutch j M) := if gate m s u w then score (t true) (W w) x else 0
        have HE' : d/2 ≤ Z.Ex M' := by
          have hpos (w) : 0 ≤ M' w := by unfold M'; split_ifs; exact score_nonneg _ _ _; norm_num
          have Ht := Z.upperTail Q M' hpos d (by intro i hi; unfold M'; rw [ite_eq_left hi.1]; exact HN i hi)
          have hh : 0 ≤ d := exp_nonneg _
          nlinarith
        have Heq : exp (-1) ≤ 1/2 := by rw [exp_neg,← one_div]; exact one_div_le_one_div_of_le (by norm_num) exp_one_gt_two.le
        rw [Hx _ hb']
        change P true * exp (rating (s.win u) ((t true).hike x) + (if _ then _ else _)) ≤
          (if u.take A x then P true * (exp (u.bill/8)*Z.Ex M') else _)
        rw [ite_eq_left rfl,ite_eq_left H,exp_add,sub_eq_add_neg,exp_add]
        apply mul_le_mul_of_nonneg_left _ (P.nonneg _)
        change d * _ ≤ _
        rw [mul_left_comm]
        have hh : d * exp (-1) ≤ Z.Ex M' := by have hh : 0 ≤ d := exp_nonneg _; nlinarith
        exact mul_le_mul_of_nonneg_left hh (exp_nonneg _)
      have hb' : v.fork.bit x=false := decide_eq_false H
      change 0 < (v.fork.dst (v.fork.bit x)).mass at hx3
      change 0 < (v.fork.dst (v.fork.bit x)).actor x at hx2
      rw [hb'] at hx3 hx2
      have HX := ih false (hd false) m ht hx3 hx2 he
      rw [Hx _ hb']
      change P false * _ ≤ (if u.take A x then _ else P false * score (t false) m x)
      rw [ite_eq_right H,ite_eq_right (by decide),add_zero]
      exact mul_le_mul_of_nonneg_left HX (P.nonneg _)

end Road
end FourierLLogL.Dyadic.Procedure

end OAI
