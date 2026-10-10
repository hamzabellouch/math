import OAI.Analysis.FourierLLogL.Procedure.Counts
import OAI.Analysis.FourierLLogL.Procedure.Memory

/-! # Scoring surviving reference histories. We require evidence at successes only,
zeroing the score for regular successes without it. -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Memory
variable {M J j : ℕ} {s : Scene M}
open scoped Classical

def gate (m : Memory M) (s : Scene M) (u : Update j M s.here) (w : Clutch j M) :=
    if u.regular then admissible m.profile s.here (cushion j) ∧ u.alarm s.fund.mood m.current w
      else True

def sampleWinner (s : Scene M) (u : Update j M s.here) (m : Memory M) (x : Grid M)
    (f : Memory M → Grid M → ℝ) :=
    let A := s.fund.mood
    let B := u.next A
    exp (u.bill/8) * (fresh A B j x).Ex (fun w => if gate m s u w then f (m.stash A B w) x else 0)

def turnScore (s : Scene M) (v : Turn j s) (m : Memory M)
    (x : Grid M) (f : Bool → Memory M → Grid M → ℝ) :=
    match v with
    | .move => f ((step s).bit x) m x
    | .ask u =>
      if u.take s.fund.mood x then
        (toss s u).probs true * sampleWinner s u m x (f true)
      else
        (toss s u).probs false * f false m x

namespace Road
def score {s : Scene M} (t : Road j M s) (m : Memory M) (x : Grid M) :=
    match t with
    | .finish _ _ => 1
    | .push _ _ t => score t m x
    | .fork s v t => turnScore s v m x (fun b m x => score (t b) m x)

lemma score_nonneg {s : Scene M} (t : Road j M s) (m : Memory M) (x : Grid M) :
    0 ≤ score t m x := by
  induction t generalizing m x with
  | finish => change (0:ℝ)≤1; norm_num
  | push s v t ih => exact ih m x
  | fork s v t ih =>
    cases v
    · unfold score turnScore; dsimp only
      split_ifs
      · apply mul_nonneg (Law.nonneg _ _)
        unfold sampleWinner; dsimp only
        apply mul_nonneg (exp_nonneg _)
        refine Ex_nonneg _ fun z => ?_; split_ifs
        · exact ih true _ _
        · norm_num
      exact mul_nonneg (Law.nonneg _ _) (ih false _ _)
    exact ih _ _ _

private lemma total_gate {m : Memory M} (s : Scene M) (u : Update j M s.here) (f : Memory M → Grid M → ℝ)
    (hh : ∀ w : Clutch j M,
      let t := m.stash s.fund.mood (u.next s.fund.mood) w
      expU (fun x => prefixE t.profile s.here x * f t x) ≤ expU (prefixE t.profile s.here)) :
    let A := s.fund.mood; let B := u.next A
    let N := prefixE m.profile s.here
    expU (fun x => N x * sampleWinner s u m x f) ≤ exp (u.bill/8) *
      expU (fun x => N x*(fresh A B j x).prob (gate m s u)) := by
  intro A B N
  let c := exp (u.bill/8)
  let rate := stashRate A B j
  have he (x : Grid M) (w : Clutch j M) :
      N x * fresh A B j x w = rate * prefixE (stash m A B w).profile s.here x := multiply_stash _ _ _ _ _ _
  let U := uniform (Grid M)
  have step (w : Clutch j M) :
      U.Ex (fun x => N x*(fresh A B j x w * (if gate m s u w then f (stash m A B w) x else 0))) ≤
        U.Ex (fun x => N x * (fresh A B j x w * (if gate m s u w then 1 else 0))) := by
    by_cases H : gate m s u w
    · simp_rw [ite_eq_left H, ← mul_assoc,he,mul_assoc,mul_one,Ex_lmul]
      have Hh := hh w
      simp_rw [expU_ex] at Hh
      exact mul_le_mul_of_nonneg_left Hh (rate_positive _ _ _)
    simp [H]
  have H0 (x : Grid M) :
      N x*sampleWinner s u m x f =
        c*∑ w, N x*(fresh A B j x w * if gate m s u w then f (stash m A B w) x else 0) := by
    unfold sampleWinner; dsimp only
    rw [← Finset.mul_sum]; unfold Ex
    dsimp only [B,A,c]; rw [mul_left_comm]
  have H1 (x : Grid M) :
      N x*(fresh A B j x).prob (gate m s u) =
        ∑ w, N x * (fresh A B j x w * if gate m s u w then 1 else 0) := by
    unfold prob Ex; rw [Finset.mul_sum]
  simp_rw [expU_ex,H0,H1,Ex_lmul,Ex_finset_sum]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => step i) (exp_nonneg _)

lemma stake_upper :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, 1000*((2:ℝ)^J) ≤ 2^M →
      ∀ (s : Scene M) (f : Grid M → ℝ) (t : Road j M s),
        Trusted J f t → ∀ m : Memory M, m.Ready j s.fund →
          let g := prefixE m.profile s.here
          expU (fun x => g x*score t m x) ≤ expU g := by
  filter_upwards [conditional_bound capA cap_ok,Fund.fund_est] with j hu hf
  intro M J hJ s f t h m he
  induction t generalizing m with
  | finish s b =>
    intro g; simp [score]
  | push s v t ih =>
    obtain ⟨ha,hb,hc,hd⟩ := h
    have hF : (s.pace v).fund = s.fund := by cases v <;> rfl
    have hP : (s.pace v).here = s.here := by cases v <;> rfl
    have HH := ih hd m (hF.symm ▸ he)
    rw [hP] at HH
    exact HH
  | fork s v t ih =>
    obtain ⟨ha,hb,hc,hd⟩ := h
    intro g
    let V := uniform (Grid M)
    cases v with
    | move =>
      let Q (b : Bool) := prefixE m.profile (s.smaller b).here
      have h1 (b : Bool) :
          V.Ex (fun x => Q b x * score (t b) m x) ≤ V.Ex (Q b) := by
        have H := ih b (hd b) m (show Ready m _ _ from he)
        simp_rw [expU_ex] at H
        exact H
      have hi (x : Grid M) :
          g x*score (.fork s .move t) m x =
            Q false x*score (t false) m x + Q true x*score (t true) m x ∧
          g x = Q false x+Q true x := by
        have hh : x∈s.here.L.block M → x∈s.here.R.block M → False :=
          fun h h' => Set.disjoint_left.mp (s.here.block_separate M) h h'
        change (g x*score (t ((step s).bit x)) m x = _ ∧ _)
        unfold g Q
        unfold prefixE
        by_cases hl : x∈s.here.L.block M <;> by_cases hr : x∈s.here.R.block M
        all_goals
          first
            | exact (hh hl hr).elim
            | have hx : x∈s.here.block M ↔ _ := Set.ext_iff.mp (block_union _ _) x
              first
              | rw [show (step s).bit x = true from decide_eq_true hr]
                simp [smaller,child,hx, hl,hr]
              | rw [show (step s).bit x = false from decide_eq_false hr]
                simp [smaller,child,hx, hl,hr]
      rw [funext (fun x => (hi x).1),funext (fun x => (hi x).2)]
      simp_rw [expU_ex,Ex_add]
      unfold V at h1
      exact add_le_add (h1 false) (h1 true)
    | ask u =>
      let A := s.fund.mood
      let B := u.next A
      have hA : 0 ≤ A := ha.capital.effects.nonneg
      let T := toss s u
      let P := T.probs
      let F (b : Bool) := score (t b)
      have HI : V.Ex (fun x => g x*F false m x) ≤ V.Ex g := by
        have H := ih false (hd _) m (show Ready _ _ _ from he)
        simp_rw [expU_ex] at H; exact H
      have HH : V.Ex (fun x => g x* sampleWinner s u m x (F true)) ≤ V.Ex g := by
        unfold V; simp_rw [← expU_ex]
        have hG := total_gate s u (F true) (m:=m) (by
          intro w; exact ih true (hd true) _ (stash_ready m (s:=s) he u hc.2.positive hA w))
        apply hG.trans
        cases H : u.regular with
        | false =>
          change u.regular=false at H
          have Hp (x : Grid M) : (fresh A B j x).prob (gate m s u)=1 := by
            unfold prob; simp [gate,H,Ex_const]
          change exp (u.bill/8) * expU (fun x => g x * (fresh A B j x).prob _) ≤ _
          simp_rw [Hp,mul_one]
          simp [Update.bill,H]
        | true =>
          have Hh : u.bill=u.credit := by simp [Update.bill,H]
          change exp (u.bill/8) * expU (fun x => g x * (fresh A B j x).prob _) ≤ _
          rw [Hh]
          by_cases hN : admissible m.profile s.here (cushion j)
          · have HE : gate m s u = u.alarm A m.current := by
              funext w; simp [gate,H,hN]; rfl
            rw [HE]
            have HP := ((hf M).2 s.fund s.here ha.capital).2
              (fun h => hb.2.1 ⟨hc.1,Or.inl h⟩) ha.within |>.1
            have Ht := hu M s.here s.fund.mood HP (by
              apply le_trans _ hJ
              gcongr
              exact pow_le_pow_right₀ (by norm_num) ha.depth_ok)
              s.actor u hc.2 H m.profile he.ordered (stash_length_bound m he ha) hN m.current
            apply le_trans (mul_le_mul_of_nonneg_left Ht (Real.exp_nonneg _))
            rw [← mul_assoc,← exp_add,add_neg_cancel,exp_zero,one_mul]
          · have Hp (x : Grid M) : (fresh A B j x).prob (gate m s u)=0 := by
              unfold gate prob
              simp [hN,H,Ex_const]
            simp_rw [Hp,mul_zero,expU_ex,Ex_const,mul_zero]
            exact Ex_nonneg _ fun i => prefixE_nonneg _ _ _
      rw [expU_ex,expU_ex]
      let R (x) := sampleWinner s u m x (F true)
      calc
        _ ≤ V.Ex fun x => P false * (g x * F false m x) + P true * (g x * R x) :=
          Ex_mono _ fun x => by
            change g x * (if u.take A x then P true*R x else P false*F false m x) ≤ _
            have h1 : 0 ≤ F false m x := score_nonneg _ _ _
            have h2 : 0 ≤ R x := by
              unfold R sampleWinner; dsimp only
              apply mul_nonneg (exp_nonneg _) (Ex_nonneg _ _)
              intro i
              split_ifs <;> first | exact score_nonneg _ _ _ | exact le_rfl
            have hG : 0 ≤ g x := prefixE_nonneg _ _ _
            split_ifs
            · rw [mul_left_comm]; exact le_add_of_nonneg_left (mul_nonneg (P.nonneg _) (mul_nonneg hG h1))
            · rw [mul_left_comm]; exact le_add_of_nonneg_right (mul_nonneg (P.nonneg _) (mul_nonneg hG h2))
        _ = P false*(V.Ex (fun x => g x*F false m x)) + P true*(V.Ex (fun x => g x*R x)) := by
          rw [Ex_add,Ex_lmul,Ex_lmul]
        _ ≤ P false*V.Ex g + P true*V.Ex g :=
          add_le_add (mul_le_mul_of_nonneg_left HI (P.nonneg _)) (mul_le_mul_of_nonneg_left HH (P.nonneg _))
        _ = _ := by rw [← add_mul,show P false + P true = 1 by simpa only [Fintype.sum_bool,add_comm] using P.total,one_mul]

end Road
end FourierLLogL.Dyadic.Procedure

end OAI
