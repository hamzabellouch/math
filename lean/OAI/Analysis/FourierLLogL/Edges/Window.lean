import OAI.Analysis.FourierLLogL.Edges.Wire
/-! # Cost of an observed boundary window -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal

namespace Wire
variable {M : ℕ} {s : Scene M} {t : Wire M s}
open scoped Classical

private lemma spotted_equal {s : Scene M} (h : ReadyAt s) (hm : 0 < s.mass)
    (q : Grid M → Prop) (hq : spotted q s.here.lev) :
    s.actor.prob q = (s.here.dice M).prob q := by
  let c := s.here.start M
  have hc : c∈s.here.block M := start_mem h.1.1 h.1.2
  have hh (P : Law (Grid M)) (hp : ∀ x, 0 < P x → x∈s.here.block M) :
      P.prob q = if q c then 1 else 0 := by
    unfold prob
    conv_rhs => rw [← Ex_const P (if q c then 1 else 0)]
    refine Ex_congr_mem _ fun x hx => ?_
    have H := hq _ rfl _ (hp x hx) _ hc
    by_cases hv : q c <;> simp [hv,H]
  exact (hh _ (piece_support h.1 (actor_def h.1 h.2 hm))).trans (hh _
    (fun x hx => (dice_positive h.1).mp hx)).symm

def coverL (n : ℕ) (l : List (Pulse M)) : ℝ := ((l.take n).map Pulse.realized).sum

def fairValue (q : Grid M → Prop) (n : ℕ) (l : List (Pulse M)) (x : Grid M) :=
    if q x then exp (-coverL n l) else 0

private lemma present {s : Scene M} (t : Wire M s) {a : Bool} (h : t.Valid a)
    (hm : 0 < s.mass) (n : ℕ) (hn : s.here.lev+n ≤ M) (q : Grid M → Prop)
    (hq : spotted q (s.here.lev+n)) :
    s.actor.Ex (fun x => fairValue q n (t.read x) x) ≤ (s.here.dice M).prob q := by
  classical
  induction t generalizing n a with
  | term s =>
    obtain ⟨hh,he⟩ := h
    have H : n = 0 := by omega
    subst n
    simp only [Nat.add_zero] at hq
    rw [← spotted_equal hh hm _ hq]
    unfold prob; simp only [fairValue,coverL,List.take_zero,List.map_nil,List.sum_nil,
      neg_zero,exp_zero]; exact le_rfl
  | stay s v k ih =>
    cases v <;> exact ih h.2 hm n hn hq
  | spot s u k ih =>
    obtain ⟨ha,h2,hH,hk⟩ := h
    have he := hH hm
    rw [spotEx u k (fairValue q n) he]
    rw [← Ex_const u.snip.probs ((s.here.dice M).prob q)]
    apply Ex_mono_mem
    intro b hb
    have hx := ih b (hk b) ((true_mass he).mp hb) n
      (by rw [h2 b]; exact hn) (by rw [h2 b]; exact hq)
    rw [h2 b] at hx
    exact hx
  | link s g k ih =>
    obtain ⟨ha,hG,hV,hk⟩ := h
    have he : (step s).TrueLaw := step_true ha.1.1 hG ha.2 hm
    cases n with
    | zero =>
      simp only [Nat.add_zero] at hq
      rw [← spotted_equal ha hm _ hq]
      unfold prob; simp only [fairValue,coverL,List.take_zero,List.map_nil,List.sum_nil,
        neg_zero,exp_zero]; exact le_rfl
    | succ n =>
      rw [linkEx g k (fairValue q (n+1)) he]
      let P := (step s).probs
      let V (b) := (s.smaller b).actor
      let Z (b) := fun x => fairValue q (n+1) (⟨s,g,b⟩::(k b).read x) x
      have HE (b : Bool) :
          P b * (V b).Ex (Z b) ≤ (1/2)*(s.smaller b |>.here.dice M).prob q := by
        rcases eq_or_lt_of_le (P.nonneg b) with hi|hi
        · rw [← hi,zero_mul]
          apply mul_nonneg (by norm_num) (prob_nonneg _ _)
        have hP : (s.smaller b).here.lev+n=s.here.lev+(n+1) := by cases b <;>
          simp [smaller,child,L,R,add_comm n,add_assoc]
        have H := ih b (hk b) ((true_mass he).mp hi) n (by rw [hP]; exact hn)
          (by rw [hP]; exact hq)
        have hZ (x : Grid M) : Z b x =
            (2*P b)⁻¹ * fairValue q n ((k b).read x) x := by
          unfold Z fairValue; split_ifs
          · unfold coverL; simp only [List.take_succ_cons,List.map_cons,List.sum_cons, Pulse.realized]
            rw [show -(whistle _ _+_)= -whistle (step s) b + -coverL n ((k b).read x) by
              unfold coverL; ring,exp_add,Real.exp_neg,whistle,exp_log (by change 0< 2* P b; positivity)]
            rfl
          · ring

        rw [funext hZ,Ex_lmul, ← mul_assoc]
        rw [show P b*(2*P b)⁻¹=1/2 by field_simp]
        exact mul_le_mul_of_nonneg_left H (by norm_num)
      change P.Ex (fun b => (V b).Ex (Z b)) ≤ _
      rw [Ex,Fintype.sum_bool]
      apply (add_le_add (HE true) (HE false)).trans
      unfold prob
      rw [dice_child s.here ha.1.1 hG]
      simp only [smaller,child]
      linarith

def startMark (i : ℕ) (l : List (Pulse M)) : Prop :=
    reach i * log 2/2 ≤ coverL (reach i) l

private lemma distance_scale (i : ℕ) (main : Bool) :
    exp ((reach i)*log 2/2)*(4*side (reach i)) ≤ gateWidth main i/4 := by
  let n := 40+4*i
  have hi : reach i = 2*n := by unfold reach n; omega
  have hE :
      exp (((reach i):ℝ)*log 2/2)*(4*side (reach i)) = 4 * side n := by
    rw [hi,Nat.cast_mul,Nat.cast_ofNat,show 2*(n:ℝ)*log 2/2=log (2^n) by rw [log_pow]; ring,
       exp_log (by positivity : 0 < (2:ℝ)^n)]
    unfold side
    rw [mul_comm 2 n,pow_mul,one_div,inv_pow]
    field_simp
  rw [hE]
  have he : side n = side 40 * side i ^ 4 := by
    unfold n side; rw [pow_add,mul_comm 4 i,pow_mul]
  unfold gateWidth; rw [he]
  have hQ : side i^4 ≤ side i^2 :=
      pow_le_pow_of_le_one (side_pos _).le (side_le _) (by omega)
  have h₂ : side i^2 ≤ side i := by
    simpa using pow_le_pow_of_le_one (side_pos i).le (side_le i) (by omega : 1 ≤ 2)
  split <;> norm_num [side] at * <;> nlinarith

theorem mark_chance {s : Scene M} (t : Wire M s) {a : Bool} (h : t.Valid a)
    (hm : 0 < s.mass) (ht : ¬ enter s) (main : Bool) (i : ℕ) (hh : hazard s main i) :
    let P := s.actor
    P.prob (flanked s.here i) ≤ 2*P.prob (fun x => startMark i (t.read x)) := by
  obtain ⟨hx1,hx2⟩ := h.atSrc
  obtain ⟨hi,hj,hc⟩ := hazard_rule hx1 hx2 hm ht hh
  let q := flanked (M:=M) s.here i
  let n := reach i; let r := n * log 2/2
  intro P
  have HH := present t h hm n hi q (flanked_at _ _)
  have H₁ := HH.trans (flank_prob _ hx1.1 i hi)
  let f := fun x => fairValue q n (t.read x) x
  let b := fun x => startMark i (t.read x)
  let F (x) := if b x then (1:ℝ) else 0
  have H :
      P.prob q ≤ P.prob b + exp r*P.Ex f := by
    unfold prob
    rw [← Ex_lmul, ← Ex_add]
    refine Ex_mono _ fun x => ?_
    unfold f fairValue
    by_cases h1 : q x
    · simp only [h1,ite_true]
      split_ifs with H
      · have H : 0 ≤ exp r * exp (-coverL n (t.read x)) := by positivity
        linarith
      rw [zero_add,← exp_add]; apply Real.one_le_exp
      change ¬ r ≤ coverL n (t.read x) at H; linarith
    simp only [h1,ite_false]; split_ifs <;> norm_num
  have hT : exp r * P.Ex f ≤ gateWidth main i /4 :=
    (mul_le_mul_of_nonneg_left H₁ (exp_nonneg _)).trans (distance_scale i main)
  change gateWidth main i/2 ≤ P.prob q at hc
  change P.prob q ≤ 2*P.prob b
  linarith

end Wire
end FourierLLogL.Dyadic.Procedure

end OAI
