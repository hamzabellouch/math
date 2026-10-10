import OAI.Analysis.FourierLLogL.Assembly.Cast
/-! # The uniform output path -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Paths
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture Chart Snapshot
variable {M j J : ℕ} {s q : Scene M} {f : Grid M → ℝ}
open scoped Classical


namespace CastShow
open Troupe

def jackpot (x : Grid M) {s : Scene M} (t : Play j M s) :=
    s.norm*souvenir s.live j ((project t).stream x)
def annual (x : Grid M) {s : Scene M} (t : Play j M s) : ℝ := match t with
| .rest _ => 0
| .ticket _ t => jackpot x t+annual x t
| .freeze _ t => annual x t
| .attempt _ _ l r => annual x l+annual x r
| .jump s l r => if (step s).bit x then annual x r else annual x l

lemma fit_ticket {s : Scene M} {t : Play j M s.reset} (h : (Play.ticket s t).Follows J f) :
    Fit s.reset ∧ entry s.reset ∧ (s.live=true → exp (-height j) ≤ s.reset.norm) := by
  obtain ⟨ha,hb,hc,hd,he⟩ := h
  have hh := hb.2.2
  refine ⟨⟨⟨ha.within,ha.positive⟩,hh,?_⟩,rfl, fun H => le_of_not_gt (fun h => hc ⟨H,Or.inr h⟩)⟩
  change s.mass/s.mass ≤ 4; rw [div_self hh.ne']; norm_num

lemma annual_valid :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, J ≤ M → ∀ s : Scene M, ∀ f : Grid M → ℝ,
      ∀ t : Play j M s, t.Follows J f → ∀ u x : Grid M, x∈s.here.block M →
        ‖summons u x t‖ ≤ annual x t := by
  filter_upwards [gala] with j hj M J hh s f t h u x hx
  induction t with
  | rest s => simp [summons,annual]
  | ticket s t ih =>
    rw [summons,annual]
    have HT := fit_ticket h
    obtain ⟨ha,hb,hc,hd,he⟩ := h
    apply le_trans (norm_add_le _ _)
    apply add_le_add _ (ih he hx)
    let q := t
    unfold ordinary jackpot; rw [norm_scaleC,abs_of_nonneg HT.1.pos.le]
    apply mul_le_mul_of_nonneg_left _ HT.1.pos.le
    have H := Thread.projected _ he
    exact hj _ _ hh _ f _ _ _ (stream_cast _ H x) (trip_stream _ H HT.1 hx)
  | freeze s t ih => exact ih h.2.2.2 hx
  | attempt s v l r il ir =>
    rw [summons,annual]
    exact (norm_add_le _ _).trans (add_le_add (il h.2.2.2.2.1 hx) (ir h.2.2.2.2.2 hx))
  | jump s l r il ir =>
    rw [summons,annual]
    have HE := stream_child (less_self _) hx
    split_ifs with HH
    · exact ir h.2.2.2.2 (HH ▸ HE)
    · rw [show (step s).bit x=false from Bool.eq_false_iff.mpr HH] at HE
      exact il h.2.2.2.1 HE

/-- Prices in true history. -/
def normStamp (s : Scene M) (j : ℕ) :=
    if s.live then (s.norm/s.mass)*stamp s j else 0
def billOf : Event j M → ℝ
| .pace s .renew => gateTax s.reset j
| .march s .move _ => normStamp s j
| _ => 0

def netGross {s : Scene M} (t : Play j M s) := (trace true t).flatFee billOf
def yieldA {s : Scene M} (t : Play j M s) :=
    (s.here.dice M).Ex (fun x => annual x t)
def overdue {s : Scene M} (t : Play j M s) :=
    if s.live then s.norm*stats (project t) (subtotal (fun b => stamp b.post j)) else 0

lemma dueEmpty {s : Scene M} {t : Play j M s} (h : project t=blank s) : overdue t=0 := by
  unfold overdue; rw [h]
  split; simp only [stats_nil,subtotal_nil,mul_zero]; rfl
lemma due_restart {s : Scene M} {t : Play j M s} (h : s.norm=0) : overdue t=0 := by simp [overdue,h]

lemma cost_jump (s : Scene M) (l : Play j M (s.smaller false)) (r : Play j M (s.smaller true))
    (h : (Play.jump s l r).Follows J f) :
    let a := s.norm*(if s.live then stamp s j else 0)
    yieldA (Play.jump s l r) + overdue (Play.jump s l r) =
      ((yieldA l+overdue l)+(yieldA r+overdue r))/2+a :=
by
  intro a
  let t := Play.jump s l r

  let k (b : Bool) : Thread M (s.smaller b) := match b with | false => project l | true => project r
  have HG : Following j J f (ran s s k) := projected _ h
  obtain ⟨ha,hb,hc,hd,he⟩ := h
  let v (b : Thread.Beat M) := stamp b.post j
  let U (q : Scene M) := q.here.dice M
  have hM : s.here.lev < M := (Play.first hd).within.2
  have HH : yieldA t=(yieldA l+yieldA r)/2 := by
    unfold yieldA
    rw [dice_child s.here ha.within.1 hM]
    have H (b : Bool) (x : Grid M) (hx : 0 < (U (s.smaller b)) x) :
        (step s).bit x=b := step_dice_child s.here ha.within.1 hM b hx
    have HE : (U (s.smaller false)).Ex (fun x => annual x t)=yieldA l := by
      apply Ex_congr_mem; intro x hx; unfold t; rw [annual,H false x hx]; rfl
    have HF : (U (s.smaller true)).Ex (fun x => annual x t)=yieldA r := by
      apply Ex_congr_mem; intro x hx; unfold t; rw [annual,H true x hx]; rfl
    change ((U (s.smaller false)).Ex (fun x => annual x t) + (U (s.smaller true)).Ex (fun x => annual x t))/2=(yieldA l+yieldA r)/2
    rw [HE,HF]
  have HF : (project t).fee v=stamp s j+((project l).fee v+(project r).fee v)/2 := by
    change (ran s s k).fee v=_
    rw [Thread.fee_ran k HG,fair_av]
    change (stamp s j+_+(stamp s j+_))/2=_
    unfold k; ring
  change yieldA t+_ = _
  rw [HH]
  unfold a overdue
  change (yieldA l+yieldA r)/2 +(if s.live=true then s.norm*(project t).fee v else 0) =
    ((yieldA l+(if s.live=true then s.norm*(project l).fee v else 0))+
      (yieldA r+(if s.live=true then s.norm*(project r).fee v else 0)))/2+
        s.norm*(if s.live then _ else 0)
  rw [HF]; split <;> ring

lemma cost_attempt (s : Scene M) (u : Update j M s.here)
    (l : Play j M (s.lose u)) (r : Play j M (s.win u)) :
    yieldA (Play.attempt s u l r)+overdue (Play.attempt s u l r) =
      yieldA l+overdue l+(yieldA r+overdue r) := by
  rw [due_restart (s:=s.win u) rfl]
  have h₁ : yieldA (Play.attempt s u l r)=yieldA l+yieldA r :=
    Ex_add (s.here.dice M) _ _
  have h₂ : overdue (Play.attempt s u l r)=overdue l := by
    unfold overdue; rw [project]
    cases project l <;> rfl
  rw [h₁,h₂]; ring

lemma cost_overall :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ f : Grid M → ℝ, ∀ s : Scene M,
      ∀ t : Play j M s, t.Follows J f → (∀ x, f x ≤ exp (height j)) →
        yieldA t+overdue t ≤ s.mass*netGross t := by
  filter_upwards [receipt_paid] with j hj M J f s t h hf
  induction t with
  | rest s =>
    rw [netGross,trace,flat_finish,dueEmpty rfl]
    simp_rw [yieldA,annual,Ex_const]; simp
  | ticket s t ih =>
    let v := s.reset
    have hs := fit_ticket h
    obtain ⟨ha,hb,hc,hd,he⟩ := h
    have HE := hj M J v (project t) f (projected _ he) hs.1 hs.2.1 hs.2.2 hf
    have HA : yieldA (Play.ticket s t)=
        v.norm*stats (project t) (souvenir v.live j)+yieldA t := by
      unfold yieldA
      simp_rw [annual,jackpot]; rw [Ex_add,Ex_lmul]
      rfl
    rw [HA, netGross, trace, flat_push,dueEmpty rfl,add_zero]
    let x := stats (project t) (souvenir v.live j)
    change v.norm*x+_ ≤ s.mass*(gateTax s.reset j+netGross t)
    let a : ℝ := if v.live then stats (project t) (subtotal (fun b => stamp b.post j)) else 0
    change x ≤ gateTax v j+a at HE
    have Hi := ih he
    rw [show overdue t = s.mass*a by unfold overdue a v; split <;> first|rfl|simp] at Hi
    change yieldA t+s.mass*a ≤ s.mass*_ at Hi
    change s.mass*x+_ ≤ s.mass*(gateTax v j+_)
    nlinarith [hb.2.2]
  | freeze s t ih =>
    rw [dueEmpty rfl,netGross,trace]
    rw [ite_eq_left rfl,flat_push]
    have HH := ih h.2.2.2
    rw [due_restart (s:=s.out) rfl] at HH
    change yieldA t+0 ≤ s.mass*(0+netGross t)
    rw [zero_add]; exact HH
  | jump s l r il ir =>
    let t := Play.jump s l r
    rw [cost_jump _ _ _ h]
    have H₁ := traced t true h
    unfold netGross; rw [trace,flat_fork _ _ H₁]
    obtain ⟨ha,hb,hc,hd,he⟩ := h
    let g (b : Bool) := if b then netGross r else netGross l

    let v : Bool → ℝ := fun b => match b with
      | false => netGross l
      | true => netGross r
    let w : ∀ b, Road j M (s.smaller b) := fun b => match b with
      | false => trace true l
      | true => trace true r
    let P := (step s).probs
    let m := s.mass; let x := s.norm*(if s.live then stamp s j else 0)
    have HV (b : Bool) : (w b).flatFee billOf = v b := by cases b <;> rfl
    have heq : P.Ex (fun b : Bool => normStamp s j+(w b).flatFee billOf) = normStamp s j+P.Ex v := by
      simp_rw [HV,Ex_add _ (f:=fun _ => _),Ex_const]
    change _ + x ≤ s.mass*P.Ex (fun b => normStamp s j+(w b).flatFee billOf)
    rw [heq,mul_add]
    have hM : s.here.lev < M := (Play.first hd).within.2
    have hi := output_split s ha.within.1 hM ha.positive hb.1.2.2 v
    have hm := hb.1.2.2
    rw [show s.mass*normStamp s j=x by unfold x normStamp; split; field_simp; simp]
    change s.mass*P.Ex v=_ at hi
    rw [hi,fair_av]
    have HI : (fun b => (s.smaller b).mass*v b) false = (s.smaller false).mass*netGross l := rfl
    change _/2+x ≤ x+ ((s.smaller false).mass*netGross l+(s.smaller true).mass*netGross r)/2
    linarith [il hd,ir he]
  | attempt s u l r il ir =>
    let t := Play.attempt s u l r
    let v := toss s u; let P := v.probs
    have H := traced t true h
    rw [cost_attempt,netGross,trace,flat_fork _ _ H]
    obtain ⟨ha,hb,hc,hd,he,hx⟩ := h
    let w : ∀ b, Road j M (v.dst b) := fun b => match b with
      | false => trace true l
      | true => trace true r
    change _ ≤ s.mass*P.Ex (fun b => 0+(w b).flatFee billOf)
    simp only [zero_add,Ex,Fintype.sum_bool]
    have Hi := toss_true u ha.within ha.positive hb.1.2.2
    have HH : (s.lose u).mass = P false*s.mass := toss_mass Hi false
    have HJ : (s.win u).mass = P true*s.mass := toss_mass Hi true
    change _ ≤ s.mass*(P true*netGross r+P false*netGross l)
    have Hi₁ := il he; have Hi₂ := ir hx
    rw [HH] at Hi₁; rw [HJ] at Hi₂; linarith

end CastShow


end FourierLLogL.Dyadic.Procedure.Paths

end OAI
