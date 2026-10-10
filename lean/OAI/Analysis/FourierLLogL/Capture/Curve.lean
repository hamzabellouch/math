import OAI.Analysis.FourierLLogL.Capture.Append

/-! # Adaptive frequency list along a plateau -/

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Capture
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Chart

variable {M J j : ℕ}
open scoped Classical

def speed (p : Node) (i n : ℕ) := band p i (offset i n)
def horizon (p : Node) (i n : ℕ) := (1+n:ℝ)*speed p i n
def localSize (p : Node) (i : ℕ) (c : Chart M) :=
    c.wide ≤ c.size*speed p i c.size

lemma speed_pos (p : Node) (i n : ℕ) : 0 ≤ speed p i n := by unfold speed band; positivity
lemma speed_le {p q : Node} (h : p.lev ≤ q.lev) {i n m : ℕ} (he : n ≤ m) :
    speed p i n ≤ speed q i m := by
  unfold speed band offset
  gcongr; norm_num

/-- One or several appends before a jump. -/
structure Widen (p : Scene M) (i : ℕ) (main : Bool) (c d : Chart M) : Prop where
  sonic : d.Sound
  extend : c.items ⊆ d.items
  paid : flex p main d.refs+price main i*(d.size-c.size:ℝ) ≤ flex p main c.refs
  expands : localSize p.here i c → localSize p.here i d
  mass : d.size=c.size ∨ amp i main/2 ≤ p.mass/p.norm
  awake : ¬ hazard p main i → ∀ x, intense main p (side i) x →
    atReach d.items (d.wide+speed p.here i d.size) x

lemma widen_done (main : Bool) (i : ℕ) {q : Scene M}
    (hp : q.here.valid) (he : q.here.lev < M) (ha : 0 ≤ q.wage) (hn : 0 < q.norm)
    (hm : 0 < q.mass) (hM : q.mass ≤ 2*q.norm)
    (c : Chart M) (h : c.Sound) : ∃ d, Widen q i main c d := by
  classical
  let b := Fintype.card (Grid M)
  suffices H : ∀ n : ℕ, ∀ c : Chart M, b-c.size=n → c.Sound →
      ∃ d, Widen q i main c d from H _ _ rfl h
  intro n; induction n using Nat.strong_induction_on with
  | h n ih =>
  intro c heq h
  by_cases hv : ¬ hazard q main i → ∀ x, intense main q (side i) x →
      atReach c.items (c.wide+speed q.here i c.size) x
  · exact ⟨c,h,Finset.Subset.refl _,by simp,id,Or.inl rfl,hv⟩
  push Not at hv
  obtain ⟨hH,x,hx,hB⟩ := hv
  obtain ⟨d,h1,h2,h3,h4,h5⟩ := append_choose _ _ hp he ha hn hm hM hH c h x hx hB
  have hd : b-d.size < n := by
    have H : d.size ≤ b := Finset.card_le_univ _; omega
  obtain ⟨t,h₁,h₂,h₃,h₄,h₅,h₆⟩ := ih _ hd d rfl h4
  refine ⟨t,h₁,Finset.Subset.trans ?_ h₂,?_,fun hk => h₄ ?_,Or.inr
    (expensive_intent main hp he ha hn hm hx), h₆⟩
  · rw [h1]; exact Finset.subset_insert _ _
  · rw [← h2] at h₃; push_cast at *
    linarith
  unfold localSize at *; rw [h3,← h2]; push_cast
  have hi' : speed q.here i c.size ≤ speed q.here i (c.size+1) := speed_le le_rfl (by omega)
  change c.wide+speed q.here i c.size ≤ _
  nlinarith [Nat.cast_nonneg (α:=ℝ) c.size]

def zoom (s : Scene M) (i : ℕ) (main : Bool) (q : Chart M) : Chart M :=
    if h : ∃ c, Widen s i main q c then Classical.choose h else q

lemma zoom_spec {s q : Scene M} {l}
    (t : Chart M) (hp : t.Sound) (i : ℕ) (main : Bool) {f : Grid M → ℝ}
    (h : Following j J f (Thread.ran s q l)) :
    Widen q i main t (zoom q i main t) := by
  unfold zoom; split
  · exact Classical.choose_spec _
  · rename_i hF; apply False.elim; apply hF
    obtain ⟨ha,hb,hc,hd,he,hk⟩ := h
    have hS := hd.2.2; unfold enter at hS
    have ht := hd.1.2.2
    exact widen_done main _ hc.within.1 (rooted _ (hk false)).within.2 hc.positive (by linarith) ht
      (by linarith) _ hp


def goal (i : ℕ) (main : Bool) (q : Chart M) : List (Beat M) → Chart M
  | [] => q
  | b::l => goal i main (zoom b.post i main q) l

def buildup (i : ℕ) (main : Bool) (q : Chart M) (l : List (Beat M)) :=
    ((goal i main q l).size:ℝ) - q.size

lemma buildup_ran (i : ℕ) (main : Bool) (q : Chart M) (b : Beat M) (l : List (Beat M)) :
    buildup i main q (b::l) = (zoom b.post i main q).size - (q.size:ℝ) +
      buildup i main (zoom b.post i main q) l := by simp only [buildup,goal]; ring

def chartDebt (s : Scene M) (j : ℕ) (q : Chart M) (b : Bool) :=
    flex s b q.refs+(minimumT j)⁻¹

lemma buildup_total (s : Scene M) (t : Thread M s) (f : Grid M → ℝ)
    (h : Following j J f t) (main : Bool) (i : ℕ) (C : Chart M) (hC : C.Sound)
    (hn : 0 < s.norm) :
    (amp i main/2*price main i)*(s.here.dice M).Ex (fun x => buildup i main C (t.stream x)) ≤
      s.mass/s.norm*chartDebt s j C main := by
  induction t generalizing C with
  | blank s =>
    have hh := rooted _ h
    rcases eq_or_lt_of_le hh.mass_lower with H|H
    · simp [stream,buildup,goal,← H,Ex_const]
    have hF := flex_nonneg _ ⟨hh.within,hh.positive⟩ H main _ (Chart.Sound.pos C hC)
    have hp : 0 ≤ s.mass/s.norm*chartDebt s j C main := mul_nonneg (by positivity)
      (add_nonneg hF (inv_nonneg.mpr (minimum_pos j).le))
    simpa only [stream,buildup,goal,sub_self,Ex_const,mul_zero] using hp
  | ran s q k ih =>
    let Z := zoom q i main C
    let A := amp i main; let b := price main i
    let G (u : Chart M) (t : Scene M) := flex t main u.refs
    let B := (minimumT j)⁻¹
    let v := step q; let m := (keep s q).snip
    have hm' := pre_pos h
    have hD : Widen q i main C Z := zoom_spec _ hC i main h
    have hd := debt_at h
    rw [stream_branch k h (fun l _ => buildup i main C l)]
    have he b' :
        (q.smaller b').norm = q.norm := rfl
    obtain ⟨ha,hb,hc,hf,ht,hk⟩ := h
    have hs' : ReadyAt s := ⟨ha.within,ha.positive⟩
    have hq' : ReadyAt q := ⟨hc.within,hc.positive⟩
    have hQ : 0 < q.norm := by rw [hb.1.flat]; exact hn
    have hq := hf.1.2.2
    have hv : q.here.lev < M := (rooted _ (hk false)).within.2
    have hF := flex_down main q hc.within.1 hv hc.positive hq Z.refs (Chart.Sound.pos _ hD.sonic)
    have hS := flex_keep main hb.1 hs' hq' hm' _ (Chart.Sound.pos _ hC)
    have hK : m.probs true * s.mass=q.mass := (kept_mass hb.1 hs' hq' hm').symm
    have hz : 0 ≤ (Z.size:ℝ)-C.size := by
      apply sub_nonneg.mpr
      exact_mod_cast Finset.card_le_card hD.extend
    have HP : 0 ≤ b := by unfold b price; positivity
    let d := (Z.size:ℝ)-C.size
    have hP : A/2*b*d ≤ q.mass/q.norm*(b*d) := by
      rcases hD.mass with H|H
      · unfold d; simp [H]
      · rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right H (mul_nonneg HP hz)
    let D (u) := G Z (q.smaller u)+B
    have hh (u : Bool) :
      (A/2*b)* ((q.smaller u).here.dice M).Ex (fun x => buildup i main Z ((k u).stream x)) ≤
        (q.smaller u).mass/q.norm * D u := ih u (hk u) Z hD.sonic hQ
    let U := uniform Bool
    let x (u : Bool) := ((q.smaller u).here.dice M).Ex (fun x => buildup i main Z ((k u).stream x))

    have HI : U.Ex (fun z => ((q.smaller z).mass/q.norm)*D z) ≤
        q.mass/q.norm*(G Z q +B) := by
      have He := output_split q hc.within.1 hv hc.positive hq (fun z => q.norm⁻¹*D z)
      have HM : (step q).probs.Ex D ≤ G Z q+B := by
        unfold D; rw [Ex_add,Ex_const]
        exact add_le_add_left hF B
      rw [Ex_lmul] at He
      calc
        _ = q.mass*(q.norm⁻¹ * v.probs.Ex D) := by
          unfold U v; rw [He]; congr 1; funext z; ring
        _ ≤ _ := by
          rw [← mul_assoc,← div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left HM (by positivity)
    have HS :
        (A/2*b)*(U.Ex fun z => d+x z) ≤ q.mass/q.norm*(b*d+G Z q+B) := by
      rw [Ex_add (f:=fun _ => d),Ex_const,mul_add,← Ex_lmul]
      have HH := U.Ex_mono hh
      change U.Ex (fun z => A/2*b*x z) ≤ _ at HH
      apply le_trans (add_le_add hP (HH.trans HI)); rw [mul_add,mul_add]
      exact le_of_eq (by ring)
    simp_rw [buildup_ran,Ex_add,Ex_const]
    have hhT : (A/2*b)*(d+U.Ex x) ≤ q.mass/q.norm*(b*d+G Z q+B) := by
      rw [Ex_add (f:=fun _=>d),Ex_const] at HS; exact HS

    have hg3 :
        q.mass/q.norm*(b*d+G Z q+B) ≤ s.mass/s.norm*(G C s+B) := by
      rw [hb.1.flat,← hK]
      have hx : b*d + G Z q ≤ G C q := by
        have hi := hD.paid; change G Z q + b*d ≤ G C q at hi; linarith
      have ht : m.probs true*(b*d+G Z q+B) ≤ G C s+B := by
        change m.probs.entropy ≤ B*m.probs false at hd
        change m.probs true*G C q ≤ G C s+m.probs.entropy at hS
        have HQ : m.probs true + m.probs false = 1 := by simpa only [Fintype.sum_bool] using m.probs.total
        nlinarith [m.probs.nonneg true,show B * (m.probs true + m.probs false) = B by rw [HQ]; ring]
      rw [mul_div_assoc,mul_comm (m.probs true),mul_assoc (a:=s.mass/s.norm)]
      exact mul_le_mul_of_nonneg_left ht (div_nonneg hm'.le hn.le)
    change A/2*b*(d+U.Ex x) ≤ s.mass/s.norm*(G C s+B)
    exact hhT.trans hg3

end FourierLLogL.Dyadic.Procedure.Capture

end OAI
