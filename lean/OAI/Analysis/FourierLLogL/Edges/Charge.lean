import OAI.Analysis.FourierLLogL.Edges.Intervals

/-! # The unlabelled entropy charge inequality -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Wire
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Pulse
variable {M : ℕ} {s : Scene M}
open scoped Classical

def toll (p : Policy M) (main : Bool) (e : Pulse M) :=
    if e.active = true ∧ ¬ enter e.scene then
      e.scene.norm/e.scene.mass * surcharge e.scene main (p e.scene) else 0

private lemma mark_total {p : Policy M} (main : Bool) (w : Wire M s) {a : Bool}
    (h : w.Valid a) (hm : 0 < s.mass) :
    w.expenditure (toll p main) ≤ 2*s.actor.Ex (fun x => labels p (w.read x)) := by
  induction w generalizing a with
  | term => simp [expenditure,read,Ex_const,labels]
  | stay s v w ih =>
    rw [fee_stay]
    cases v <;> exact ih h.2 hm
  | spot s u k ih =>
    have hh := h.2.2.1 hm
    have h1 := spotEx u k (fun z _ => (labels p z:ℝ)) hh
    rw [fee_spot _ _ _ hh,h1,← Ex_lmul]
    apply Ex_mono_mem _
    exact fun b hb => ih b (h.2.2.2 _) ((true_mass hh).mp hb)
  | link s v k ih =>
    obtain ⟨he,hh,hx,hk⟩ := h
    have hf := step_true he.1.1 hh he.2 hm
    let P := (step s).probs; let T := s.actor
    let F (b : Bool) := (k b).expenditure (toll p main)
    let L := Wire.link s v k
    let Q (b : Bool) := (s.smaller b).actor
    have ht (b : Bool) (hp : 0 < P b) :
        F b ≤ 2*(Q b).Ex (fun x => (labels p ((k b).read x):ℝ)) :=
      ih b (hk _) ((true_mass hf).mp hp)
    let Y (b : Bool) : Pulse M := ⟨s,v,b⟩
    let B := if v = true ∧ ¬ s.enter then s.norm/s.mass * surcharge s main (p s) else 0
    have hT (b) : toll p main (Y b) = B := rfl
    let x1 (b : Bool) (i : Grid M) : ℝ := ↑(tags p (Y b) ((k b).read i))
    let x2 (b : Bool) (i : Grid M) : ℝ := ↑(labels p ((k b).read i))
    have Hx : T.Ex (fun i => (labels p (L.read i):ℝ)) =
        P.Ex (fun b => (Q b).Ex (x1 b)+(Q b).Ex (x2 b)) := by
      unfold T L; rw [linkEx v k (fun z _ => (labels p z:ℝ)) hf]
      unfold P Q; simp only [labels,Nat.cast_add]
      simp_rw [Ex_add]; rfl
    have H₁ : B ≤ 2*P.Ex (fun b => (Q b).Ex (x1 b)) := by
      have hp1 : 0 ≤ 2*P.Ex (fun b => (Q b).Ex (x1 b)) := by
        apply mul_nonneg (by norm_num)
        exact Ex_nonneg _ fun i => Ex_nonneg _ fun j => by unfold x1; positivity
      dsimp only [B]
      split_ifs with hv
      · obtain ⟨hv,hE⟩ := hv
        cases ha : decide (hazard s main (p s))
        · rw [surcharge,ite_eq_right (of_decide_eq_false ha),mul_zero]; exact hp1
        have hi := of_decide_eq_true ha
        rw [surcharge,ite_eq_left hi,(hazard_rule he.1 he.2 hm hE hi).2.1]
        have Hh : L.Valid a := ⟨he,hh,hx,hk⟩
        apply (mark_chance L Hh hm hE main (p s) hi).trans
        refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num)
        unfold prob
        rw [linkEx v k (fun z i => if startMark (p s) z then (1:ℝ) else 0) hf]
        unfold P Q
        congr 1; funext b; refine congrArg (Q b).Ex ?_
        funext i
        unfold x1 tags Y
        simp [hv]
      exact hp1
    rw [fee_link v k _ hf,Ex_add]
    change P.Ex (fun b => toll p main (Y b))+P.Ex F ≤ _
    simp_rw [hT,Ex_const]
    change _ ≤ 2*T.Ex (fun i => (labels p (L.read i):ℝ))
    rw [Hx,Ex_add,mul_add]
    apply add_le_add H₁
    rw [← Ex_lmul]; exact Ex_mono_mem _ ht

/-- All length charge or the version using trailing K. -/
theorem edge_total (p : Policy M) (main : Bool) (t : Wire M s) {a : Bool}
    (h : Valid t a) (hm : 0 < s.mass) (K : ℕ) (hk : ∀ x : Scene M, K=0 ∨ reach (p x) ≤ K) :
    t.expenditure (toll p main) ≤ 128*t.expenditure (due K)+2*K := by
  apply le_trans (mark_total main t h hm)
  have H := s.actor.Ex_mono (mark_intervals p t h K hk)
  rw [Ex_add,Ex_lmul,Ex_const] at H
  unfold expenditure
  linarith

end FourierLLogL.Dyadic.Procedure.Wire

end OAI
