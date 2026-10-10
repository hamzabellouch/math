import OAI.Analysis.FourierLLogL.Edges.Extended

/-! # The edge bounds in the global road -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse
variable {M J j : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

def Event.edgeFee (p : Policy M) (b : Bool) (e : Event j M) :=
    match e with
    | .march s .move t => toll p b ⟨s,true,t⟩
    | _ => 0

lemma cut_wire (t : Road j M s) (h : Trusted J f t) (hm : 0 < s.mass) (K : ℕ) (hK : K ≠ 0) :
    expenditure (tape t) (due K) = flatFee t likelihood := by
  apply active_charge _ _ _ _ _ _ t h hm
  · intro i hi; unfold due; rw [ite_eq_right]; simp [hi,hK]
  · intro s p; simp [likelihood]
  · intro s v p; simp [likelihood]
  intro s _
  simp only [due,or_true, ↓reduceIte,Pulse.signal]
  change (step s).probs.Ex (step s).whistle = _
  rw [Ex_const,pitch_eq]

lemma toll_wire (t : Road j M s) (h : Trusted J f t) (hm : 0 < s.mass) (p : Policy M) (b : Bool) :
    expenditure (tape t) (toll p b) = flatFee t (edgeFee p b) := by
  apply active_charge _ _ _ _ _ _ t h hm
  · intro i hi; simp [toll,hi]
  · intro s v; simp [edgeFee]
  · intro s u v; simp [edgeFee]
  intro s _; rfl

lemma global_edges :
    ∀ᶠ j : ℕ in atTop, ∀ M J : ℕ, ∀ f : Grid M → ℝ,
      (∀ x, f x ≤ exp (height j)) →
      let s := beginPlay f true
      ∀ t : Road j M s, Trusted J f t → 1/Thermal.H j ≤ s.mass →
        (∀ p : Policy M, t.flatFee (edgeFee p false) ≤ 1000*height j) ∧
        ∀ i, i ≤ testIx j → t.flatFee (edgeFee (fun _ => i) true) ≤ 10000*limitC*Thermal.H j := by
  filter_upwards [Road.final_coarse, Road.mem_budget,hpoly limitC 1] with j hi hL h
    M J f hF s t hT hM
  let a := Thermal.H j; let d := height j
  have hp : 0 < a := H_pos _
  have he : 1 ≤ a := H_ge _
  have hc : 1 ≤ limitC := by unfold limitC; norm_num
  have hm : 0 < s.mass := lt_of_lt_of_le (by positivity : 0<1/a) hM
  let T := tape t
  have ht : T.Valid true := tape_ok t hT
  constructor
  · intro p
    rw [← toll_wire t hT hm]
    apply le_trans (edge_total p false T ht hm 0 (fun i => Or.inl rfl))
    have hr := rootSafe hT
    let k := fun _ : Grid M => uniform Unit
    have hD : levels s-s.actor.entropy ≤ d+a := by
      have h := local_deficit_dry s (uniform Unit) hr.within hr.positive hm d hF
      unfold deficit at h
      rw [privateH_const] at h
      have HH := log_le_log (by positivity : 0 < 1/a) hM
      rw [one_div,log_inv] at HH
      linarith [log_le_sub_one_of_pos hp]
    have H₁ := due_all T _ ht hm
    rw [show T.spotDebt=t.flatFee memFee from debt_like t hT hm] at H₁
    have HH := (hL M J s f t hT hm).2
    change t.flatFee memFee ≤ limitC*a at HH
    rw [pow_one] at h; change limitC*a≤d at h
    change 128 * expenditure T (due 0)+_≤1000*d
    norm_num; nlinarith
  intro i he'
  rw [←toll_wire t hT hm]
  apply le_trans (edge_total _ true T ht hm (reach i) (fun i => Or.inr le_rfl))
  have H : T.expenditure (due (reach i)) = t.flatFee likelihood := cut_wire t hT hm _ (Nat.ne_of_gt (reach_pos _))
  rw [H]
  have hi := (hi M J s f t hT hM).1
  have hz := (main_bounds _ he').2.1
  unfold reach; push_cast
  change t.flatFee likelihood ≤ 2*limitC *a at hi
  change _ ≤ 19*a at hz
  change _ ≤ 10000*limitC*a
  nlinarith

end FourierLLogL.Dyadic.Procedure

end OAI
