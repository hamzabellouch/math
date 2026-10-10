import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.NearEligible

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}
open RadiusMenus
open scoped Classical

noncomputable def guideAt (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : Option (State V)) : Guided.Kernel Unit (MainAction D C.bad.card) :=
  match s with
  | none => Guided.pure (.inl ())
  | some s => if hs : C.Correct hD mainKappa s then
      if ht : C.Terminal mainKappa Δ s then Guided.pure (.inl ())
      else C.activeGuide hD Δ hΔ hP hm s hs ht
    else ⟨fun _ a => (mainActual D S Δ C.bad.card).weight (some s) a,
      fun _ a => (mainActual D S Δ C.bad.card).nonneg (some s) a,
      fun _ => (mainActual D S Δ C.bad.card).total (some s)⟩

noncomputable def guideKernel (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    Guided.Kernel (Option (State V)) (MainAction D C.bad.card) :=
  ⟨fun s a => (C.guideAt hD Δ hΔ hP hm s).weight () a,
    fun s a => (C.guideAt hD Δ hΔ hP hm s).nonneg () a,
    fun s => (C.guideAt hD Δ hΔ hP hm s).total ()⟩

noncomputable def stoppedActual (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ) :=
  Guided.stoppedKernel (mainActual D S Δ C.bad.card) (C.stop hD Δ) (.inl ())

noncomputable def guidedUpdate (C : Comparison D S O) (hD : D.Nonempty) (F : Finset V) (Δ : ℝ) :=
  Guided.stoppedUpdate
    (update D F S hD Δ (comparisonCost D C.assign) mainKappa C.bad.card
      (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa C.bad.card))
    (C.stop hD Δ)

def Valid (C : Comparison D S O) (hD : D.Nonempty) : Option (State V) → Prop
  | none => False
  | some s => C.Correct hD mainKappa s

noncomputable def remaining (C : Comparison D S O) : Option (State V) → ℕ
  | none => 0
  | some s => C.counter s

lemma guide_invariant (C : Comparison D S O) (hD : D.Nonempty) (F : Finset V) (hOF : O ⊆ F)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : Option (State V)) (hs : C.Valid hD s) (a : MainAction D C.bad.card)
    (ha : 0 < (C.guideKernel hD Δ hΔ hP hm).weight s a) :
    C.Valid hD (C.guidedUpdate hD F Δ s a) := by
  cases s with
  | none => contradiction
  | some s =>
    change C.Correct hD mainKappa s at hs
    by_cases ht : C.Terminal mainKappa Δ s
    · change C.Valid hD (if C.stop hD Δ (some s) then some s else _)
      rw [ite_eq_left (show C.stop hD Δ (some s) from ⟨hs,ht⟩)]
      exact hs
    · have hstop : ¬C.stop hD Δ (some s) := by simpa only [stop,and_iff_right hs] using ht
      change 0 < (C.guideAt hD Δ hΔ hP hm (some s)).weight () a at ha
      simp only [guideAt,dite_eq_left hs,dite_eq_right ht] at ha
      have hW := C.active_weight_pos hD Δ hΔ hP s hs ht
      simp only [guidedUpdate,Guided.stoppedUpdate,ite_eq_right hstop]
      rcases C.activeGuide_support hD Δ hΔ hP hm s hs ht a ha with ⟨_,w,rfl,hw⟩ | ⟨_,_,w,rfl,hw⟩
      · obtain ⟨R,he,hc,_⟩ := C.update_eligible_ball hD F hOF Δ hP hm s hs hW w hw
        rw [he]
        exact hc
      · obtain ⟨v,_,he,hc,_⟩ := C.update_eligible_removal hD F Δ s hs hW w hw
        rw [he]
        exact hc

lemma guide_counter_decreases (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : Option (State V)) (hs : C.Valid hD s) (ht : ¬C.stop hD Δ s)
    (a : MainAction D C.bad.card) (ha : 0 < (C.guideKernel hD Δ hΔ hP hm).weight s a) :
    C.remaining (C.guidedUpdate hD F Δ s a) < C.remaining s := by
  cases s with
  | none => contradiction
  | some s =>
    change C.Correct hD mainKappa s at hs
    have hterm : ¬C.Terminal mainKappa Δ s := fun h => ht ⟨hs,h⟩
    change 0 < (C.guideAt hD Δ hΔ hP hm (some s)).weight () a at ha
    simp only [guideAt,dite_eq_left hs,dite_eq_right hterm] at ha
    have hW := C.active_weight_pos hD Δ hΔ hP s hs hterm
    simp only [guidedUpdate,Guided.stoppedUpdate,ite_eq_right ht]
    rcases C.activeGuide_support hD Δ hΔ hP hm s hs hterm a ha with ⟨_,w,rfl,hw⟩ | ⟨_,_,w,rfl,hw⟩
    · obtain ⟨R,he,_,hc⟩ := C.update_eligible_ball hD F hOF Δ hP hm s hs hW w hw
      rw [he]
      exact hc
    · obtain ⟨v,_,he,_,hc⟩ := C.update_eligible_removal hD F Δ s hs hW w hw
      rw [he]
      exact hc

theorem guide_hits (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (seed : Fin (2*C.bad.card) → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight (2*C.bad.card) (some State.initial) seed) :
    Guided.Hits (C.guidedUpdate hD F Δ) (C.stop hD Δ) (2*C.bad.card) (some State.initial) seed := by
  apply Guided.supported_path_hits (C.guidedUpdate hD F Δ) (C.guideKernel hD Δ hΔ hP hm)
    (C.stop hD Δ) (C.Valid hD) C.remaining
    (C.guide_invariant hD F hOF Δ hΔ hP hm) ?_
    (C.guide_counter_decreases hD F hOF Δ hΔ hP hm) (2*C.bad.card) (some State.initial)
    (C.correct_initial hD mainKappa) ?_ seed hseed
  · intro s hs hc
    cases s with
    | none => contradiction
    | some s =>
      exact ⟨hs,C.counter_zero_terminal hD mainKappa Δ s hs mainKappa_pos.le hc⟩
  · simp only [remaining,counter,State.initial,List.length_nil,Finset.card_empty,add_zero,Nat.sub_zero,le_refl]

noncomputable def actionMenuWeight (m : ℕ) : MainAction D m → ℝ
  | .inr (.inr (_,e)) => menuWeight (firstSize mainKappa)
      (geometricCap mainKappa mainKappa_pos) (thirdSize mainKappa m) e
  | _ => 1

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma actionMenuWeight_nonneg (m : ℕ) (a : MainAction D m) :
    0 ≤ actionMenuWeight m a := by
  rcases a with u | (w | ⟨w,e⟩)
  · exact zero_le_one
  · exact zero_le_one
  · exact menuWeight_nonneg _ _ _ e

lemma weighted_ratio_bound (ρ H T W : ℝ) (hH : 0 ≤ H) (hT : 0 < T)
    (hr : ρ ≤ T/(2*W)) : ρ*(H/T) ≤ H/(2*W) := by
  have hh := mul_le_mul_of_nonneg_right hr (div_nonneg hH hT.le)
  have he : T/(2*W)*(H/T) = H/(2*W) := by
    by_cases hW : W = 0
    · simp [hW]
    · field_simp
  exact he ▸ hh

lemma activeGuide_domination (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (ht : ¬C.Terminal mainKappa Δ s)
    (a : MainAction D C.bad.card) :
    NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a *
      (C.activeGuide hD Δ hΔ hP hm s hs ht).weight () a ≤
      (mainActual D S Δ C.bad.card).weight (some s) a := by
  have hW := C.active_weight_pos hD Δ hΔ hP s hs ht
  have hbound := C.correct_weight_bound hD Δ s hs hΔ hP hm
  let p : Guided.Kernel Unit (MainAction D C.bad.card) :=
    ⟨fun _ a => (mainActual D S Δ C.bad.card).weight (some s) a,
      fun _ a => (mainActual D S Δ C.bad.card).nonneg (some s) a,
      fun _ => (mainActual D S Δ C.bad.card).total (some s)⟩
  change _ ≤ p.weight () a
  unfold activeGuide
  split_ifs with hb
  · refine Guided.routed_domination p _ _ (fun _ w v he => by
      simp only [Sum.inr.injEq,Prod.mk.injEq] at he; exact he.1)
      (fun _ a => NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a) ?_ () a
    intro u w
    change _ * (if w.val ∈ C.nearEligible s then
      clientWeight S Δ s w/C.nearTotal Δ s else 0) ≤ _
    by_cases hw : w.val ∈ C.nearEligible s
    · rw [ite_eq_left hw]
      have hr := NearClients.ball_progress _ _ _ _ hP mainKappa_pos hW hb hbound
      have hh := weighted_ratio_bound _ _ _ _ (clientWeight_nonneg S Δ s w)
        ((mul_pos mainKappa_pos hP).trans hb) hr
      simp only [p,mainActual,actualKernel,transitionWeight,ite_eq_left hW]
      change _ ≤ clientWeight S Δ s w/(2*totalWeight D S Δ s)*
        menuWeight (firstSize mainKappa) (geometricCap mainKappa mainKappa_pos)
          (thirdSize mainKappa C.bad.card) (C.prescribedEntry hD hP hm s w)
      simpa only [actionMenuWeight,mul_assoc,mul_comm,mul_left_comm] using
        mul_le_mul_of_nonneg_right hh (menuWeight_nonneg _ _ _ (C.prescribedEntry hD hP hm s w))
    · rw [ite_eq_right hw,mul_zero]
      exact p.nonneg u _
  · refine Guided.routed_domination p _ _ (fun _ w v he => by simpa only [Sum.inr.injEq,Sum.inl.injEq] using he)
      (fun _ a => NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a) ?_ () a
    intro u w
    change _ * (if w.val ∈ C.removalEligible Δ s then
      clientWeight S Δ s w/C.removalTotal Δ s else 0) ≤ _
    by_cases hw : w.val ∈ C.removalEligible Δ s
    · rw [ite_eq_left hw]
      have hi : mainKappa*comparisonCost D C.assign < C.removalTotal Δ s := by
        by_contra hh
        exact ht ⟨le_of_not_gt hb,le_of_not_gt hh⟩
      have hr := NearClients.removal_progress _ _ _ _ _ hP mainKappa_pos hW
        (le_of_not_gt hb) hi hbound
      have hh := weighted_ratio_bound _ _ _ _ (clientWeight_nonneg S Δ s w)
        ((mul_pos mainKappa_pos hP).trans hi) hr
      simpa only [actionMenuWeight,mul_one,p,mainActual,actualKernel,transitionWeight,ite_eq_left hW] using hh
    · rw [ite_eq_right hw,mul_zero]
      exact p.nonneg u _

noncomputable def guideLoss (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ)
    (s : Option (State V)) (a : MainAction D C.bad.card) : ℝ :=
  if C.Valid hD s ∧ ¬C.stop hD Δ s then
    NearClients.progressConstant mainKappa * actionMenuWeight C.bad.card a else 1

lemma guideLoss_nonneg (C : Comparison D S O) (hD : D.Nonempty) (Δ : ℝ)
    (s : Option (State V)) (a : MainAction D C.bad.card) :
    0 ≤ C.guideLoss hD Δ s a := by
  unfold guideLoss
  split_ifs
  · exact mul_nonneg (NearClients.progressConstant_pos _ mainKappa_pos).le
      (actionMenuWeight_nonneg _ _)
  · exact zero_le_one

lemma guideLoss_domination (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (hΔ : 0 ≤ Δ) (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : Option (State V)) (a : MainAction D C.bad.card) :
    C.guideLoss hD Δ s a * (C.guideKernel hD Δ hΔ hP hm).weight s a ≤
      (C.stoppedActual hD Δ).weight s a := by
  cases s with
  | none =>
    have hstop : ¬C.stop hD Δ none := fun h => h
    have hg : ¬(C.Valid hD none ∧ ¬C.stop hD Δ none) := fun h => h.1
    simp only [guideLoss,ite_eq_right hg,one_mul,guideKernel,guideAt,
      stoppedActual,Guided.stoppedKernel,ite_eq_right hstop,mainActual,actualKernel,
      transitionWeight,Guided.pure]
    split_ifs <;> norm_num
  | some s =>
    by_cases hs : C.Correct hD mainKappa s
    · by_cases ht : C.Terminal mainKappa Δ s
      · have hstop : C.stop hD Δ (some s) := ⟨hs,ht⟩
        have hg : ¬(C.Valid hD (some s) ∧ ¬C.stop hD Δ (some s)) := fun h => h.2 hstop
        simp only [guideLoss,ite_eq_right hg,one_mul,guideKernel,guideAt,dite_eq_left hs,dite_eq_left ht,
          stoppedActual,Guided.stoppedKernel,ite_eq_left hstop,Guided.pure,le_refl]
      · have hstop : ¬C.stop hD Δ (some s) := fun h => ht h.2
        have hg : C.Valid hD (some s) ∧ ¬C.stop hD Δ (some s) := ⟨hs,hstop⟩
        simp only [guideLoss,ite_eq_left hg,guideKernel,guideAt,dite_eq_left hs,dite_eq_right ht,
          stoppedActual,Guided.stoppedKernel,ite_eq_right hstop]
        exact C.activeGuide_domination hD Δ hΔ hP hm s hs ht a
    · have hstop : ¬C.stop hD Δ (some s) := fun h => hs h.1
      have hg : ¬(C.Valid hD (some s) ∧ ¬C.stop hD Δ (some s)) := fun h => hs h.1
      simp only [guideLoss,ite_eq_right hg,one_mul,guideKernel,guideAt,dite_eq_right hs,
        stoppedActual,Guided.stoppedKernel,ite_eq_right hstop,le_refl]

noncomputable def history (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (Δ : ℝ) (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (i : Fin (n+1)) : State V :=
  (Guided.states (C.guidedUpdate hD F Δ) n (some State.initial) seed i).getD State.initial

lemma history_state (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin (n+1)) :
    Guided.states (C.guidedUpdate hD F Δ) n (some State.initial) seed i =
      some (C.history hD F Δ n seed i) := by
  have hv := Guided.states_invariant (C.guidedUpdate hD F Δ) (C.guideKernel hD Δ hΔ hP hm)
    (C.Valid hD) (C.guide_invariant hD F hOF Δ hΔ hP hm) n (some State.initial)
    (C.correct_initial hD mainKappa) seed hseed i
  unfold history
  cases he : Guided.states (C.guidedUpdate hD F Δ) n (some State.initial) seed i with
  | none => rw [he] at hv; exact False.elim hv
  | some s => rfl

lemma history_correct (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin (n+1)) : C.Correct hD mainKappa (C.history hD F Δ n seed i) := by
  have hh := Guided.states_invariant (C.guidedUpdate hD F Δ) (C.guideKernel hD Δ hΔ hP hm)
    (C.Valid hD) (C.guide_invariant hD F hOF Δ hΔ hP hm) n (some State.initial)
    (C.correct_initial hD mainKappa) seed hseed i
  rw [C.history_state hD F hOF Δ hΔ hP hm n seed hseed i] at hh
  exact hh

lemma supported_guide_step (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (s : State V) (hs : C.Correct hD mainKappa s) (a : MainAction D C.bad.card)
    (ha : 0 < (C.guideKernel hD Δ hΔ hP hm).weight (some s) a) :
    (C.Terminal mainKappa Δ s ∧ a = .inl () ∧ C.guidedUpdate hD F Δ (some s) a = some s) ∨
    (∃ w : D, ∃ R, a = .inr (.inr (w,C.prescribedEntry hD hP hm s w)) ∧
      w.val ∈ C.nearEligible s ∧ C.guidedUpdate hD F Δ (some s) a = some (s.add w R)) ∨
    (∃ w : D, ∃ v, a = .inr (.inl w) ∧ v ∈ C.nonproxy \ s.deleted ∧
      C.guidedUpdate hD F Δ (some s) a = some (s.remove v)) := by
  by_cases ht : C.Terminal mainKappa Δ s
  · have he : a = .inl () := by
      by_contra hh
      simp only [guideKernel,guideAt,dite_eq_left hs,dite_eq_left ht,Guided.pure,ite_eq_right hh] at ha
      exact lt_irrefl 0 ha
    refine Or.inl ⟨ht,he,?_⟩
    change (if C.stop hD Δ (some s) then some s else _) = some s
    exact ite_eq_left ⟨hs,ht⟩
  · have hstop : ¬C.stop hD Δ (some s) := fun h => ht h.2
    change 0 < (C.guideAt hD Δ hΔ hP hm (some s)).weight () a at ha
    simp only [guideAt,dite_eq_left hs,dite_eq_right ht] at ha
    have hW := C.active_weight_pos hD Δ hΔ hP s hs ht
    rcases C.activeGuide_support hD Δ hΔ hP hm s hs ht a ha with ⟨_,w,he,hw⟩ | ⟨_,_,w,he,hw⟩
    · obtain ⟨R,hupdate,_,_⟩ := C.update_eligible_ball hD F hOF Δ hP hm s hs hW w hw
      refine Or.inr (Or.inl ⟨w,R,he,hw,?_⟩)
      simp only [guidedUpdate,Guided.stoppedUpdate,ite_eq_right hstop,he]
      exact hupdate
    · obtain ⟨v,hv,hupdate,_,_⟩ := C.update_eligible_removal hD F Δ s hs hW w hw
      refine Or.inr (Or.inr ⟨w,v,he,hv,?_⟩)
      simp only [guidedUpdate,Guided.stoppedUpdate,ite_eq_right hstop,he]
      exact hupdate

lemma history_step (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin n) :
    let s := C.history hD F Δ n seed i.castSucc
    let t := C.history hD F Δ n seed i.succ
    (C.Terminal mainKappa Δ s ∧ seed i = .inl () ∧ t = s) ∨
    (∃ w : D, ∃ R, seed i = .inr (.inr (w,C.prescribedEntry hD hP hm s w)) ∧
      w.val ∈ C.nearEligible s ∧ t = s.add w R) ∨
    (∃ w : D, ∃ v, seed i = .inr (.inl w) ∧ v ∈ C.nonproxy \ s.deleted ∧ t = s.remove v) := by
  dsimp only
  have ha := Guided.supported_step (C.guidedUpdate hD F Δ) (C.guideKernel hD Δ hΔ hP hm)
    n (some State.initial) seed hseed i
  rw [C.history_state hD F hOF Δ hΔ hP hm n seed hseed i.castSucc] at ha
  have he := Guided.states_step (C.guidedUpdate hD F Δ) n (some State.initial) seed i
  rw [C.history_state hD F hOF Δ hΔ hP hm n seed hseed i.castSucc,
    C.history_state hD F hOF Δ hΔ hP hm n seed hseed i.succ] at he
  rcases C.supported_guide_step hD F hOF Δ hΔ hP hm _
      (C.history_correct hD F hOF Δ hΔ hP hm n seed hseed i.castSucc) (seed i) ha with
    ⟨ht,hact,hup⟩ | ⟨w,R,hact,hw,hup⟩ | ⟨w,v,hact,hv,hup⟩
  · exact Or.inl ⟨ht,hact,Option.some.inj (he.trans hup)⟩
  · exact Or.inr (Or.inl ⟨w,R,hact,hw,Option.some.inj (he.trans hup)⟩)
  · exact Or.inr (Or.inr ⟨w,v,hact,hv,Option.some.inj (he.trans hup)⟩)

lemma history_leaves_mono (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed) :
    Monotone (fun i => (C.history hD F Δ n seed i).leaves.toFinset) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  rcases C.history_step hD F hOF Δ hΔ hP hm n seed hseed i with
    ⟨_,_,he⟩ | ⟨w,R,_,_,he⟩ | ⟨w,v,_,_,he⟩
  · rw [he]
  · rw [he]
    intro z hz
    exact List.mem_toFinset.mpr (List.mem_append_left _ (List.mem_toFinset.mp hz))
  · rw [he]
    exact Finset.Subset.refl _

def IsBall {m : ℕ} (a : MainAction D m) : Prop := ∃ w e, a = .inr (.inr (w,e))
def IsThird {m : ℕ} (a : MainAction D m) : Prop := ∃ w j, a = .inr (.inr (w,.inr (.inr j)))

noncomputable def ballLeader (hD : D.Nonempty) {m : ℕ} : MainAction D m → D
  | .inr (.inr (w,_)) => w
  | _ => ⟨hD.choose,hD.choose_spec⟩

noncomputable def ballSteps {m n : ℕ} (seed : Fin n → MainAction D m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => IsBall (seed i))

noncomputable def thirdSteps {m n : ℕ} (seed : Fin n → MainAction D m) : Finset (Fin n) :=
  Finset.univ.filter (fun i => IsThird (seed i))

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma thirdSteps_subset {m n : ℕ} (seed : Fin n → MainAction D m) :
    thirdSteps seed ⊆ ballSteps seed := by
  intro i hi
  obtain ⟨w,j,he⟩ := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,w,_,he⟩

lemma history_ball (C : Comparison D S O) (hD : D.Nonempty)
    (F : Finset V) (hOF : O ⊆ F) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (n : ℕ) (seed : Fin n → MainAction D C.bad.card)
    (hseed : 0 < Guided.pathWeight (C.guidedUpdate hD F Δ)
      (C.guideKernel hD Δ hΔ hP hm).weight n (some State.initial) seed)
    (i : Fin n) (hi : i ∈ ballSteps seed) :
    let s := C.history hD F Δ n seed i.castSucc
    let w := ballLeader hD (seed i)
    ∃ R, seed i = .inr (.inr (w,C.prescribedEntry hD hP hm s w)) ∧
      w.val ∈ C.nearEligible s ∧ C.history hD F Δ n seed i.succ = s.add w R := by
  dsimp only
  obtain ⟨wi,ei,hai⟩ := (Finset.mem_filter.mp hi).2
  rcases C.history_step hD F hOF Δ hΔ hP hm n seed hseed i with
    ⟨_,ha,_⟩ | ⟨w,R,ha,hw,he⟩ | ⟨w,v,ha,_,_⟩
  · rw [hai] at ha; contradiction
  · have hl : ballLeader hD (seed i) = w := by rw [ha]; rfl
    rw [hl]
    exact ⟨R,ha,hw,he⟩
  · rw [hai] at ha
    cases Sum.inr.inj ha

end Comparison
end MetricKMedianRecovery.Sampling

end OAI
