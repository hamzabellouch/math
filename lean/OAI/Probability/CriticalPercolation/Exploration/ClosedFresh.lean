import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.CompileEmptyReads

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree BondGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma exhaustive_mapTarget (G : BondGraph V E) (B : Set V) (order : List (Dart V E))
    (ho : Exhaustive G order) : Exhaustive (G.wireTargets B) (order.map (mapDart B)) := by
  intro v e t he
  obtain ⟨a,b,hab⟩ : ∃ a b, G.ends e = s(a,b) := Sym2.exists.mp ⟨G.ends e,rfl⟩
  change Sym2.map (collapseTarget B) (G.ends e) = s(v,t) at he
  rw [hab,Sym2.map_mk] at he
  rcases Sym2.eq_iff.mp he with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact List.mem_map.mpr ⟨(a,e,b),ho a e b hab,by simp only [mapDart,ha,hb]⟩
  · exact List.mem_map.mpr ⟨(b,e,a),ho b e a (hab.trans Sym2.eq_swap),
      by simp only [mapDart,ha,hb]⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
lemma mapState_initial (B : Set V) (a : V) :
    mapState (E := E) B (initial a) = initial (collapseTarget B a) := by
  simp [mapState,initial]

omit [Fintype E] in

theorem search_reads_targetWiring (G : BondGraph V E) (B : Set V)
    (order : List (Dart V E)) (horder : GoodDarts G order) (a : V) (ω : E → Bool) :
    (search G order a B).reads ω =
      (search (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a) {none}).reads ω := by
  by_cases ha : a ∈ B
  · have hs := compile_stop G order B (rank order (initial a) (push G order a))
      (initial a) (push G order a) ⟨a,Finset.mem_singleton_self _,ha⟩
    have hn := (collapseTarget_eq_none B a).mpr ha
    have hs' := compile_stop (G.wireTargets B) (order.map (mapDart B)) {none}
      (rank (order.map (mapDart B)) (initial (collapseTarget B a))
        (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a)))
      (initial (collapseTarget B a))
      (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a))
      ⟨collapseTarget B a,Finset.mem_singleton_self _,by simp only [Set.mem_singleton_iff,hn]⟩
    unfold search
    rw [hs,hs']; rfl
  · let r := rank order (initial (E := E) a) (push G order a)
    let r' := rank (order.map (mapDart B)) (initial (E := E) (collapseTarget B a))
      (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a))
    have h := compile_reads_targetWiring G B order horder (max r r')
      (initial a) (push G order a) (push_goodDarts G order a) ω
    rw [mapState_initial,push_mapTarget G B order horder a ha] at h
    have h1 := compile_reads_rank_independent G order B r (max r r')
      (initial a) (push G order a) ω le_rfl (le_max_left ..)
    have h2 := compile_reads_rank_independent (G.wireTargets B) (order.map (mapDart B)) {none}
      r' (max r r') (initial (collapseTarget B a))
      (push (G.wireTargets B) (order.map (mapDart B)) (collapseTarget B a)) ω
      le_rfl (le_max_right ..)
    exact h1.trans (h.trans h2.symm)

theorem search_target_pivotal_moments (G : BondGraph V E) (B : Set V)
    (order : List (Dart V E)) (horder : GoodDarts G order) (ho : Exhaustive G order)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    expect w ((search G order a B).score p F w) ≤ 1 ∧
      expect w (fun ω => ((search G order a B).score p F w ω)^2) ≤ 3 := by
  let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
  have h := targetSearch_moments G B (order.map (mapDart B))
    (exhaustive_mapTarget G B order ho) a hp w h0 h1
  have heq : (search G order a B).score p F w =
      (targetSearch G B (order.map (mapDart B)) a).score p F w := by
    funext ω
    rw [score_eq_listScore,score_eq_listScore]
    unfold targetSearch
    rw [search_reads_targetWiring G B order horder]
  change expect w ((search G order a B).score p F w) ≤ 1 ∧ _
  rw [heq]
  exact h

end CriticalPercolation.LazyDFS

namespace CriticalPercolation.SearchTree
open scoped Classical
open FiniteProduct LazyDFS

variable {E R : Type*} [Fintype E] [DecidableEq E]

def ClosedFresh (r : E → Prop → ℝ) (p : ℝ) (C : Set E) (used : Finset E) : Prop :=
  ∀ e ∉ used, r e False = (if e ∈ C then 1 else 1-p) ∧
    r e True = (if e ∈ C then 0 else p)

omit [Fintype E] in
lemma closedFresh_pin (r : E → Prop → ℝ) (p : ℝ) (C : Set E) (used : Finset E)
    (hf : ClosedFresh r p C used) (e : E) (b : Prop) :
    ClosedFresh (pin r e b) p C (insert e used) := by
  intro j hj
  have hj' : j ≠ e ∧ j ∉ used := by simpa only [Finset.mem_insert,not_or] using hj
  unfold pin
  simp only [Function.update,dite_eq_right hj'.1]
  exact hf j hj'.2

noncomputable def contactScore (T : SearchTree E R) (p : ℝ) (C : Set E)
    (F : Set E → Prop) (w : E → Prop → ℝ) (ω : E → Prop) : ℝ :=
  match T with
  | .done _ => 0
  | .ask e l r => (if e ∈ C then p*delta w F e else 0) +
      if ω e then r.contactScore p C F (pin w e True) ω
      else l.contactScore p C F (pin w e False) ω

noncomputable def terminalProbability (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : E → Prop) : ℝ :=
  match T with
  | .done _ => prob w F
  | .ask e l r => if ω e then r.terminalProbability F (pin w e True) ω
      else l.terminalProbability F (pin w e False) ω

omit [DecidableEq E] in
lemma contact_mean_step (e : E) (l r : SearchTree E R) (p : ℝ) (C : Set E)
    (F : Set E → Prop) (w v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1) :
    expect v ((.ask e l r : SearchTree E R).contactScore p C F w) =
      (if e ∈ C then p*delta w F e else 0) +
      v e True*expect (pin v e True) (r.contactScore p C F (pin w e True)) +
      v e False*expect (pin v e False) (l.contactScore p C F (pin w e False)) := by
  change expect v (fun ω => (if e ∈ C then p*delta w F e else 0) +
    if ω e then r.contactScore p C F (pin w e True) ω
    else l.contactScore p C F (pin w e False) ω) = _
  rw [expect_add,expect_const v hv]
  erw [expect_prop_ite]
  ring

omit [DecidableEq E] in
lemma terminal_mean_step (e : E) (l r : SearchTree E R) (F : Set E → Prop)
    (w v : E → Prop → ℝ) :
    expect v ((.ask e l r : SearchTree E R).terminalProbability F w) =
      v e True*expect (pin v e True) (r.terminalProbability F (pin w e True)) +
      v e False*expect (pin v e False) (l.terminalProbability F (pin w e False)) := by
  exact expect_prop_ite v e _ _

theorem contact_mean_terminal (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used) :
    expect v (T.contactScore p C F w) + expect v (T.terminalProbability F w) = prob w F := by
  induction T generalizing used w v with
  | done r =>
    change expect v (fun _ => 0) + expect v (fun _ => prob w F) = prob w F
    rw [expect_zero,expect_const v hv,zero_add]
  | ask e l r hl hr =>
    have he : w e False = 1-p ∧ w e True = p := hf e hT.1
    have hv' := hc e hT.1
    have hl' := hl (insert e used) hT.2.1 (pin w e False) (pin v e False)
      (pin_normalized w hw e False) (pin_normalized v hv e False)
      (fresh_pin w p used hf e False) (closedFresh_pin v p C used hc e False)
    have hr' := hr (insert e used) hT.2.2 (pin w e True) (pin v e True)
      (pin_normalized w hw e True) (pin_normalized v hv e True)
      (fresh_pin w p used hf e True) (closedFresh_pin v p C used hc e True)
    have hs : prob w F = w e False*prob (pin w e False) F +
        w e True*prob (pin w e True) F := expect_split_pin w e _
    rw [contact_mean_step e l r p C F w v hv,terminal_mean_step,hv'.1,hv'.2]
    rw [he.1,he.2] at hs
    by_cases heC : e ∈ C <;> simp only [heC,↓reduceIte,zero_mul,one_mul,add_zero,zero_add]
    · unfold delta
      linear_combination hl' - hs
    · linear_combination (1-p)*hl' + p*hr' - hs

omit [DecidableEq E] in
lemma terminalProbability_nonneg (T : SearchTree E R) (F : Set E → Prop)
    (w : E → Prop → ℝ) (hn : ∀ e b, 0 ≤ w e b) (ω : E → Prop) :
    0 ≤ T.terminalProbability F w ω := by
  induction T generalizing w with
  | done r => exact prob_nonneg w hn F
  | ask e l r hl hr =>
    unfold terminalProbability
    split_ifs
    · exact hr (pin w e True) (pin_nonneg w hn e True)
    · exact hl (pin w e False) (pin_nonneg w hn e False)

theorem contact_mean_le_prob (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    (p : ℝ) (C : Set E) (F : Set E → Prop) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hnw : ∀ e b, 0 ≤ w e b) (hnv : ∀ e b, 0 ≤ v e b)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used) :
    expect v (T.contactScore p C F w) ≤ prob w F := by
  have ht := contact_mean_terminal T used hT p C F w v hw hv hf hc
  have hn := expect_nonneg hnv (terminalProbability_nonneg T F w hnw)
  linarith

omit [DecidableEq E] in
lemma expect_square_add_const (v : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1)
    (a : ℝ) (f : (E → Prop) → ℝ) :
    expect v (fun ω => (a+f ω)^2) = a^2+2*a*expect v f+expect v (fun ω => (f ω)^2) := by
  have heq : (fun ω => (a+f ω)^2) = (fun ω => a^2+2*a*f ω+(f ω)^2) := by
    funext ω; ring
  rw [heq,expect_add,expect_add,expect_const v hv,expect_const_mul]

theorem contact_second_le_three_mean (T : SearchTree E R) (used : Finset E) (hT : T.Valid used)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (C : Set E) (F : Set E → Prop)
    (hF : ∀ s t, s ⊆ t → F s → F t) (w v : E → Prop → ℝ)
    (hw : ∀ e, ∑ b, w e b = 1) (hv : ∀ e, ∑ b, v e b = 1)
    (hnw : ∀ e b, 0 ≤ w e b) (hnv : ∀ e b, 0 ≤ v e b)
    (hf : Fresh w p used) (hc : ClosedFresh v p C used) :
    expect v (fun ω => (T.contactScore p C F w ω)^2) ≤
      3*expect v (T.contactScore p C F w) := by
  induction T generalizing used w v with
  | done r =>
    change expect v (fun _ => (0:ℝ)^2) ≤ 3*expect v (fun _ => 0)
    rw [expect_const v hv,expect_zero]
    norm_num
  | ask e l r hl hr =>
    have he := hf e hT.1
    have hv' := hc e hT.1
    have hl' := hl (insert e used) hT.2.1 (pin w e False) (pin v e False)
      (pin_normalized w hw e False) (pin_normalized v hv e False)
      (pin_nonneg w hnw e False) (pin_nonneg v hnv e False)
      (fresh_pin w p used hf e False) (closedFresh_pin v p C used hc e False)
    have hr' := hr (insert e used) hT.2.2 (pin w e True) (pin v e True)
      (pin_normalized w hw e True) (pin_normalized v hv e True)
      (pin_nonneg w hnw e True) (pin_nonneg v hnv e True)
      (fresh_pin w p used hf e True) (closedFresh_pin v p C used hc e True)
    let a := if e ∈ C then p*delta w F e else 0
    have hsq : (fun ω => ((.ask e l r : SearchTree E R).contactScore p C F w ω)^2) =
        (fun ω => if ω e then (a+r.contactScore p C F (pin w e True) ω)^2
          else (a+l.contactScore p C F (pin w e False) ω)^2) := by
      funext ω
      change ((if e ∈ C then p*delta w F e else 0) +
        if ω e then r.contactScore p C F (pin w e True) ω
        else l.contactScore p C F (pin w e False) ω)^2 = _
      by_cases hω : ω e <;> simp only [hω,↓reduceIte,a]
    rw [hsq]
    erw [expect_prop_ite]
    rw [contact_mean_step e l r p C F w v hv,hv'.1,hv'.2]
    by_cases heC : e ∈ C
    · simp only [heC,↓reduceIte,zero_mul,one_mul,add_zero,zero_add]
      have haeq : a = p*delta w F e := ite_eq_left heC
      rw [← haeq]
      change expect (pin v e False) (fun ω => (a+l.contactScore p C F (pin w e False) ω)^2) ≤
        3*(a+expect (pin v e False) (l.contactScore p C F (pin w e False)))
      rw [expect_square_add_const _ (pin_normalized v hv e False)]
      have hmean := (contact_mean_le_prob l (insert e used) hT.2.1 p C F
        (pin w e False) (pin v e False) (pin_normalized w hw e False)
        (pin_normalized v hv e False) (pin_nonneg w hnw e False) (pin_nonneg v hnv e False)
        (fresh_pin w p used hf e False) (closedFresh_pin v p C used hc e False)).trans
          (prob_le_one _ (pin_normalized w hw e False) (pin_nonneg w hnw e False) F)
      have hd := delta_unit w hw hnw e (by rw [he.1]; exact (sub_pos.mpr hp.2).ne')
        (by rw [he.2]; exact hp.1.ne') F hF
      have ha : 0 ≤ a ∧ a ≤ 1 := by
        simp only [a,heC,↓reduceIte]
        exact ⟨mul_nonneg hp.1.le hd.1,
          (mul_le_mul_of_nonneg_left hd.2 hp.1.le).trans (by linarith [hp.2])⟩
      have hpair := mul_le_mul_of_nonneg_left hmean ha.1
      nlinarith
    · have ha : a = 0 := ite_eq_right heC
      simp only [heC,↓reduceIte,ha,zero_add]
      have hlb := mul_le_mul_of_nonneg_left hl' (sub_pos.mpr hp.2).le
      have hrb := mul_le_mul_of_nonneg_left hr' hp.1.le
      linarith

end CriticalPercolation.SearchTree

end
end

end OAI
