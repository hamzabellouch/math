import OAI.Probability.FirstPassage.BKDyadicPaths
import Mathlib.Topology.Instances.Int
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

namespace PlanarFPP
open Filter
open scoped Topology

noncomputable def roundedSurvival (t : ℕ) (r : ℝ) : ℝ :=
  (⌊(2:ℝ)^t * Real.exp (-r)⌋₊ : ℝ)/(2:ℝ)^t

noncomputable def roundedEdgeCost (t : ℕ) (r : ℝ) : ℝ :=
  -Real.log (roundedSurvival t r)

lemma roundedSurvival_nonneg (t : ℕ) (r : ℝ) : 0 ≤ roundedSurvival t r := by
  unfold roundedSurvival
  positivity

lemma roundedSurvival_le (t : ℕ) (r : ℝ) : roundedSurvival t r ≤ Real.exp (-r) := by
  rw [roundedSurvival,div_le_iff₀ (by positivity)]
  simpa only [mul_comm] using Nat.floor_le (show 0 ≤ (2:ℝ)^t*Real.exp (-r) by positivity)

lemma roundedSurvival_tendsto (r : ℝ) :
    Tendsto (fun t => roundedSurvival t r) atTop (𝓝 (Real.exp (-r))) := by
  have h := (tendsto_nat_floor_mul_div_atTop (Real.exp_pos (-r)).le).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  simpa [roundedSurvival,Function.comp_def,mul_comm] using h

lemma roundedSurvival_eventually_pos (r : ℝ) :
    ∀ᶠ t in atTop, 0 < roundedSurvival t r :=
  (roundedSurvival_tendsto r).eventually (lt_mem_nhds (Real.exp_pos (-r)))

lemma roundedEdgeCost_ge (t : ℕ) (r : ℝ) (hp : 0 < roundedSurvival t r) :
    r ≤ roundedEdgeCost t r := by
  have h := Real.log_le_log hp (roundedSurvival_le t r)
  rw [Real.log_exp] at h
  unfold roundedEdgeCost
  linarith

lemma roundedEdgeCost_tendsto (r : ℝ) :
    Tendsto (fun t => roundedEdgeCost t r) atTop (𝓝 r) := by
  have h := ((Real.continuousAt_log (Real.exp_ne_zero (-r))).tendsto.comp
    (roundedSurvival_tendsto r)).neg
  simpa [roundedEdgeCost,Real.log_exp] using h

lemma rounded_pathCost_tendsto (w : Edge → ℝ) (p : Vertex) (ds : List Step) :
    Tendsto (fun t => pathCost (fun e => roundedEdgeCost t (w e)) p ds) atTop
      (𝓝 (pathCost w p ds)) := by
  induction ds generalizing p with
  | nil => exact tendsto_const_nhds
  | cons d ds ih => exact (roundedEdgeCost_tendsto (w (d.edge p))).add (ih _)

def RoundedPathGood (t : ℕ) (w : Edge → ℝ) (p : StrictPathWitness) : Prop :=
  (∀ e ∈ p.edges, 0 < roundedSurvival t (w e)) ∧
    pathCost (fun e => roundedEdgeCost t (w e)) p.start p.steps < p.bound

def StrictPathWitness.Good (w : Edge → ℝ) (p : StrictPathWitness) : Prop :=
  pathCost w p.start p.steps < p.bound

lemma RoundedPathGood.original {t : ℕ} {w : Edge → ℝ} {p : StrictPathWitness}
    (h : RoundedPathGood t w p) : p.Good w := by
  exact lt_of_le_of_lt (pathCost_le_of_edges p.start p.steps
    (fun e he => roundedEdgeCost_ge t (w e) (h.1 e he))) h.2

lemma StrictPathWitness.Good.eventually_rounded {w : Edge → ℝ} {p : StrictPathWitness}
    (h : p.Good w) : ∀ᶠ t in atTop, RoundedPathGood t w p := by
  have he : ∀ᶠ t in atTop, ∀ e ∈ p.edges, 0 < roundedSurvival t (w e) := by
    rw [Filter.eventually_all_finset]
    intro e _
    exact roundedSurvival_eventually_pos (w e)
  have hc := (rounded_pathCost_tendsto w p.start p.steps).eventually (gt_mem_nhds h)
  exact he.and hc

lemma strict_path_list_eventually_rounded (w : Edge → ℝ) (ps : List StrictPathWitness)
    (h : ∀ p ∈ ps, p.Good w) : ∀ᶠ t in atTop, ∀ p ∈ ps, RoundedPathGood t w p := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := (h p (List.mem_cons_self ..)).eventually_rounded
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    filter_upwards [hp,ht] with t hp ht q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact ht q hq

def StrictDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness)) (w : Edge → ℝ) : Prop :=
  ∃ ps : List StrictPathWitness,
    List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ p.Good w) ps Fs ∧
    ps.Pairwise (fun p q => Disjoint p.edges q.edges)

def RoundedDisjointPaths (S : Finset Edge) (Fs : List (Set StrictPathWitness))
    (t : ℕ) (w : Edge → ℝ) : Prop :=
  ∃ ps : List StrictPathWitness,
    List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ RoundedPathGood t w p) ps Fs ∧
    ps.Pairwise (fun p q => Disjoint p.edges q.edges)

lemma RoundedDisjointPaths.original {S : Finset Edge} {Fs : List (Set StrictPathWitness)}
    {t : ℕ} {w : Edge → ℝ} (h : RoundedDisjointPaths S Fs t w) : StrictDisjointPaths S Fs w := by
  obtain ⟨ps,hps,hd⟩ := h
  refine ⟨ps,?_,hd⟩
  exact hps.imp (fun _ _ h => ⟨h.1,h.2.1,h.2.2.original⟩)

lemma StrictDisjointPaths.eventually_rounded {S : Finset Edge} {Fs : List (Set StrictPathWitness)}
    {w : Edge → ℝ} (h : StrictDisjointPaths S Fs w) :
    ∀ᶠ t in atTop, RoundedDisjointPaths S Fs t w := by
  obtain ⟨ps,hps,hd⟩ := h
  have hg : ∀ p ∈ ps, p.Good w := by
    clear hd
    induction hps with
    | nil => simp
    | cons hp hps ih =>
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact hp.2.2
      · exact ih q hq
  filter_upwards [strict_path_list_eventually_rounded w ps hg] with t ht
  refine ⟨ps,?_,hd⟩
  clear hd hg
  induction hps with
  | nil => exact List.Forall₂.nil
  | @cons p F ps Fs hp hps ih =>
    exact List.Forall₂.cons ⟨hp.1,hp.2.1,ht p (List.mem_cons_self ..)⟩
      (ih (fun q hq => ht q (List.mem_cons_of_mem _ hq)))

theorem strict_disjoint_eventual_rounded_iff (S : Finset Edge) (Fs : List (Set StrictPathWitness))
    (w : Edge → ℝ) :
    StrictDisjointPaths S Fs w ↔ ∀ᶠ t in atTop, RoundedDisjointPaths S Fs t w := by
  constructor
  · exact StrictDisjointPaths.eventually_rounded
  · intro h
    obtain ⟨t,ht⟩ := h.exists
    exact ht.original

end PlanarFPP

end OAI
