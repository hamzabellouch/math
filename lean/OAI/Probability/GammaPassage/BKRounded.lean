import OAI.Probability.GammaPassage.BKDyadic
import OAI.Probability.GammaPassage.BKBitLaw
import OAI.Probability.GammaPassage.PathIntegrability

namespace OAI

namespace GammaFPP.BK
open PlanarFPP MeasureTheory ProbabilityTheory Set Finset Filter
open scoped Topology ENNReal
variable {shape rate : ℝ} (hs : 0 < shape) (hr : 0 < rate)

def RoundedGood (t : ℕ) (w : Edge → ℝ) (p : StrictPathWitness) : Prop :=
  (∀ e ∈ p.edges, 0 < gammaRoundedSurvival (shape := shape) (rate := rate) t (w e)) ∧
    pathCost (fun e => gammaRoundedCost hs hr t (w e)) p.start p.steps < p.bound

lemma rounded_original {t : ℕ} {w : Edge → ℝ} {p : StrictPathWitness}
    (hw : ∀ e, 0 ≤ w e) (h : RoundedGood hs hr t w p) : p.Good w := by
  exact lt_of_le_of_lt (pathCost_le_of_edges p.start p.steps
    (fun e he => gammaRoundedCost_ge hs hr t (hw e) (h.1 e he))) h.2

lemma rounded_path_tendsto (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (p : Vertex) (ds : List Step) :
    Tendsto (fun t => pathCost (fun e => gammaRoundedCost hs hr t (w e)) p ds)
      atTop (𝓝 (pathCost w p ds)) := by
  induction ds generalizing p with
  | nil => exact tendsto_const_nhds
  | cons d ds ih => exact (gammaRoundedCost_tendsto hs hr (hw (d.edge p))).add (ih _)

lemma eventually_rounded {w : Edge → ℝ} (hw : ∀ e, 0 ≤ w e)
    {p : StrictPathWitness} (h : p.Good w) :
    ∀ᶠ t in atTop, RoundedGood hs hr t w p := by
  have he : ∀ᶠ t in atTop, ∀ e ∈ p.edges,
      0 < gammaRoundedSurvival (shape := shape) (rate := rate) t (w e) := by
    rw [Filter.eventually_all_finset]
    intro e _
    exact gammaRoundedSurvival_eventually_pos hs hr (hw e)
  exact he.and ((rounded_path_tendsto hs hr w hw p.start p.steps).eventually (gt_mem_nhds h))

def RoundedDisjoint (S : Finset Edge) (Fs : List (Set StrictPathWitness))
    (t : ℕ) (w : Edge → ℝ) : Prop :=
  ∃ ps : List StrictPathWitness,
    List.Forall₂ (fun p F => p ∈ F ∧ p.edges ⊆ S ∧ RoundedGood hs hr t w p) ps Fs ∧
    ps.Pairwise (fun p q => Disjoint p.edges q.edges)

lemma rounded_disjoint_original {S : Finset Edge} {Fs : List (Set StrictPathWitness)}
    {t : ℕ} {w : Edge → ℝ} (hw : ∀ e, 0 ≤ w e)
    (h : RoundedDisjoint hs hr S Fs t w) : StrictDisjointPaths S Fs w := by
  obtain ⟨ps,hps,hd⟩ := h
  exact ⟨ps,hps.imp (fun _ _ hp => ⟨hp.1,hp.2.1,rounded_original hs hr hw hp.2.2⟩),hd⟩

lemma list_eventually_rounded (w : Edge → ℝ) (hw : ∀ e, 0 ≤ w e)
    (ps : List StrictPathWitness) (h : ∀ p ∈ ps, p.Good w) :
    ∀ᶠ t in atTop, ∀ p ∈ ps, RoundedGood hs hr t w p := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    have hp := eventually_rounded hs hr hw (h p (List.mem_cons_self ..))
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    filter_upwards [hp,ht] with t hp ht q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hp
    · exact ht q hq

lemma disjoint_eventually_rounded {S : Finset Edge} {Fs : List (Set StrictPathWitness)}
    {w : Edge → ℝ} (hw : ∀ e, 0 ≤ w e) (h : StrictDisjointPaths S Fs w) :
    ∀ᶠ t in atTop, RoundedDisjoint hs hr S Fs t w := by
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
  filter_upwards [list_eventually_rounded hs hr w hw ps hg] with t ht
  refine ⟨ps,?_,hd⟩
  clear hd hg
  induction hps with
  | nil => exact List.Forall₂.nil
  | @cons p F ps Fs hp hps ih =>
    exact List.Forall₂.cons ⟨hp.1,hp.2.1,ht p (List.mem_cons_self ..)⟩
      (ih (fun q hq => ht q (List.mem_cons_of_mem _ hq)))

variable {Ω : Type*} {τ : Edge → Ω → ℝ}

lemma cell_survival {S : Finset Edge} {t : ℕ} {x : Finset (Edge × Fin t)}
    {ω : Ω} (hc : ω ∈ gammaDyadicRankCell shape rate τ S t x)
    {e : Edge} (he : e ∈ S) :
    gammaRoundedSurvival (shape := shape) (rate := rate) t (τ e ω) =
      dyadicSurvival t x e := by
  rw [gammaRoundedSurvival, hc e he, dyadicSurvival_eq_rank]

lemma cell_path_iff {S : Finset Edge} {t : ℕ} {x : Finset (Edge × Fin t)}
    {ω : Ω} (hc : ω ∈ gammaDyadicRankCell shape rate τ S t x)
    (p : StrictPathWitness) (hp : p.edges ⊆ S) :
    RoundedGood hs hr t (fun e => τ e ω) p ↔
      BitGood (gammaSurvivalQuantile hs hr) t x p := by
  have heq : ∀ e ∈ p.edges,
      gammaRoundedSurvival (shape := shape) (rate := rate) t (τ e ω) =
        dyadicSurvival t x e := fun e he => cell_survival hc (hp he)
  have hh := pathCost_eq_of_agree
    (fun e => gammaRoundedCost hs hr t (τ e ω))
    (fun e => gammaSurvivalQuantile hs hr (dyadicSurvival t x e))
    p.start p.steps (fun e he => congrArg (gammaSurvivalQuantile hs hr) (heq e he))
  unfold RoundedGood BitGood
  rw [hh]
  apply and_congr_left
  intro _
  exact forall_congr' (fun e => forall_congr' (fun he => by rw [heq e he]))

/-- Every guarded edge has finite extended cost; zero rank remains infinity. -/
lemma rounded_guard_is_finite (t : ℕ) {w : Edge → ℝ} (hw : ∀ e, 0 ≤ w e)
    (p : StrictPathWitness) :
    (∀ e ∈ p.edges, gammaSurvivalQuantileExtended hs hr
      (gammaRoundedSurvival (shape := shape) (rate := rate) t (w e)) ≠ ⊤) ↔
    (∀ e ∈ p.edges, 0 < gammaRoundedSurvival (shape := shape) (rate := rate) t (w e)) := by
  exact forall_congr' (fun e => forall_congr' (fun _ =>
    gammaRoundedSurvival_finite_iff hs hr t (hw e)))
end GammaFPP.BK

end OAI
