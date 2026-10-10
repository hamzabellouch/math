import Mathlib
import OAI.Probability.Ballisticity.Estimates.BufferRootRetention
import OAI.Probability.Ballisticity.Walk.BufferHistoryBracket
import OAI.Probability.Ballisticity.Estimates.RawPairMassComposition

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter Function
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma buffer_all_height_retention {d : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    {R : ℝ} (hR : 0 ≤ R) (a ε α g : ℝ) {κ : ℝ≥0}
    (hκpos : 0 < κ) (hκ1 : κ ≤ 1) (hg : 0 < g) (hg1 : g ≤ 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (hα : 0 ≤ α)
    (H : ℝ → ℕ) (hH : ∀ r, 0 < H r)
    (x : Lattice d × Lattice d) (hx : x ∈ PairAtHeight (realPosition (step e)) a)
    (ω : Environment d) (hκ : ∀ y u, κ ≤ (ω y).1 u) (t : ℕ) :
    ∃ n : ℕ, let l := (bufferHistory e f hef R (signedCoordinate f (x.2-x.1)) ε α g κ H hH
        (bufferRootNode e f hef R a x hx) ω n);
      bufferWordHeight l ≤ t ∧
      ((κ:ℝ≥0∞)^(⌈R⌉₊+2)*(bufferRetentionCost R g κ)^n)*((κ:ℝ≥0∞)^2*ENNReal.ofReal g) ≤
        rawPairEndpointLaw (realPosition (step e)) (t+1) ω x
          {y | signedCoordinate f (x.2-x.1) ≤ signedCoordinate f (y.2-y.1)} := by
  let z := signedCoordinate f (x.2-x.1)
  let root := bufferRootNode e f hef R a x hx
  obtain ⟨n,hnt,hnt'⟩ := bufferHistory_bracket e f hef R z ε α g κ H hH root ω t
  let l := bufferHistory e f hef R z ε α g κ H hH root ω n
  change bufferWordHeight l ≤ t at hnt
  let N := bufferNodeAt e f hef R z ε α g κ H hH root l
  have ha : ω ∈ N.active := by
    rw [bufferNodeAt_active_iff_history,bufferHistory_length]
    exact ⟨Set.mem_univ _,rfl⟩
  have hv := bufferNodeAt_valid e f hef hR z ε α g hκpos hκ1 hg hg1 hε H hH root le_rfl
    (bufferRootNode_valid e f hef R a x hx κ) l
  obtain ⟨hp,hgap⟩ := hv ω hκ ha
  have := hp
  have hnR : 0 ≤ N.radius := hR.trans (bufferNodeAt_radius e f hef R z ε α g κ H hH root le_rfl l)
  have hret := bufferNodeAt_root_retained e f hef hR a ε α g hκpos hκ1 hg hg1 hε hε1 hα
    H hH x hx l ω hκ ha
  have hj : t-bufferWordHeight l ≤ bufferFirstFailure (realPosition (step e)) f N.level
      (z+(1-ε)*N.radius) g N.law (H N.radius) ω := by
    change t < _ at hnt'
    simp only [bufferHistory,bufferWordHeight] at hnt'
    change t < (bufferNodeDecision e f z ε α g H N ω).1+1+bufferWordHeight l at hnt'
    change t < bufferFirstFailure (realPosition (step e)) f N.level (z+(1-ε)*N.radius) g N.law (H N.radius) ω+1+bufferWordHeight l at hnt'
    omega
  have hm := bufferPartialStage_mass e f N.level z N.radius ε α g N.law (hH N.radius) ω
    (fun y => hκ y e) hκ1 hg1 hnR hε hε1 hα hgap (t-bufferWordHeight l) hj
  have hb := rawPair_gap_mass_composition e f (1+bufferWordHeight l) (t-bufferWordHeight l) ω x (N.law ω).val
    ((κ:ℝ≥0∞)^(⌈R⌉₊+2)*(bufferRetentionCost R g κ)^l.length) ((κ:ℝ≥0∞)^2*ENNReal.ofReal g) z hret hm
  have hh : 1+bufferWordHeight l+(t-bufferWordHeight l)=t+1 := by omega
  have hlen : l.length=n := bufferHistory_length e f hef R z ε α g κ H hH root ω n
  refine ⟨n,hnt,?_⟩
  simpa only [hh,hlen] using hb
end DirectionalTransience

end

end

end OAI
