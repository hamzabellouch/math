import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeCharts
import OAI.Probability.Ballisticity.Stationary.EpisodeAdapted
import OAI.Probability.Ballisticity.Estimates.StageClassification
import OAI.Probability.Ballisticity.Coupling.FreshStages

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeChart
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

lemma actual_failure_bound (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (c : EpisodeChart (k:=k) e f r) (fexp g χ b : ℝ) (N : ℕ)
    (ht : c.height<N) (hH : 0 < episodeStageH χ b c.scale) (δ : ℝ≥0∞)
    (hbound : ∀ π : BudgetProfile (k:=k) e f c.height (r c.scale),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b c.scale)
        (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ δ)
    (A : Set (Environment d))
    (hA : MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) c.height)] A) :
    environmentLaw ν (A ∩ {ω | episodeStageFails e f r fexp g χ b N (c.state ω) ω}) ≤
      δ*environmentLaw ν A := by
  have hb := fresh_stage_bound ν e f c.height (r c.scale)
    (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b)))
    (episodeStageH χ b c.scale) (ENNReal.ofReal (Real.exp (-((k:ℝ)*b)))) δ
    c.profile c.measurable_profile (fun η => hbound (c.profile η)) A hA
  apply le_trans (measure_mono ?_) hb
  intro ω hω
  refine ⟨hω.1,?_⟩
  have hs := stopped_stage_failure_subset e f c.height
    (r (c.scale*Real.exp (-fexp*b))) (r (c.scale*Real.exp (g*b))) ((k:ℝ)*b)
    c.layerProfile (episodeStageH χ b c.scale) (N-c.height) hH (by omega)
  apply hs
  exact hω.2

end EpisodeChart
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r}

lemma past_inter_chart (A : EpisodeAtlas q) (B : Set (Environment d))
    (hB : ∀ m : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      (B ∩ {ω | (q ω).height=m})) (l : A.Label) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) (A.chart l).height)]
      (B ∩ (A.chart l).event) := by
  have he : B ∩ (A.chart l).event =
      (B ∩ {ω | (q ω).height=(A.chart l).height}) ∩ (A.chart l).event := by
    ext ω
    constructor
    · rintro ⟨hω,hl⟩
      refine ⟨⟨hω,?_⟩,hl⟩
      change (q ω).height=(A.chart l).height
      rw [A.correct l ω hl]
      rfl
    · rintro ⟨⟨hω,_⟩,hl⟩
      exact ⟨hω,hl⟩
  rw [he]
  exact (hB _).inter (A.chart l).measurable_event

lemma actual_failure_bound (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (A : EpisodeAtlas q) (hpart : A.IsPartition) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (hH : ∀ s, sfloor ≤ s → 0 < episodeStageH χ b s) (δ : ℝ≥0∞)
    (hbound : ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
      environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
        (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
        (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ δ)
    (B : Set (Environment d))
    (hB : ∀ m : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      (B ∩ {ω | (q ω).height=m})) :
    environmentLaw ν (B ∩ {ω | EpisodeReady e f r sfloor N (q ω) ∧
      episodeStageFails e f r fexp g χ b N (q ω) ω}) ≤
      δ*environmentLaw ν (B ∩ {ω | EpisodeReady e f r sfloor N (q ω)}) := by
  let := A.countable
  let L := {l : A.Label // (A.chart l).height < N ∧ sfloor ≤ (A.chart l).scale}
  let D : L → Set (Environment d) := fun l => B ∩ (A.chart l.val).event
  let E : L → Set (Environment d) := fun l => D l ∩
    {ω | episodeStageFails e f r fexp g χ b N ((A.chart l.val).state ω) ω}
  have hD (l : L) : MeasurableSet (D l) :=
    (rowSigma_le _) _ (A.past_inter_chart B hB l.val)
  have hDj : Pairwise (fun l m : L => Disjoint (D l) (D m)) := by
    intro l m hne
    apply Set.disjoint_left.mpr
    intro ω hl hm
    exact hne (Subtype.ext (hpart l.val m.val ω hl.2 hm.2))
  have hUB : (⋃ l : L, D l) = B ∩ {ω | EpisodeReady e f r sfloor N (q ω)} := by
    ext ω
    constructor
    · intro hh
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hh
      refine ⟨hl.1,?_⟩
      change EpisodeReady e f r sfloor N (q ω)
      rw [A.correct l.val ω hl.2]
      exact l.property
    · rintro ⟨hω,hr⟩
      obtain ⟨l,hl⟩ := A.cover ω
      have hlr : (A.chart l).height < N ∧ sfloor ≤ (A.chart l).scale := by
        change EpisodeReady e f r sfloor N ((A.chart l).state ω)
        rw [←A.correct l ω hl]
        exact hr
      exact Set.mem_iUnion.mpr ⟨⟨l,hlr⟩,hω,hl⟩
  have hUE : (⋃ l : L, E l) = B ∩ {ω | EpisodeReady e f r sfloor N (q ω) ∧
      episodeStageFails e f r fexp g χ b N (q ω) ω} := by
    ext ω
    constructor
    · intro hh
      obtain ⟨l,hl,hf⟩ := Set.mem_iUnion.mp hh
      refine ⟨hl.1,?_⟩
      change EpisodeReady e f r sfloor N (q ω) ∧ episodeStageFails e f r fexp g χ b N (q ω) ω
      rw [A.correct l.val ω hl.2]
      exact ⟨l.property,hf⟩
    · rintro ⟨hω,hr,hf⟩
      have hmem : ω∈⋃ l : L, D l := by rw [hUB]; exact ⟨hω,hr⟩
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hmem
      refine Set.mem_iUnion.mpr ⟨l,hl,?_⟩
      change episodeStageFails e f r fexp g χ b N ((A.chart l.val).state ω) ω
      rw [←A.correct l.val ω hl.2]
      exact hf
  calc
    _ = environmentLaw ν (⋃ l : L, E l) := congrArg _ hUE.symm
    _ ≤ ∑' l : L, environmentLaw ν (E l) := measure_iUnion_le _
    _ ≤ ∑' l : L, δ*environmentLaw ν (D l) := ENNReal.tsum_le_tsum (fun l =>
      (A.chart l.val).actual_failure_bound ν fexp g χ b N l.property.1
        (hH _ l.property.2) δ (hbound _ l.property.2 _) (D l) (A.past_inter_chart B hB l.val))
    _ = δ*(∑' l : L, environmentLaw ν (D l)) := ENNReal.tsum_mul_left
    _ = δ*environmentLaw ν (⋃ l : L, D l) := congrArg (δ* ·) (measure_iUnion hDj hD).symm
    _ = _ := congrArg (fun Z => δ*environmentLaw ν Z) hUB

end EpisodeAtlas
end DirectionalTransience

end

end OAI
