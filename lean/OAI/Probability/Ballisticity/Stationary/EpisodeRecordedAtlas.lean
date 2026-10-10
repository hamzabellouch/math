import Mathlib
import OAI.Probability.Ballisticity.Stationary.EpisodeAdapted
import OAI.Probability.Ballisticity.Stationary.LocalEpisodeLog
import OAI.Probability.Ballisticity.Estimates.StageClassification

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

structure EpisodeRecordedAtlas {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
    (q : Environment d → EpisodeState (k:=k) e f r) (J F : Environment d → ℕ)
    extends EpisodeAtlas q where
  stages : Label → ℕ
  failures : Label → ℕ
  stages_correct : ∀ l ω, ω∈(chart l).event → J ω=stages l
  failures_correct : ∀ l ω, ω∈(chart l).event → F ω=failures l

namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

noncomputable def zero (A : EpisodeAtlas q) : EpisodeRecordedAtlas q (fun _ => 0) (fun _ => 0) where
  toEpisodeAtlas := A
  stages := fun _ => 0
  failures := fun _ => 0
  stages_correct := fun _ _ _ => rfl
  failures_correct := fun _ _ _ => rfl

noncomputable def advance (A : EpisodeRecordedAtlas q J F) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N : ℕ) :
    EpisodeRecordedAtlas
      (fun ω => if EpisodeReady e f r sfloor N (q ω) then episodeStageNext e f hef r fexp g χ b N (q ω) ω else q ω)
      (fun ω => J ω+if EpisodeReady e f r sfloor N (q ω) then 1 else 0)
      (fun ω => F ω+if EpisodeReady e f r sfloor N (q ω) ∧ episodeStageFails e f r fexp g χ b N (q ω) ω then 1 else 0) := by
  have := A.countable
  refine { Label := A.Label×Option (ℕ×Bool×Bool)
           countable := inferInstance
           chart := fun l => (A.chart l.1).countedBranch hef fexp g χ b sfloor N l.2
           cover := ?_
           correct := ?_
           stages := fun l => A.stages l.1+if l.2.isSome then 1 else 0
           failures := fun l => A.failures l.1+if (l.2.map (fun z => z.2.2)).getD false then 1 else 0
           stages_correct := ?_
           failures_correct := ?_ }
  · intro ω
    obtain ⟨l,hl⟩ := A.cover ω
    obtain ⟨j,hj⟩ := (A.chart l).countedBranch_covers hef fexp g χ b sfloor N ω hl
    exact ⟨(l,j),hj⟩
  · intro l ω hω
    obtain ⟨hl,hnext⟩ := (A.chart l.1).countedBranch_state hef fexp g χ b sfloor N ω l.2 hω
    rw [A.correct l.1 ω hl]
    exact hnext.symm
  · intro l ω hω
    have hl := ((A.chart l.1).countedBranch_state hef fexp g χ b sfloor N ω l.2 hω).1
    rw [A.stages_correct l.1 ω hl,A.correct l.1 ω hl]
    exact congrArg (A.stages l.1+ ·) (((A.chart l.1).countedBranch_record hef fexp g χ b sfloor N ω l.2 hω).1)
  · intro l ω hω
    have hl := ((A.chart l.1).countedBranch_state hef fexp g χ b sfloor N ω l.2 hω).1
    rw [A.failures_correct l.1 ω hl,A.correct l.1 ω hl]
    exact congrArg (A.failures l.1+ ·) (((A.chart l.1).countedBranch_record hef fexp g χ b sfloor N ω l.2 hω).2)

lemma advance_partition (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition)
    (hef : e.1 ≠ f.1) (fexp g χ b sfloor : ℝ) (N : ℕ) :
    (A.advance hef fexp g χ b sfloor N).toEpisodeAtlas.IsPartition := by
  rintro ⟨l,j⟩ ⟨m,h⟩ ω hl hm
  have hl₀ := ((A.chart l).countedBranch_state hef fexp g χ b sfloor N ω j hl).1
  have hm₀ := ((A.chart m).countedBranch_state hef fexp g χ b sfloor N ω h hm).1
  have he := hA l m ω hl₀ hm₀
  subst m
  exact Prod.ext rfl ((A.chart l).countedBranch_unique hef fexp g χ b sfloor N ω j h hl hm)

lemma count_event (A : EpisodeRecordedAtlas q J F) (m j h : ℕ) :
    MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) m)]
      {ω | (q ω).height=m ∧ J ω=j ∧ F ω=h} := by
  have := A.countable
  have he : {ω | (q ω).height=m ∧ J ω=j ∧ F ω=h} =
      ⋃ l : {l : A.Label // (A.chart l).height=m ∧ A.stages l=j ∧ A.failures l=h}, (A.chart l.val).event := by
    ext ω
    constructor
    · rintro ⟨hm,hj,hf⟩
      obtain ⟨l,hl⟩ := A.cover ω
      refine Set.mem_iUnion.mpr ⟨⟨l,?_,?_,?_⟩,hl⟩
      · rw [A.correct l ω hl] at hm
        exact hm
      · exact (A.stages_correct l ω hl).symm.trans hj
      · exact (A.failures_correct l ω hl).symm.trans hf
    · intro hh
      obtain ⟨l,hl⟩ := Set.mem_iUnion.mp hh
      change (q ω).height=m ∧ J ω=j ∧ F ω=h
      rw [A.correct l ω hl,A.stages_correct l ω hl,A.failures_correct l ω hl]
      exact l.property
  rw [he]
  apply MeasurableSet.iUnion
  intro l
  have hm := (A.chart l.val).measurable_event
  rwa [l.property.1] at hm

noncomputable def run (A : EpisodeAtlas q) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N n : ℕ) :
    EpisodeRecordedAtlas
      (fun ω => episodeRun e f hef r fexp g χ b sfloor N (q ω) ω n)
      (fun ω => episodeSteps e f hef r fexp g χ b sfloor N (q ω) ω n)
      (fun ω => episodeCount e f hef r fexp g χ b sfloor N (q ω) ω
        (episodeStageFails e f r fexp g χ b N) n) := by
  induction n with
  | zero => exact zero A
  | succ n ih => exact ih.advance hef fexp g χ b sfloor N

lemma run_partition (A : EpisodeAtlas q) (hA : A.IsPartition) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N n : ℕ) :
    (run A hef fexp g χ b sfloor N n).toEpisodeAtlas.IsPartition := by
  induction n with
  | zero => exact hA
  | succ n ih => exact advance_partition _ ih hef fexp g χ b sfloor N

end EpisodeRecordedAtlas
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

noncomputable def reinject (A : EpisodeRecordedAtlas q J F) (hef : e.1 ≠ f.1)
    (sfloor : ℝ) (hR : 0 ≤ r sfloor) :
    EpisodeRecordedAtlas (fun ω => episodeInitial (k:=k) e f hef r sfloor hR (q ω).height ω) J F where
  Label := A.Label
  countable := A.countable
  chart := fun l => { episodeInitialChart e f hef r sfloor hR (A.chart l).height with
    event := (A.chart l).event
    measurable_event := (rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < (((A.chart l).height+1:ℕ):ℝ)
      change dot (realPosition x) (realPosition (step e)) < ((A.chart l).height:ℝ) at hx
      exact hx.trans_le (by exact_mod_cast Nat.le_add_right (A.chart l).height 1))) _ (A.chart l).measurable_event }
  cover := A.cover
  correct := by
    intro l ω hω
    change episodeInitial e f hef r sfloor hR (q ω).height ω =
      episodeInitial e f hef r sfloor hR (A.chart l).height ω
    rw [A.correct l ω hω]
    rfl
  stages := A.stages
  failures := A.failures
  stages_correct := A.stages_correct
  failures_correct := A.failures_correct

lemma reinject_partition (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition)
    (hef : e.1 ≠ f.1) (sfloor : ℝ) (hR : 0 ≤ r sfloor) :
    (A.reinject hef sfloor hR).toEpisodeAtlas.IsPartition := hA

noncomputable def runFrom (A : EpisodeRecordedAtlas q J F) (hef : e.1 ≠ f.1)
    (fexp g χ b sfloor : ℝ) (N n : ℕ) :
    EpisodeRecordedAtlas
      (fun ω => episodeRun e f hef r fexp g χ b sfloor N (q ω) ω n)
      (fun ω => J ω+episodeSteps e f hef r fexp g χ b sfloor N (q ω) ω n)
      (fun ω => F ω+episodeCount e f hef r fexp g χ b sfloor N (q ω) ω
        (episodeStageFails e f r fexp g χ b N) n) := by
  induction n with
  | zero => exact A
  | succ n ih =>
    let B := ih.advance hef fexp g χ b sfloor N
    refine { toEpisodeAtlas := B.toEpisodeAtlas
             stages := B.stages
             failures := B.failures
             stages_correct := ?_
             failures_correct := ?_ }
    · intro l ω hω
      rw [episodeSteps,←Nat.add_assoc]
      exact B.stages_correct l ω hω
    · intro l ω hω
      rw [episodeCount,←Nat.add_assoc]
      exact B.failures_correct l ω hω

lemma runFrom_partition (A : EpisodeRecordedAtlas q J F) (hA : A.toEpisodeAtlas.IsPartition)
    (hef : e.1 ≠ f.1) (fexp g χ b sfloor : ℝ) (N n : ℕ) :
    (A.runFrom hef fexp g χ b sfloor N n).toEpisodeAtlas.IsPartition := by
  induction n with
  | zero => exact hA
  | succ n ih =>
    exact advance_partition _ ih hef fexp g χ b sfloor N

end EpisodeRecordedAtlas
end DirectionalTransience

end

end OAI
