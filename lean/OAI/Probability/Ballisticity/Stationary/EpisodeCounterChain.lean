import Mathlib
import OAI.Probability.Ballisticity.Entropy.EntropyVariational
import OAI.Probability.Ballisticity.Stationary.EpisodeRecordedAtlas
import OAI.Probability.Ballisticity.Stationary.EpisodeCountLedger

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

structure EpisodeCounter {d k : ℕ} (e f : Direction d) (r : ℝ → ℝ) where
  state : EpisodeState (k:=k) e f r
  stages : ℕ
  failures : ℕ

noncomputable def episodeCounterChain {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) : ℕ → EpisodeCounter (k:=k) e f r
  | 0 => ⟨episodeInitial e f hef r sfloor hR 0 ω,0,0⟩
  | i+1 => let p := episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let q := episodeRun e f hef r fexp g χ b sfloor N p.state ω N
    ⟨episodeInitial e f hef r sfloor hR q.height ω,
      p.stages+episodeSteps e f hef r fexp g χ b sfloor N p.state ω N,
      p.failures+episodeCount e f hef r fexp g χ b sfloor N p.state ω
        (episodeStageFails e f r fexp g χ b N) N⟩

noncomputable def episodeCounterAtlas {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N i : ℕ) :
    EpisodeRecordedAtlas (fun ω => (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).state)
      (fun ω => (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).stages)
      (fun ω => (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).failures) := by
  induction i with
  | zero => exact EpisodeRecordedAtlas.zero (episodeInitialAtlas e f hef r sfloor hR 0)
  | succ i ih => exact (ih.runFrom hef fexp g χ b sfloor N N).reinject hef sfloor hR

lemma episodeCounterAtlas_partition {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N i : ℕ) :
    (episodeCounterAtlas (k:=k) e f hef r fexp g χ b sfloor hR N i).toEpisodeAtlas.IsPartition := by
  induction i with
  | zero => exact episodeInitialAtlas_partition e f hef r sfloor hR 0
  | succ i ih => exact EpisodeRecordedAtlas.runFrom_partition _ ih hef fexp g χ b sfloor N N

lemma episodeRun_stopped {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) (hq : N ≤ q.height) (n : ℕ) :
    episodeRun e f hef r fexp g χ b sfloor N q ω n=q ∧
    episodeSteps e f hef r fexp g χ b sfloor N q ω n=0 ∧
    episodeCount e f hef r fexp g χ b sfloor N q ω (episodeStageFails e f r fexp g χ b N) n=0 := by
  have hnr : ¬EpisodeReady e f r sfloor N q := fun h => (Nat.not_lt_of_ge hq) h.1
  induction n with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih =>
    simp only [episodeRun,episodeSteps,episodeCount,ih.1,ih.2.1,ih.2.2,hnr,ite_false,false_and,add_zero,and_self]

lemma episodeCounterChain_actual {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
    (ω : Environment d) (i : ℕ) :
    let T := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let p := episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    (T<N → p.state=episodeInitial e f hef r sfloor hR T ω) ∧
    (N≤T → N≤p.state.height) ∧
    p.stages=EpisodeChainLedger.steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i ∧
    p.failures=EpisodeChainLedger.count (k:=k) e f hef r fexp g χ b sfloor hR N ω
      (episodeStageFails e f r fexp g χ b N) i := by
  dsimp only
  induction i with
  | zero => exact ⟨fun _ => rfl,fun h => h.trans (Nat.zero_le _),rfl,rfl⟩
  | succ i ih =>
    let T := episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    let p := episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    by_cases ht : T<N
    <;> dsimp only [T] at ht
    · have he := ih.1 ht
      simp only [episodeBoundary,episodeCounterChain,EpisodeChainLedger.steps,EpisodeChainLedger.count,he,ite_eq_left ht]
      refine ⟨fun _ => rfl,?_,?_,?_⟩
      · intro hh
        exact hh.trans (Nat.le_add_right _ 1)
      · rw [ih.2.2.1]
      · rw [ih.2.2.2]
    · have hp := ih.2.1 (Nat.le_of_not_lt ht)
      have hz := episodeRun_stopped e f hef r fexp g χ b sfloor N p.state ω hp N
      dsimp only [p] at hz
      simp only [episodeBoundary,episodeCounterChain,EpisodeChainLedger.steps,EpisodeChainLedger.count,ite_eq_right ht,
        hz.1,hz.2.1,hz.2.2,add_zero]
      refine ⟨fun h => False.elim (ht h),?_,ih.2.2.1,ih.2.2.2⟩
      intro _
      exact hp.trans (Nat.le_add_right _ 1)

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience
namespace EpisodeRecordedAtlas
variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}
  {q : Environment d → EpisodeState (k:=k) e f r} {J F : Environment d → ℕ}

lemma measurable_counts (A : EpisodeRecordedAtlas q J F) : Measurable (fun ω => (J ω,F ω)) := by
  apply measurable_to_countable'
  intro z
  have he : (fun ω => (J ω,F ω)) ⁻¹' {z} =
      ⋃ m : ℕ, {ω | (q ω).height=m ∧ J ω=z.1 ∧ F ω=z.2} := by
    ext ω
    constructor
    · intro h
      have hh : J ω=z.1 ∧ F ω=z.2 := Prod.mk.inj h
      exact Set.mem_iUnion.mpr ⟨(q ω).height,rfl,hh⟩
    · intro h
      obtain ⟨m,hm,hj,hf⟩ := Set.mem_iUnion.mp h
      exact Prod.ext hj hf
  rw [he]
  exact MeasurableSet.iUnion fun m => (rowSigma_le _) _ (A.count_event m z.1 z.2)

end EpisodeRecordedAtlas

lemma episode_counts_le_loops {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ) (q : EpisodeState (k:=k) e f r)
    (ω : Environment d) (test : EpisodeState (k:=k) e f r → Environment d → Prop) (n : ℕ) :
    episodeSteps e f hef r fexp g χ b sfloor N q ω n ≤ n ∧
    episodeCount e f hef r fexp g χ b sfloor N q ω test n ≤ n := by
  induction n with
  | zero => exact ⟨le_refl _,le_refl _⟩
  | succ n ih =>
    rw [episodeSteps,episodeCount]
    constructor <;> split <;> omega

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "Fail" => episodeStageFails (k:=k) e f r fexp g χ b N
local notation "J" => fun ω i => steps (k:=k) e f hef r fexp g χ b sfloor hR N ω i
local notation "C" => fun ω i => count (k:=k) e f hef r fexp g χ b sfloor hR N ω Fail i

lemma measurable_counts (i : ℕ) : Measurable (fun ω => (J ω i,C ω i)) := by
  have he : (fun ω => ((episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).stages,
      (episodeCounterChain (k:=k) e f hef r fexp g χ b sfloor hR N ω i).failures)) =
      (fun ω => (J ω i,C ω i)) := by
    funext ω
    have hh := episodeCounterChain_actual (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    exact Prod.ext hh.2.2.1 hh.2.2.2
  rw [←he]
  exact (episodeCounterAtlas (k:=k) e f hef r fexp g χ b sfloor hR N i).measurable_counts

lemma counts_bounded (ω : Environment d) (i : ℕ) : J ω i ≤ i*N ∧ C ω i ≤ i*N := by
  induction i with
  | zero => simp only [steps,count,Nat.zero_mul,le_refl,and_self]
  | succ i ih =>
    have hh := episode_counts_le_loops e f hef r fexp g χ b sfloor N
      (episodeInitial (k:=k) e f hef r sfloor hR
        (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) ω) ω Fail N
    dsimp only at ih ⊢
    rw [steps,count,Nat.succ_mul]
    constructor <;> split <;> omega

lemma counts_integrable (Q : Measure (Environment d)) [IsFiniteMeasure Q] (i : ℕ) :
    Integrable (fun ω => (J ω i:ℝ)) Q ∧ Integrable (fun ω => (C ω i:ℝ)) Q := by
  have hm := measurable_counts (k:=k) e f hef r fexp g χ b sfloor hR N i
  have hcast : Measurable (fun n : ℕ => (n:ℝ)) := measurable_of_countable _
  constructor
  · apply Entropy.integrable_of_bounded (hcast.comp hm.fst)
    refine ⟨(i*N:ℕ),fun ω => ?_⟩
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp only [Function.comp_def]
    exact_mod_cast (counts_bounded (k:=k) e f hef r fexp g χ b sfloor hR N ω i).1
  · apply Entropy.integrable_of_bounded (hcast.comp hm.snd)
    refine ⟨(i*N:ℕ),fun ω => ?_⟩
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    dsimp only [Function.comp_def]
    exact_mod_cast (counts_bounded (k:=k) e f hef r fexp g χ b sfloor hR N ω i).2

end EpisodeChainLedger
end DirectionalTransience

end

end OAI
