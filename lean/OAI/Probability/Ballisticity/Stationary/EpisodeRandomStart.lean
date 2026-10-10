import Mathlib
import OAI.Probability.Ballisticity.Estimates.StageExponentialScales
import OAI.Probability.Ballisticity.Stationary.EpisodeAdapted

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

noncomputable def randomEpisodeInitialAtlas {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor)
    (T : Environment d → ℕ)
    (hT : ∀ t : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) t)] {ω | T ω=t}) :
    EpisodeAtlas (fun ω => episodeInitial (k:=k) e f hef r sfloor hR (T ω) ω) where
  Label := ℕ
  countable := inferInstance
  chart := fun t => { episodeInitialChart e f hef r sfloor hR t with
    event := {ω | T ω=t}
    measurable_event := (rowSigma_mono (by
      intro x hx
      change dot (realPosition x) (realPosition (step e)) < ((t+1:ℕ):ℝ)
      change dot (realPosition x) (realPosition (step e)) < (t:ℝ) at hx
      exact hx.trans_le (by exact_mod_cast Nat.le_add_right t 1))) _ (hT t) }
  cover := fun ω => ⟨T ω,rfl⟩
  correct := by
    intro t ω hω
    change T ω=t at hω
    change episodeInitial (k:=k) e f hef r sfloor hR (T ω) ω = episodeInitial e f hef r sfloor hR t ω
    rw [hω]

lemma randomEpisodeInitialAtlas_partition {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (sfloor : ℝ) (hR : 0 ≤ r sfloor)
    (T : Environment d → ℕ)
    (hT : ∀ t : ℕ, MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) t)] {ω | T ω=t}) :
    (randomEpisodeInitialAtlas (k:=k) e f hef r sfloor hR T hT).IsPartition := by
  intro l m ω hl hm
  change T ω=l at hl
  change T ω=m at hm
  exact hl.symm.trans hm

noncomputable def actualEpisodeStageAtlas {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N i n : ℕ) :
    EpisodeAtlas (fun ω => episodeRun e f hef r fexp g χ b sfloor N
      (episodeInitial (k:=k) e f hef r sfloor hR
        (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) ω) ω n) :=
  (randomEpisodeInitialAtlas (k:=k) e f hef r sfloor hR
    (fun ω => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i)
    (fun t => episodeBoundary_height_event (k:=k) e f hef r fexp g χ b sfloor hR N i t)).run
      hef fexp g χ b sfloor N n

lemma actualEpisodeStageAtlas_partition {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N i n : ℕ) :
    (actualEpisodeStageAtlas (k:=k) e f hef r fexp g χ b sfloor hR N i n).IsPartition :=
  EpisodeAtlas.run_partition _ (randomEpisodeInitialAtlas_partition (k:=k) e f hef r sfloor hR _ _)
    hef fexp g χ b sfloor N n

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical Topology
namespace DirectionalTransience

lemma stage_height_dominates_growth (g χ b s : ℝ) (hg : g < χ) (hb : 0 < b)
    (hs : 1 / (Real.exp (χ*b)-Real.exp (g*b)) ≤ s) :
    s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ) := by
  have hsub : 0 < Real.exp (χ*b)-Real.exp (g*b) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_right hg hb))
  have hm := (div_le_iff₀ hsub).mp hs
  have hf := Nat.lt_floor_add_one (s*Real.exp (χ*b))
  change s*Real.exp (g*b) ≤ (⌊s*Real.exp (χ*b)⌋₊:ℝ)
  nlinarith only [hm,hf]

theorem operational_stage_parameters {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (D₀ : ℝ) (hD₀ : 0 ≤ D₀) :
    let μ := independentConditionedPairLaw ν (realPosition (step e))
    let S := commonIncrementProcess (realPosition (step e)) f 0
    let r := fluctuationRadius μ S
    ∃ fexp g χ K : ℝ, 0 < fexp ∧ 0 < g ∧ g < χ ∧ 0 < K ∧
      1/g < (1/2:ℝ)/64 ∧ (1+fexp/g)*D₀/K < (1/2:ℝ)/64 ∧
      ∃ k : ℕ, 2 ≤ k ∧ ∀ᶠ b : ℝ in atTop, 0 < b ∧ ∃ sfloor : ℝ, 1 ≤ sfloor ∧
        (∀ s, sfloor ≤ s → 0 < episodeStageH χ b s ∧
          s*Real.exp (g*b) ≤ (episodeStageH χ b s : ℝ)) ∧
        ∀ s, sfloor ≤ s → ∀ a : ℝ, ∀ π : BudgetProfile (k:=k) e f a (r s),
          environmentLaw ν (stageBadEvent e f (episodeStageH χ b s)
            (r (s*Real.exp (-fexp*b))) (r (s*Real.exp (g*b))) π.val
            (ENNReal.ofReal (Real.exp (-((k:ℝ)*b))))) ≤ ENNReal.ofReal (Real.exp (-2*K*b)) := by
  dsimp only
  obtain ⟨fexp,g,χ,K,hf,hg,hχ,hK,hgs,hKs,k,hk,hb⟩ :=
    separated_stages_with_gap ν hue e f hef htrans D₀ hD₀
  refine ⟨fexp,g,χ,K,hf,hg,hχ,hK,hgs,hKs,k,hk,?_⟩
  filter_upwards [hb] with b hb
  obtain ⟨hb,oldfloor,hold,hbound⟩ := hb
  let sfloor := max oldfloor (max 1 (1/(Real.exp (χ*b)-Real.exp (g*b))))
  have hfloor : 1 ≤ sfloor := (le_max_left _ _).trans (le_max_right _ _)
  refine ⟨hb,sfloor,hfloor,?_,?_⟩
  · intro s hs
    have hh := stage_height_dominates_growth g χ b s hχ hb
      ((le_max_right _ _).trans ((le_max_right _ _).trans hs))
    refine ⟨?_,hh⟩
    have hs0 : 0 < s := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hfloor.trans hs)
    exact_mod_cast (mul_pos hs0 (Real.exp_pos _)).trans_le hh
  · intro s hs a π
    simpa only [episodeStageH,neg_mul] using hbound s ((le_max_left _ _).trans hs) a π

end DirectionalTransience

end

end OAI
