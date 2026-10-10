import Mathlib
import OAI.Probability.Ballisticity.Entropy.EntropyVariational
import OAI.Probability.Ballisticity.Stationary.EpisodeAdapted
import OAI.Probability.Ballisticity.Stationary.EpisodeCountLedger

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience

lemma episodeSteps_mono {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d) :
    Monotone (episodeSteps e f hef r fexp g χ b sfloor N q ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [episodeSteps]
  exact Nat.le_add_right _ _

lemma episodeSteps_pos_of_ready {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (N : ℕ)
    (q : EpisodeState (k:=k) e f r) (ω : Environment d)
    (hq : EpisodeReady e f r sfloor N q) (n : ℕ) (hn : 0 < n) :
    0 < episodeSteps e f hef r fexp g χ b sfloor N q ω n := by
  have hm := episodeSteps_mono e f hef r fexp g χ b sfloor N q ω (Nat.succ_le_of_lt hn)
  have he : episodeSteps e f hef r fexp g χ b sfloor N q ω 1=1 := by
    simp only [episodeSteps,episodeRun,hq,ite_true,zero_add]
  rw [he] at hm
  omega

lemma episodeBoundary_mono {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ) (ω : Environment d) :
    Monotone (episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [episodeBoundary]
  split
  · exact (episodeFinal_gt (k:=k) e f hef r fexp g χ b sfloor hR N _ ω).le
  · exact le_refl _

lemma episodeBoundary_measurable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
    (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N i : ℕ) :
    Measurable (fun ω => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N ω i) := by
  apply measurable_to_countable'
  intro m
  exact (rowSigma_le _) _ (episodeBoundary_height_event (k:=k) e f hef r fexp g χ b sfloor hR N i m)

namespace EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "J" => steps (k:=k) e f hef r fexp g χ b sfloor hR N

noncomputable def number (ω : Environment d) : ℕ → ℕ
  | 0 => 0
  | i+1 => number ω i+if T ω i<N then 1 else 0
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

lemma number_sum (ω : Environment d) (n : ℕ) :
    M ω n=∑ i ∈ Finset.range n, if T ω i<N then 1 else 0 := by
  induction n with
  | zero => simp only [number,Finset.range_zero,Finset.sum_empty]
  | succ n ih => rw [number,Finset.sum_range_succ,ih]

lemma number_le (ω : Environment d) (n : ℕ) : M ω n ≤ n := by
  induction n with
  | zero => exact le_refl _
  | succ n ih => rw [number]; split <;> omega

lemma number_measurable (n : ℕ) : Measurable (fun ω => M ω n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ih.add (Measurable.ite (measurableSet_lt
      (episodeBoundary_measurable (k:=k) e f hef r fexp g χ b sfloor hR N n) measurable_const)
      measurable_const measurable_const)

lemma number_stage_bound (ω : Environment d) (n : ℕ) : M ω n ≤ J ω n+1 ∧
    (T ω n<N → M ω n ≤ J ω n) := by
  induction n with
  | zero => exact ⟨by simp only [number,steps]; omega,fun _ => le_refl _⟩
  | succ n ih =>
    rw [number,steps,episodeBoundary]
    by_cases ht : T ω n<N
    · simp only [ite_eq_left ht]
      have hm := ih.2 ht
      constructor
      · omega
      · intro hp
        have hheight := episodeRun_height_mono e f hef r fexp g χ b sfloor N
          (episodeInitial (k:=k) e f hef r sfloor hR (T ω n) ω) ω N
        have hready : EpisodeReady e f r sfloor N
            (episodeInitial (k:=k) e f hef r sfloor hR (T ω n) ω) := ⟨lt_of_le_of_lt hheight hp,le_refl _⟩
        have hj := episodeSteps_pos_of_ready e f hef r fexp g χ b sfloor N _ ω hready N (Nat.zero_lt_of_lt ht)
        omega
    · simp only [ite_eq_right ht,add_zero]
      exact ⟨ih.1,fun h => False.elim (ht h)⟩

lemma number_integrable (Q : Measure (Environment d)) [IsFiniteMeasure Q] (n : ℕ) :
    Integrable (fun ω => (M ω n:ℝ)) Q := by
  apply Entropy.integrable_of_bounded ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
    (number_measurable (k:=k) e f hef r fexp g χ b sfloor hR N n))
  refine ⟨n,fun ω => ?_⟩
  dsimp only [Function.comp_def]
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω n

end EpisodeChainLedger
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical
namespace DirectionalTransience.EpisodeChainLedger
variable {d k : ℕ} (e f : Direction d) (hef : e.1 ≠ f.1)
  (r : ℝ → ℝ) (fexp g χ b sfloor : ℝ) (hR : 0 ≤ r sfloor) (N : ℕ)
local notation "T" => episodeBoundary (k:=k) e f hef r fexp g χ b sfloor hR N
local notation "M" => number (k:=k) e f hef r fexp g χ b sfloor hR N

lemma number_mono (ω : Environment d) : Monotone (M ω) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [number]
  exact Nat.le_add_right _ _

lemma number_active (ω : Environment d) (i : ℕ) (ha : T ω i<N) : M ω i=i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have hprev : T ω i<N := lt_of_le_of_lt
      (episodeBoundary_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.le_succ i)) ha
    rw [number,ite_eq_left hprev,ih hprev]

lemma number_stopped (ω : Environment d) (i : ℕ) (hi : N ≤ T ω i) (j : ℕ) : M ω (i+j)=M ω i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hn : ¬T ω (i+j)<N := not_lt.mpr (hi.trans
      (episodeBoundary_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.le_add_right _ _)))
    rw [Nat.add_succ,number,ite_eq_right hn,add_zero,ih]

lemma active_iff_lt_number (ω : Environment d) (i : ℕ) : T ω i<N ↔ i<M ω N := by
  constructor
  · intro ha
    have hi := episodeBoundary_progress (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    have hin : i<N := by omega
    have hm : M ω (i+1)=i+1 := by rw [number,ite_eq_left ha,number_active (k:=k) e f hef r fexp g χ b sfloor hR N ω i ha]
    have hh := number_mono (k:=k) e f hef r fexp g χ b sfloor hR N ω (Nat.succ_le_of_lt hin)
    change M ω (i+1) ≤ M ω N at hh
    rw [hm] at hh
    exact Nat.lt_of_succ_le hh
  · intro hm
    by_contra ha
    have hi : i<N := lt_of_lt_of_le hm (number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω N)
    have hh := number_stopped (k:=k) e f hef r fexp g χ b sfloor hR N ω i (Nat.le_of_not_lt ha) (N-i)
    rw [Nat.add_sub_of_le hi.le] at hh
    have hu := number_le (k:=k) e f hef r fexp g χ b sfloor hR N ω i
    omega

lemma number_positive (ω : Environment d) (hN : 0<N) : 0<M ω N :=
  (active_iff_lt_number (k:=k) e f hef r fexp g χ b sfloor hR N ω 0).mp hN

end DirectionalTransience.EpisodeChainLedger

end

end OAI
