import Mathlib
import OAI.Geometry.HyperbolicGroups.Concentration
import OAI.Geometry.HyperbolicGroups.Chernoff

namespace OAI

section
section


noncomputable section
open scoped BigOperators
open Filter Topology
namespace HyperbolicObstruction
namespace SixTable
variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

abbrev PairPositions := {rq : Fin 6 × Fin 6 // rq.1 ≠ rq.2}
instance : Fintype PairPositions :=
  inferInstanceAs (Fintype {positions : Fin 6 × Fin 6 // positions.1 ≠ positions.2})
lemma card_pairPositions : Fintype.card PairPositions = 30 := by decide

def pairTrials (r q : Fin 6) (u v : A) : Finset (Fin 6 → A) :=
  TableModel.pinCandidates {r,q} (fun i => if i = r then u else v)

omit [Nonempty A] in
lemma mem_pairTrials {r q : Fin 6} (h : r ≠ q) (u v : A) (x : Fin 6 → A) :
    x ∈ pairTrials r q u v ↔ x r = u ∧ x q = v := by
  simp [pairTrials,TableModel.pinCandidates,Ne.symm h]

omit [Nonempty A] in
lemma card_pairTrials {r q : Fin 6} (h : r ≠ q) (u v : A) :
    ((pairTrials r q u v).card : ℝ) = (Fintype.card A : ℝ)^4 := by
  rw [pairTrials,TableModel.card_pinCandidates]
  simp [h,Finset.card_insert_of_notMem]

def count (r q : Fin 6) (u v : A) (w : (Fin 6 → A) → Bool) : ℝ :=
  ∑ x ∈ pairTrials r q u v, if w x then 1 else 0

def probability (δ : ℝ) : ℝ := (Fintype.card A : ℝ)^(-3-δ)

omit [DecidableEq A] in
lemma probability_mem {δ : ℝ} (hδ : 0 ≤ δ) : probability (A := A) δ ∈ Set.Icc (0:ℝ) 1 := by
  unfold probability
  convert TableModel.powerProbability_mem
    (show (1:ℝ) ≤ Fintype.card A by exact_mod_cast Fintype.card_pos (α := A))
    (show (0:ℝ) ≤ 3+δ by linarith) using 1
  congr 1
  ring

def law (δ : ℝ) (hδ : 0 ≤ δ) : FiniteLaw ((Fin 6 → A) → Bool) :=
  FiniteLaw.bernoulliProduct (fun _ => probability (A := A) δ) (fun _ => probability_mem hδ)

lemma pair_mean (δ : ℝ) {r q : Fin 6} (h : r ≠ q) (u v : A) :
    (∑ _ ∈ pairTrials r q u v, probability (A := A) δ) = (Fintype.card A : ℝ)^(1-δ) := by
  rw [Finset.sum_const,nsmul_eq_mul,card_pairTrials h]
  have hn : 0 < (Fintype.card A : ℝ) := by exact_mod_cast Fintype.card_pos (α := A)
  rw [probability,← Real.rpow_natCast,← Real.rpow_add hn]
  congr 1
  ring

lemma centered_eq (δ : ℝ) {r q : Fin 6} (h : r ≠ q) (u v : A) (w : (Fin 6 → A) → Bool) :
    FiniteLaw.centeredCount (fun _ => probability (A := A) δ) (pairTrials r q u v) w =
      count r q u v w - (Fintype.card A : ℝ)^(1-δ) := by
  simp only [FiniteLaw.centeredCount,Finset.sum_sub_distrib,count,pair_mean δ h]

lemma count_chernoff {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    {r q : Fin 6} (h : r ≠ q) (u v : A) :
    (law (A := A) δ hδ).prob (fun w => ε*(Fintype.card A : ℝ)^(1-δ) ≤
      |count r q u v w - (Fintype.card A : ℝ)^(1-δ)|) ≤
      2*Real.exp (-ε^2*(Fintype.card A : ℝ)^(1-δ)/4) := by
  simpa only [law,centered_eq δ h,pair_mean δ h] using
    FiniteLaw.centeredCount_chernoff (fun _ : Fin 6 → A => probability (A := A) δ)
      (fun _ => probability_mem hδ) (pairTrials r q u v) hε hε2

abbrev BadPairs (δ ε : ℝ) (w : (Fin 6 → A) → Bool) : Prop :=
  ∃ rq : PairPositions, ∃ u v : A, ε*(Fintype.card A : ℝ)^(1-δ) ≤
    |count rq.val.1 rq.val.2 u v w - (Fintype.card A : ℝ)^(1-δ)|

/-- Simultaneous control of all ordered pairs in the actual single six-letter
array. No independence of different pair counts is used. -/
theorem badPairs_bound {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 < ε) (hε2 : ε ≤ 2) :
    (law (A := A) δ hδ).prob (BadPairs δ ε) ≤
      60*(Fintype.card A : ℝ)^2*Real.exp (-ε^2*(Fintype.card A : ℝ)^(1-δ)/4) := by
  classical
  apply (FiniteLaw.prob_exists_le (J := PairPositions) (law (A := A) δ hδ)
    (fun rq w => ∃ u v : A, ε*(Fintype.card A : ℝ)^(1-δ) ≤
      |count rq.val.1 rq.val.2 u v w - (Fintype.card A : ℝ)^(1-δ)|)).trans
  calc
    _ ≤ ∑ rq : PairPositions, ∑ u : A, ∑ v : A,
        2*Real.exp (-ε^2*(Fintype.card A : ℝ)^(1-δ)/4) := by
      apply Finset.sum_le_sum
      intro rq _
      apply (FiniteLaw.prob_exists_le (J := A) (law (A := A) δ hδ)
        (fun u w => ∃ v : A, ε*(Fintype.card A : ℝ)^(1-δ) ≤
          |count rq.val.1 rq.val.2 u v w - (Fintype.card A : ℝ)^(1-δ)|)).trans
      apply Finset.sum_le_sum
      intro u _
      apply (FiniteLaw.prob_exists_le (J := A) (law (A := A) δ hδ)
        (fun v w => ε*(Fintype.card A : ℝ)^(1-δ) ≤
          |count rq.val.1 rq.val.2 u v w - (Fintype.card A : ℝ)^(1-δ)|)).trans
      exact Finset.sum_le_sum fun v _ => count_chernoff hδ hε hε2 rq.property u v
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_pairPositions]; ring

lemma badPairs_rate_tendsto {δ ε : ℝ} (hδ : δ < 1) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => 60*(N:ℝ)^2*Real.exp (-ε^2*(N:ℝ)^(1-δ)/4)) atTop (𝓝 0) := by
  have ha : 0 < 1-δ := sub_pos.mpr hδ
  have hb : 0 < ε^2/4 := by positivity
  have hn := (tendsto_rpow_atTop ha).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2/(1-δ)) (ε^2/4) hb).comp hn
  have he (N : ℕ) : (((N:ℝ)^(1-δ))^(2/(1-δ))) = (N:ℝ)^2 := by
    rw [← Real.rpow_mul (Nat.cast_nonneg _)]
    rw [show (1-δ)*(2/(1-δ)) = 2 by field_simp]
    norm_cast
  have hh' := hh.const_mul 60
  simp only [mul_zero] at hh'
  apply hh'.congr
  intro N
  dsimp only [Function.comp_def]
  rw [he]
  rw [show -(ε^2/4)*(N:ℝ)^(1-δ) = -ε^2*(N:ℝ)^(1-δ)/4 by ring]
  ring

end SixTable
end HyperbolicObstruction
end
end

section

end
end

end OAI
