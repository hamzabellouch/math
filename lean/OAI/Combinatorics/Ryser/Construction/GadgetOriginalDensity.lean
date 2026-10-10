import OAI.Combinatorics.Ryser.Construction.GadgetConcentration
import OAI.Combinatorics.Ryser.Construction.GadgetOriginalExpectation
import OAI.Combinatorics.Ryser.Construction.DeletionLines
import OAI.Combinatorics.Ryser.LineCover.SurvivalNumerics
import OAI.Combinatorics.Ryser.LineCover.TailNumerics
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Lean.Elab.Tactic.Omega

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Construction

open Filter Topology

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

theorem prob_originalLineCount_lt_five (hq : 2048 ≤ Fintype.card k)
    (d : NonzeroSlope k) (z : k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => originalLineCount a d z < 5) ≤
      Real.exp (-(Fintype.card k : ℝ) / 2048) := by
  classical
  let q : ℝ := Fintype.card k
  have hqR : 2048 ≤ q := by
    dsimp only [q]
    exact_mod_cast hq
  have hq0 : 0 < q := by linarith
  have hcoordinates : (Fintype.card (NonzeroSlope k) : ℝ) ≤ q := by
    dsimp only [q]
    exact_mod_cast Fintype.card_le_of_injective
      (fun d : NonzeroSlope k => d.val) Subtype.val_injective
  have hmean : q / 4 ≤
      (FiniteLaw.uniform (GadgetOutcome k)).expectation (fun a => originalLineCount a d z) := by
    have hm := LineCover.quarter_mul_le_survival_mean (Fintype.card k) (by omega)
    rw [← expectation_originalLineCount d z, FiniteLaw.pi_uniform] at hm
    exact hm
  have htail := uniform_coordinate_concentration
    (fun a : GadgetOutcome k => originalLineCount a d z)
    2 2 (4 * q) (q / 8) (by norm_num) (by positivity) (by positivity)
    (fun i a x => originalLineCount_update_abs_le a d z i x)
    (by norm_num) (by nlinarith)
  have hratio : (q / 8) ^ 2 / (4 * q) = q / 256 := by
    field_simp [hq0.ne']; ring
  have hmin : min ((q / 8) ^ 2 / (4 * q)) ((q / 8) / 2) = q / 256 := by
    rw [hratio]
    apply min_eq_left
    linarith
  rw [hmin] at htail
  have hexponent : -(1 / 4 : ℝ) * (q / 256) = -q / 1024 := by ring
  rw [hexponent] at htail
  have hbad :
      (FiniteLaw.uniform (GadgetOutcome k)).prob (fun a => originalLineCount a d z < 5) ≤
      (FiniteLaw.uniform (GadgetOutcome k)).prob
        (fun a => q / 8 ≤ |originalLineCount a d z -
          (FiniteLaw.uniform (GadgetOutcome k)).expectation
            (fun a => originalLineCount a d z)|) := by
    apply FiniteLaw.prob_mono
    intro a ha
    have habs := neg_le_abs (originalLineCount a d z -
      (FiniteLaw.uniform (GadgetOutcome k)).expectation (fun a => originalLineCount a d z))
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp (q / 2048) := by
    have he := Real.add_one_le_exp (q / 2048)
    linarith
  rw [FiniteLaw.pi_uniform]
  change _ ≤ Real.exp (-q / 2048)
  calc
    _ ≤ 2 * Real.exp (-q / 1024) := hbad.trans htail
    _ ≤ Real.exp (q / 2048) * Real.exp (-q / 1024) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-q / 2048) := by
      rw [← Real.exp_add]
      congr 1
      ring

theorem not_originalLineDensity_imp_exists_small_count (a : GadgetOutcome k)
    (ha : ¬ OriginalLineDensity a) :
    ∃ j : NonzeroSlope k × k, originalLineCount a j.1 j.2 < 5 := by
  classical
  simp only [OriginalLineDensity, not_forall, not_le] at ha
  obtain ⟨d, z, hz, hcard⟩ := ha
  refine ⟨(d, z), ?_⟩
  rw [originalLineCount_eq_retained_filter_card a d z hz]
  exact_mod_cast hcard

theorem prob_not_originalLineDensity_le (hq : 2048 ≤ Fintype.card k) :
    (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        (fun a => ¬ OriginalLineDensity a) ≤
      (Fintype.card k : ℝ) ^ 2 * Real.exp (-(Fintype.card k : ℝ) / 2048) := by
  classical
  let μ := FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)
  have htests : (Fintype.card (NonzeroSlope k × k) : ℝ) ≤ (Fintype.card k : ℝ) ^ 2 := by
    rw [Fintype.card_prod, Nat.cast_mul]
    have hc : (Fintype.card (NonzeroSlope k) : ℝ) ≤ (Fintype.card k : ℝ) := by
      exact_mod_cast Fintype.card_le_of_injective
        (fun d : NonzeroSlope k => d.val) Subtype.val_injective
    simpa only [pow_two] using
      mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg (Fintype.card k))
  calc
    _ ≤ μ.prob (fun a => ∃ j : NonzeroSlope k × k, originalLineCount a j.1 j.2 < 5) :=
      μ.prob_mono not_originalLineDensity_imp_exists_small_count
    _ ≤ ∑ j : NonzeroSlope k × k,
        μ.prob (fun a => originalLineCount a j.1 j.2 < 5) :=
      μ.prob_exists_le _
    _ ≤ ∑ _j : NonzeroSlope k × k, Real.exp (-(Fintype.card k : ℝ) / 2048) := by
      apply Finset.sum_le_sum
      intro j _
      exact prob_originalLineCount_lt_five hq j.1 j.2
    _ = (Fintype.card (NonzeroSlope k × k) : ℝ) *
        Real.exp (-(Fintype.card k : ℝ) / 2048) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right htests (Real.exp_pos _).le

theorem prob_originalLineDensity_ge (hq : 2048 ≤ Fintype.card k) :
    1 - (Fintype.card k : ℝ) ^ 2 * Real.exp (-(Fintype.card k : ℝ) / 2048) ≤
      (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob
        OriginalLineDensity := by
  have h := prob_not_originalLineDensity_le (k := k) hq
  rw [FiniteLaw.prob_compl] at h
  linarith

theorem tendsto_originalDensity_failure_atTop :
    Tendsto (fun q : ℕ => (q : ℝ) ^ 2 * Real.exp (-(q : ℝ) / 2048))
      atTop (𝓝 0) := by
  have h : Tendsto (fun q : ℝ => q ^ 2 * Real.exp (-q / 2048)) atTop (𝓝 0) := by
    have h' := LineCover.tendsto_rpow_mul_exp_neg_rpow_atTop
      (2 : ℝ) (a := 1) (c := 1 / 2048) (by norm_num) (by norm_num)
    simpa [Real.rpow_natCast, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
  exact h.comp tendsto_natCast_atTop_atTop

def originalDensityProbability (k : Type*) [Field k] [Fintype k] [DecidableEq k] : ℝ :=
  (FiniteLaw.pi (fun _ : NonzeroSlope k => FiniteLaw.uniform k)).prob OriginalLineDensity

theorem tendsto_originalDensityProbability
    {ι : Type*} {l : Filter ι} (K : ι → Type*)
    [∀ i, Field (K i)] [∀ i, Fintype (K i)] [∀ i, DecidableEq (K i)]
    (hcard : Tendsto (fun i => Fintype.card (K i)) l atTop) :
    Tendsto (fun i => originalDensityProbability (K i)) l (𝓝 1) := by
  let μ (i : ι) := FiniteLaw.pi (fun _ : NonzeroSlope (K i) => FiniteLaw.uniform (K i))
  have hfailure : Tendsto
      (fun i => (Fintype.card (K i) : ℝ) ^ 2 *
        Real.exp (-(Fintype.card (K i) : ℝ) / 2048)) l (𝓝 0) :=
    tendsto_originalDensity_failure_atTop.comp hcard
  have hbad : Tendsto (fun i => (μ i).prob (fun a => ¬ OriginalLineDensity a)) l (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hfailure
    · exact Filter.Eventually.of_forall fun i => (μ i).prob_nonneg _
    · filter_upwards [hcard.eventually (eventually_ge_atTop 2048)] with i hi
      exact prob_not_originalLineDensity_le hi
  have hgood : Tendsto
      (fun i => 1 - (μ i).prob (fun a => ¬ OriginalLineDensity a)) l (𝓝 (1 - 0 : ℝ)) :=
    tendsto_const_nhds.sub hbad
  have heq : (fun i => 1 - (μ i).prob (fun a => ¬ OriginalLineDensity a)) =
      (fun i => originalDensityProbability (K i)) := by
    funext i
    rw [FiniteLaw.prob_compl]
    change 1 - (1 - originalDensityProbability (K i)) = originalDensityProbability (K i)
    ring
  rw [heq] at hgood
  simpa only [sub_zero] using hgood

end RyserCoveringCounterexample.Construction

end

end OAI
