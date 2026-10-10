import OAI.Probability.SLE.Gauge.DenseCandidateCover
import OAI.Probability.SLE.Gauge.MissedCellCleanup

namespace OAI

/-! The expected explicit-gauge cost of the actual finite candidate cover.
The leading constant is chosen before the compact interior cutoff; only the
vanishing missed-cell prefactor is allowed to depend on that cutoff. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance denseExpectationPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance denseExpectationPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

def denseMissedProbabilityBound (κ T D : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (D * coverRadius T n ^ codimension κ * Real.exp (-Real.sqrt (n : ℝ) / 4))

theorem dense_missed_cost_tendsto_zero
    {κ T R D : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hT : 0 < T)
    (hR : 0 ≤ R) (hD : 0 ≤ D) (K : Set ℂ)
    {h : ℝ → ℝ} (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ)) :
    Tendsto (fun n => ∑ ij ∈ retainedCoverGridIndex R (coverRadius T n) K,
      extendedGauge h (ediam (denseFineCell T n ij)) * denseMissedProbabilityBound κ T D n)
      atTop (𝓝 0) := by
  obtain ⟨A, hA, hcost⟩ := denseFineCell_eventual_gauge_bound hκ8 hT hh hf
  have hlimR : Tendsto (fun n : ℕ => (2 * R + 5) ^ 2 * A * D *
      (Real.log (n : ℝ)) ^ (codimension κ / 2) * Real.exp (-Real.sqrt (n : ℝ) / 4))
      atTop (𝓝 0) := by
    have ht := (explicit_cleanup_tendsto_zero (κ := κ) (c := 1 / 4) hκ (by norm_num)).const_mul
      ((2 * R + 5) ^ 2 * A * D)
    convert ht using 1
    · funext n
      have he : -Real.sqrt (n : ℝ) / 4 = -(1 / 4 : ℝ) * Real.sqrt (n : ℝ) := by ring
      rw [he]
      ring
    · simp only [mul_zero]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((2 * R + 5) ^ 2 * A * D *
      (Real.log (n : ℝ)) ^ (codimension κ / 2) * Real.exp (-Real.sqrt (n : ℝ) / 4)))
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlimR
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le)
  filter_upwards [hcost] with n hn
  have hr1 : coverRadius T n ≤ 1 := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hT.le) (Nat.cast_nonneg _))
  have he : -(1 / 4 : ℝ) * Real.sqrt (n : ℝ) = -Real.sqrt (n : ℝ) / 4 := by ring
  have hb := missed_cell_sum_bound (retainedCoverGridIndex R (coverRadius T n) K)
    (fun ij => extendedGauge h (ediam (denseFineCell T n ij)))
    (fun _ => denseMissedProbabilityBound κ T D n) κ (coverRadius T n) n (1 / 4)
    ((2 * R + 5) ^ 2) A D (coverRadius_pos T n) (Real.log_natCast_nonneg n)
    (sq_nonneg _) hA.le hD
    (retainedCoverGrid_card_bound hR (coverRadius_pos T n) hr1 K)
    (fun ij _ => hn ij) (fun _ _ => by simp only [denseMissedProbabilityBound, he]; exact le_rfl)
  simpa only [denseMissedProbabilityBound, he] using hb

/-- A uniform candidate charge and the actual stretched-exponential missed
bound give the upper expectation. `C` is fixed before `R`, `K`, and `D`. -/
theorem expected_hausdorff_of_dense_candidates
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hγ : ∀ ω, Continuous (γ ω))
    {T b c : ℝ} (hT : 0 < T) (hb : 0 < b) (hc : 0 < c)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ)) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (R : ℝ), 0 ≤ R → ∀ K : Set ℂ,
      K ⊆ closedBall 0 R → ∀ (v : ℕ → ℝ), (∀ n, 0 < v n) →
      ∀ (D : ℝ), 0 ≤ D →
      (∀ᶠ n : ℕ in atTop, ∀ ij ∈ retainedCoverGridIndex R (coverRadius T n) K,
        P {ω | denseMissedCell κ T b c (v n) n ij (γ ω)} ≤ denseMissedProbabilityBound κ T D n) →
      (∫⁻ ω, hausdorffGauge h (K ∩ range (γ ω)) ∂P) ≤
        (C : ℝ≥0∞) * wholeSausageChargeBound κ (R + 3) := by
  classical
  obtain ⟨C, hC, hcharge⟩ := denseCandidate_eventual_gauge_charge hκ8 hT hb hc hh hf
  refine ⟨C, hC, ?_⟩
  intro R hR K hK v hv D hD hprob
  let f : Ω → C(ℝ≥0, ℂ) := fun ω => ⟨γ ω, hγ ω⟩
  have hfmeas : Measurable f := source_whole_path_measurable f hSLE.1
  have hcover := dense_candidates_and_missed_cover hR hT hK κ b c
  have hall := hcharge.and (hcover.and hprob)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  let k : ℕ → ℕ := fun n => n + N
  have hk (n : ℕ) : N ≤ k n := Nat.le_add_left N n
  have hkTop : Tendsto k atTop atTop := tendsto_add_atTop_nat N
  apply expected_hausdorff_le_of_candidate_disks P κ hκ hκ8 γ hSLE h
    (fun ω => K ∩ range (γ ω))
    (fun n ω => denseCandidateIndices R T K κ b c (v (k n)) (k n) (γ ω))
    (fun n => retainedCoverGridIndex R (coverRadius T (k n)) K)
    (fun n => denseCandidateCenter T (k n)) (fun _ => denseCandidateRadius T)
    (fun n => denseFineCell T (k n))
    (fun n ij => {ω | denseMissedCell κ T b c (v (k n)) (k n) ij (γ ω)})
    (fun n ij _ => denseMissedCell_measurable f hfmeas κ T b c (v (k n)) (k n) ij)
    (fun n => v (k n)) (fun n => hv (k n)) (R + 3) C
    (fun n => denseCoverDiameter T (k n)) ((denseCoverDiameter_tendsto_zero hT).comp hkTop)
    (fun n _ => denseMissedProbabilityBound κ T D (k n))
    (fun n ij hij => (hN (k n) (hk n)).2.2 ij hij)
    ((dense_missed_cost_tendsto_zero hκ hκ8 hT hR hD K hh hf).comp hkTop)
  apply Eventually.of_forall
  intro ω n
  have hn := hN (k n) (hk n)
  refine ⟨?_, ?_, hn.1 R K (v (k n)) (γ ω), ?_, ?_, hn.2.1 (v (k n)) (γ ω)⟩
  · intro i _
    exact (denseCandidateRadius_le_one hT.le i).trans (by linarith)
  · exact fun _ hi => denseCandidate_disk_subset hT.le hK hi
  · exact fun _ hi => denseCandidate_enlarged_diameter hT.le hi
  · exact fun ij _ => denseFineCell_diameter T (k n) ij

end SLEExactGauge

end

end OAI
