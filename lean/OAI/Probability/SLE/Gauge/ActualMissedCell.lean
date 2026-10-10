import OAI.Probability.SLE.Gauge.ActualDenseWindow
import OAI.Probability.SLE.Loewner.ActualApproachAtRadius
import OAI.Probability.SLE.Gauge.DenseCandidateCover
import OAI.Probability.SLE.Mass.UniformCoverLevels

namespace OAI

/-! Original-law probabilities of visited cells with no terminal sausage
candidate, obtained from adapted failures under one finite centered law. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

local instance actualMissedDriverMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance actualMissedDriverBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

lemma radius_gap_power (a u v p : ℝ) (ha : 0 < a) :
    Real.exp (-p * v) * (a * Real.exp (-u)) ^ p =
      (a * Real.exp (-(u + v))) ^ p := by
  rw [Real.rpow_def_of_pos (mul_pos ha (Real.exp_pos _)),
    Real.rpow_def_of_pos (mul_pos ha (Real.exp_pos _)),
    Real.log_mul ha.ne' (Real.exp_ne_zero _),
    Real.log_mul ha.ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_exp,
    ← Real.exp_add]
  congr 1
  ring

lemma denseMissedCell_subset_actual_failure
    {Ω : Type*} (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (hc : ∀ ω, Continuous (γ ω))
    (G : Ω → ℝ≥0 → ℂ → ℂ) (T q b c v : ℝ) (n : ℕ) (ij : ℤ × ℤ) :
    {ω | denseMissedCell κ T b c v n ij (γ ω)} ⊆
      actualDenseWindowFailure κ γ hc G (coverGridCenter (coverRadius T n) ij)
        T q b v (coverMultiplicity c n) n := by
  intro ω hω
  apply mem_iInter₂.mpr
  intro j hj hsuccess
  exact (not_le_of_gt (hω.2 j hj))
    (hsuccess.trans (stoppedWholeSausageCharge_le_whole κ (sourceTracePath γ hc ω)
      _ v _))

theorem actual_missed_cell_bound_of_centered_failure
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (htrace : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (T q b c v : ℝ) (hT : 0 ≤ T) (hq : 0 ≤ q) (hgap : 1 + q ≤ T)
    (n : ℕ) (ij : ℤ × ℤ)
    (hz : coverGridCenter (coverRadius T n) ij ∈ upperHalfPlane)
    (hlevel : ∀ j ∈ coverTestWindow n,
      coverLogLevel (coverGridCenter (coverRadius T n) ij) T j =
        Real.log (2 * (coverGridCenter (coverRadius T n) ij).im) + T * (j : ℝ))
    (hvisit : coverLogLevel (coverGridCenter (coverRadius T n) ij) T (2 * n / 3 + 1) + 1 ≤
      coverVisitLevel (coverGridCenter (coverRadius T n) ij) T n)
    (hsmall : 4 * coverRadius T n ≤ (coverGridCenter (coverRadius T n) ij).im)
    (hfailure : finiteCenteredLaw P κ B γ G (coverGridCenter (coverRadius T n) ij)
      (coverVisitLevel (coverGridCenter (coverRadius T n) ij) T n)
      (actualDenseWindowFailure κ γ (fun ω => (hw ω).1) G
        (coverGridCenter (coverRadius T n) ij) T q b v (coverMultiplicity c n) n) ≤
      ENNReal.ofReal (Real.exp (-Real.sqrt (n : ℝ) / 4))) :
    P {ω | denseMissedCell κ T b c v n ij (γ ω)} ≤
      ENNReal.ofReal ((uniformInverseAngleConstant κ 1 * (512 * Real.pi) ^ codimension κ *
        initialGreen κ (coverGridCenter (coverRadius T n) ij)) *
        coverRadius T n ^ codimension κ * Real.exp (-Real.sqrt (n : ℝ) / 4)) := by
  let z := coverGridCenter (coverRadius T n) ij
  let u := coverLogLevel z T (2 * n / 3 + 1)
  let V := coverVisitLevel z T n
  have hgapV : u + 1 ≤ V := hvisit
  have hzim : 0 < z.im := hz
  let w : ℝ≥0 := ⟨V - u, by linarith⟩
  have hw1 : 1 ≤ (w : ℝ) := by change 1 ≤ V-u; linarith
  have hu : 0 ≤ u := coverLogLevel_nonneg _ _ _
  have hV : 0 ≤ V := coverVisitLevel_nonneg_of_gap z T n hvisit
  let A := actualDenseWindowFailure κ γ (fun ω => (hw ω).1) G z T q b v (coverMultiplicity c n) n
  have hA := actual_dense_window_failure_measurable_at_end P κ hκ hκ8 B hB hBm hc hB0
    γ G F hw z hz T q b v hT hq hgap (coverMultiplicity c n) n hlevel
  have happroach := actual_conditional_approach_at_radius_stop P κ hκ hκ8 B hB hBm hc hB0
    γ G F hw htrace z hz u hu w hw1 A hA
  have huv : u + (w : ℝ) = V := by change u + (V-u) = V; ring
  rw [huv] at happroach
  have hsubset : {ω | denseMissedCell κ T b c v n ij (γ ω)} ⊆
      A ∩ {ω | radiusLevelTime (γ ω) (G ω) z V < ∞} := by
    intro ω hω
    refine ⟨denseMissedCell_subset_actual_failure κ γ (fun ω => (hw ω).1) G T q b c v n ij hω, ?_⟩
    obtain ⟨x, ⟨t, rfl⟩, ht⟩ := hω.1
    have hdist : dist (γ ω t) z < 4 * coverRadius T n := by
      change dist (γ ω t) z ≤ 2 * coverRadius T n at ht
      linarith [coverRadius_pos T n]
    obtain ⟨s, _, hslive, hsR⟩ := (hw ω).radius_approach_of_trace_approach
      ((hc ω).const_mul _) z (4 * coverRadius T n) (by positivity [coverRadius_pos T n]) hsmall t hdist
    have hscale : (128 * Real.pi) * (4 * coverRadius T n) = (2 * z.im) * Real.exp (-V) := by
      rw [coverVisitLevel_radius z hz T n]
      ring
    exact radiusLevelTime_finite_of_live_radius_lt ((hc ω).const_mul _) (hw ω) z V hV s hslive
      (by rwa [← hscale])
  have hK : uniformInverseAngleConstant κ 1 * Real.exp (-codimension κ * (w : ℝ)) *
      ((2 * z.im) * Real.exp (-u)) ^ codimension κ * initialGreen κ z =
      (uniformInverseAngleConstant κ 1 * (512 * Real.pi) ^ codimension κ * initialGreen κ z) *
        coverRadius T n ^ codimension κ := by
    calc
      _ = uniformInverseAngleConstant κ 1 *
          (Real.exp (-codimension κ * (w : ℝ)) * ((2 * z.im) * Real.exp (-u)) ^ codimension κ) *
          initialGreen κ z := by ring
      _ = uniformInverseAngleConstant κ 1 *
          ((2 * z.im) * Real.exp (-V)) ^ codimension κ * initialGreen κ z := by
        rw [radius_gap_power (2 * z.im) u (w : ℝ) (codimension κ) (mul_pos (by norm_num) hzim), huv]
      _ = _ := by
        rw [coverVisitLevel_radius z hz T n,
          Real.mul_rpow (by positivity : 0 ≤ 512 * Real.pi) (coverRadius_pos T n).le]
        ring
  rw [hK] at happroach
  have hKnonneg : 0 ≤ (uniformInverseAngleConstant κ 1 * (512 * Real.pi) ^ codimension κ *
      initialGreen κ z) * coverRadius T n ^ codimension κ := by
    have hC := uniformInverseAngleConstant_pos κ 1 hκ hκ8 (by norm_num)
    have hI := initialGreen_pos κ z hz
    exact mul_nonneg (mul_nonneg
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)) hI.le)
      (Real.rpow_nonneg (coverRadius_pos T n).le _)
  calc
    _ ≤ P (A ∩ {ω | radiusLevelTime (γ ω) (G ω) z V < ∞}) := measure_mono hsubset
    _ ≤ _ := happroach
    _ ≤ ENNReal.ofReal ((uniformInverseAngleConstant κ 1 * (512 * Real.pi) ^ codimension κ *
          initialGreen κ z) * coverRadius T n ^ codimension κ) *
        ENNReal.ofReal (Real.exp (-Real.sqrt (n : ℝ) / 4)) :=
      mul_le_mul' le_rfl hfailure
    _ = _ := (ENNReal.ofReal_mul hKnonneg).symm

end SLEExactGauge

end

end OAI
