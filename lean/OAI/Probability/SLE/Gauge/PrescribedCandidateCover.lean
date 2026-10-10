import OAI.Probability.SLE.Gauge.PrescribedCoverGrid
import OAI.Probability.SLE.Gauge.PrescribedGaugeCost
import OAI.Probability.SLE.Gauge.BatchRadiusGaps
import OAI.Probability.SLE.Gauge.GaugeEntrySmallness
import OAI.Probability.SLE.Gauge.FiniteCoverAssembly

namespace OAI

/-! Actual finite candidate and missed-cell covers for a prescribed batch.
Candidate selection uses the terminal spatial measure. No terminal event
is inserted into the adapted finite change of law. -/
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

def prescribedCandidateIndices {J : ℕ} (κ : ℝ) (W : Target.WienerLaw) (n : ℕ)
    (e : Fin J → ℤ × ℕ) (C c R : ℝ) (K : Set ℂ) (ν : Measure ℂ) :
    Finset ((ℤ × ℤ) × Fin J) := by
  classical
  let r := Target.entryRadius κ W (n,none)
  exact ((prescribedGridIndex R r K) ×ˢ Finset.univ).filter (fun ij =>
    ENNReal.ofReal (c*Target.entryValue (n,some (e ij.2))*
      (Target.entryRadius κ W (n,some (e ij.2)))^Target.d κ) ≤
    ν (closedBall (prescribedGridCenter r ij.1)
      (C*Target.entryRadius κ W (n,some (e ij.2)))))

def prescribedMissedIndices {J : ℕ} (κ : ℝ) (W : Target.WienerLaw) (n : ℕ)
    (e : Fin J → ℤ × ℕ) (C c R : ℝ) (K E : Set ℂ) (ν : Measure ℂ) : Finset (ℤ × ℤ) := by
  classical
  let r := Target.entryRadius κ W (n,none)
  exact (prescribedGridIndex R r K).filter (fun ij =>
    (E ∩ prescribedFineCell r ij).Nonempty ∧ ∀ j,
      ν (closedBall (prescribedGridCenter r ij) (C*Target.entryRadius κ W (n,some (e j)))) <
      ENNReal.ofReal (c*Target.entryValue (n,some (e j))*
        (Target.entryRadius κ W (n,some (e j)))^Target.d κ))

theorem prescribed_candidates_finite_cover
    {κ : ℝ} (hκ : 0<κ) (W : Target.WienerLaw)
    (hg : Target.IsHausdorffGauge (Target.gauge κ W))
    {n J : ℕ} (hn : 1 ≤ n) (hm1 : 0<Target.moment κ W 1)
    (hJ : Target.moment κ W 1^n ≤ Target.moment κ W n)
    (e : Fin J → ℤ × ℕ) (he : ∀ j, (e j).2<Target.multiplicity κ W n (e j).1)
    (C c R : ℝ) (hC : 3 ≤ C) (hc : 0<c) (hR : 0 ≤ R)
    (K E : Set ℂ) (hK : K ⊆ closedBall 0 R) (hH : ∀ z∈K, 0 ≤ z.im)
    (hE : E ⊆ K) (ν : Measure ℂ) :
    ∃ (N : ℕ) (U : Fin N → Set ℂ), E ⊆ ⋃ i, U i ∧
      (∀ i, ediam (U i) ≤ ENNReal.ofReal (8*C*Real.exp (-(n:ℝ)^2))) ∧
      (∑ i, extendedGauge (Target.gauge κ W) (ediam (U i))) ≤
        ENNReal.ofReal ((8*C)^2/c)*ν (closedBall 0 (R+3+C)) +
        (prescribedMissedIndices κ W n e C c R K E ν).card *
          ENNReal.ofReal (36*(n:ℝ)*(Target.entryRadius κ W (n,none))^Target.d κ) := by
  classical
  let r := Target.entryRadius κ W (n,none)
  let s (j : Fin J) := Target.entryRadius κ W (n,some (e j))
  let I := prescribedCandidateIndices κ W n e C c R K ν
  let M := prescribedMissedIndices κ W n e C c R K E ν
  let x (ij : (ℤ×ℤ)×Fin J) := prescribedGridCenter r ij.1
  let rad (ij : (ℤ×ℤ)×Fin J) := C*s ij.2
  let δ := ENNReal.ofReal (8*C*Real.exp (-(n:ℝ)^2))
  have hC0 : 0 ≤ C := by linarith
  have hr : 0<r := Real.exp_pos _
  have hs (j) : 0<s j := Real.exp_pos _
  have hsmall (j) : s j ≤ Real.exp (-(n:ℝ)^2) := Target.entryRadius_le_batch_exp hκ W _
  have hrsmall : r ≤ Real.exp (-(n:ℝ)^2) := Target.entryRadius_le_batch_exp hκ W _
  have hunit : r ≤ 1 := hrsmall.trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  have hrs (j) : r ≤ s j := (Target.entryRadius_lt_of_position_lt hκ W hn
    (Target.entryPosition_lt_cleanup κ W hn hm1 hJ (he j))).le
  have hcontain (j) : 3*r ≤ C*s j := by
    nlinarith [mul_le_mul_of_nonneg_left (hrs j) (by norm_num : (0:ℝ) ≤ 3)]
  have himem {ij : (ℤ×ℤ)×Fin J} (hij : ij∈I) :
      ij.1∈prescribedGridIndex R r K ∧
      ENNReal.ofReal (c*Target.entryValue (n,some (e ij.2))*(s ij.2)^Target.d κ) ≤
        ν (closedBall (x ij) (rad ij)) := by
    exact ⟨(Finset.mem_product.mp (Finset.mem_filter.mp hij).1).1,
      (Finset.mem_filter.mp hij).2⟩
  have hcover : ∀ z∈E, (∃ ij∈I, z∈closedBall (x ij) (rad ij)) ∨
      ∃ ij∈M, z∈prescribedFineCell r ij := by
    intro z hz
    obtain ⟨ij,hij,hzcell⟩ := mem_iUnion₂.mp (prescribedGrid_covers hR hr hK hH (hE hz))
    by_cases hq : ∃ j, ENNReal.ofReal (c*Target.entryValue (n,some (e j))*(s j)^Target.d κ) ≤
        ν (closedBall (prescribedGridCenter r ij) (C*s j))
    · obtain ⟨j,hj⟩ := hq
      refine Or.inl ⟨(ij,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hij,Finset.mem_univ _⟩,hj⟩,?_⟩
      exact hzcell.trans (hcontain j)
    · refine Or.inr ⟨ij,Finset.mem_filter.mpr ⟨hij,⟨z,hz,hzcell⟩,?_⟩,hzcell⟩
      intro j
      exact lt_of_not_ge (fun hj => hq ⟨j,hj⟩)
  have hball : ∀ ij∈I, closedBall (x ij) (rad ij) ⊆ closedBall 0 (R+3+C) := by
    intro ij hij z hz
    have hx := prescribedGrid_center_bound hK (himem hij).1
    have hs1 : s ij.2 ≤ 1 := (hsmall _).trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
    have hrad : rad ij ≤ C := by dsimp only [rad]; nlinarith
    have hz' : dist z (x ij) ≤ rad ij := hz
    have ht := dist_triangle z (x ij) 0
    simp only [dist_zero_right] at ht
    change dist z 0 ≤ R+3+C
    rw [dist_zero_right]
    dsimp only [x] at ht
    nlinarith
  have hdiam : ∀ ij∈I, ediam (closedBall (x ij) (4*rad ij)) ≤ δ := by
    intro ij _
    apply ediam_le_of_forall_dist_le
    intro z hz w hw
    have hz' : dist z (x ij) ≤ 4*rad ij := hz
    have hw' : dist (x ij) w ≤ 4*rad ij := by simpa only [mem_closedBall,dist_comm] using hw
    apply (dist_triangle z (x ij) w).trans
    have hh := mul_le_mul_of_nonneg_left (hsmall ij.2) (show 0 ≤ 8*C by positivity)
    dsimp only [rad] at hz' hw'
    nlinarith
  have hmiss : ∀ ij∈M, ediam (prescribedFineCell r ij) ≤ δ := by
    intro ij _
    apply ediam_le_of_forall_dist_le
    intro z hz w hw
    have hz' : dist z (prescribedGridCenter r ij) ≤ 3*r := hz
    have hw' : dist (prescribedGridCenter r ij) w ≤ 3*r := by
      simpa only [prescribedFineCell,mem_closedBall,dist_comm] using hw
    apply (dist_triangle z (prescribedGridCenter r ij) w).trans
    have hh := mul_le_mul_of_nonneg_left hrsmall (show (0:ℝ) ≤ 6 by norm_num)
    have hexp := Real.exp_pos (-(n:ℝ)^2)
    nlinarith
  obtain ⟨N,U,hcov,hU,hcost⟩ := exists_finite_selected_missed_cover I M x rad
    (prescribedFineCell r) E (closedBall 0 (R+3+C)) ν (Target.gauge κ W)
    (C*Real.exp (-(n:ℝ)^2)) (fun ij _ => mul_le_mul_of_nonneg_left (hsmall _) hC0)
    δ (ENNReal.ofReal ((8*C)^2/c)) hball
    (fun ij hij => by
      simpa only [rad,mul_assoc] using Target.enlarged_candidate_gauge_cost W hg
        (n,some (e ij.2)) ⟨hn,he ij.2⟩ (x ij) (by linarith : 1 ≤ C) hc ν (himem hij).2)
    hdiam hmiss hcover
  refine ⟨N,U,hcov,hU,hcost.trans ?_⟩
  apply add_le_add le_rfl
  calc
    (∑ ij∈M, extendedGauge (Target.gauge κ W) (ediam (prescribedFineCell r ij))) ≤
        ∑ _ij∈M, ENNReal.ofReal (36*(n:ℝ)*r^Target.d κ) := by
      apply Finset.sum_le_sum
      intro ij _
      have hh : IsGauge (Target.gauge κ W) := ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2⟩
      refine (extendedGauge_closedBall_le hh (prescribedGridCenter r ij) (by positivity)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      have hb := Target.gauge_scaled_entry_le κ W (n,none) ⟨hn,trivial⟩ 6
      norm_num [Target.entryValue] at hb
      convert hb using 1
      dsimp only [r]
      congr 1
      ring
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]

end SLEExactGauge

end

end OAI
