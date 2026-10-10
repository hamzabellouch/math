import OAI.Analysis.FiniteFactor.OrbitSampling.Tail
import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseDecay

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology
noncomputable section

theorem unitInterval_order_failure (a : ℝ) (ha : 0 ≤ a) :
    unitIntervalMeasure {x : ℝ | Int.fract (x+a) < x} ≤ ENNReal.ofReal a := by
  have hsub : {x : ℝ | Int.fract (x+a) < x} ⊆ {x : ℝ | Int.floor (x+a) ≠ 0} := by
    intro x hx he
    change Int.fract (x+a) < x at hx
    rw [Int.fract, he, Int.cast_zero, sub_zero] at hx
    linarith
  simpa only [abs_of_nonneg ha] using (measure_mono hsub).trans (unitInterval_floor_exception a)

def sourceTailOrderFailure (θ : SourceCoordinate → ℝ) (s n : ℕ) : Set (SourceCoordinate → ℝ) :=
  ⋃ r : ℕ, ⋃ i : Fin (sourceBlockSize (s+r)),
    {x | Int.fract (x ⟨s+r,i⟩+(n : ℝ)*θ ⟨s+r,i⟩) < x ⟨s+r,i⟩}

theorem SourceAngles.block_sum_le {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (s : ℕ) :
    (∑ i : Fin (sourceBlockSize s), θ ⟨s,i⟩) ≤ 2 / ((sourceStageState s).K : ℝ) := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (hθ ⟨s,i⟩).2)
  have he : (∑ _i : Fin (sourceBlockSize s),
      2 / ((sourceBlockSize s : ℝ)*(sourceStageState s).K)) =
      2 / ((sourceStageState s).K : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [(sourceBlockSize_pos s).ne', (sourceCutoff_pos s).ne']
  exact hh.trans_eq he

theorem SourceAngles.tail_block_summable {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (s : ℕ) :
    Summable (fun r : ℕ => ∑ i : Fin (sourceBlockSize (s+r)), θ ⟨s+r,i⟩) := by
  have hh := sourceCutoff_reciprocal_summable.comp_injective (add_right_injective s)
  have hs : Summable (fun r => 2 / ((sourceStageState (s+r)).K : ℝ)) := by
    simpa [div_eq_mul_inv] using hh.mul_left 2
  exact hs.of_nonneg_of_le (fun r => Finset.sum_nonneg (fun i _ => hθ.nonneg _))
    (fun r => hθ.block_sum_le (s+r))

/-- Actual Haar probability of violating order in any tail coordinate, for
one positive orbit power. The countably infinite union is controlled. -/
theorem SourceAngles.tail_order_probability {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ) (s n : ℕ) :
    (Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure))
      (sourceTailOrderFailure θ s n) ≤ ENNReal.ofReal (4*(n : ℝ)/((sourceStageState s).K : ℝ)) := by
  let μ := Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)
  have hcoord (i : SourceCoordinate) :
      μ {x | Int.fract (x i+(n : ℝ)*θ i) < x i} ≤ ENNReal.ofReal ((n : ℝ)*θ i) := by
    have hm : MeasurableSet {t : ℝ | Int.fract (t+(n : ℝ)*θ i) < t} := by
      apply measurableSet_lt
      · exact sourceFract_measurable.comp (by fun_prop)
      · exact measurable_id
    have he := congrArg (fun ν : Measure ℝ => ν {t : ℝ | Int.fract (t+(n : ℝ)*θ i) < t})
      (Measure.infinitePi_map_eval (fun _ : SourceCoordinate => unitIntervalMeasure) i)
    rw [Measure.map_apply (measurable_pi_apply i) hm] at he
    rw [show μ {x | Int.fract (x i+(n : ℝ)*θ i) < x i} =
      unitIntervalMeasure {t | Int.fract (t+(n : ℝ)*θ i) < t} from he]
    exact unitInterval_order_failure _ (mul_nonneg (Nat.cast_nonneg _) (hθ.nonneg _))
  have hblock (r : ℕ) :
      μ (⋃ i : Fin (sourceBlockSize (s+r)),
        {x | Int.fract (x ⟨s+r,i⟩+(n : ℝ)*θ ⟨s+r,i⟩) < x ⟨s+r,i⟩}) ≤
      ENNReal.ofReal ((n : ℝ)*(∑ i : Fin (sourceBlockSize (s+r)), θ ⟨s+r,i⟩)) := by
    apply (measure_iUnion_le _).trans
    calc
      _ ≤ ∑' i : Fin (sourceBlockSize (s+r)), ENNReal.ofReal ((n : ℝ)*θ ⟨s+r,i⟩) :=
        ENNReal.tsum_le_tsum (fun i => hcoord ⟨s+r,i⟩)
      _ = _ := by
        rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hθ.nonneg _)),
          ← Finset.mul_sum]
  calc
    _ ≤ ∑' r : ℕ, μ (⋃ i : Fin (sourceBlockSize (s+r)),
        {x | Int.fract (x ⟨s+r,i⟩+(n : ℝ)*θ ⟨s+r,i⟩) < x ⟨s+r,i⟩}) := measure_iUnion_le _
    _ ≤ ∑' r : ℕ, ENNReal.ofReal ((n : ℝ)*(∑ i : Fin (sourceBlockSize (s+r)), θ ⟨s+r,i⟩)) :=
      ENNReal.tsum_le_tsum hblock
    _ = ENNReal.ofReal ((n : ℝ)*sourceTailAngleSum θ s) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun r => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => hθ.nonneg _)))
        ((hθ.tail_block_summable s).mul_left (n : ℝ)), tsum_mul_left]
      rfl
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hh := mul_le_mul_of_nonneg_left (hθ.tail_sum_bound s) (Nat.cast_nonneg n)
      simpa [mul_div_assoc, mul_comm, mul_left_comm] using hh)

/-- The source's trimming error tends to zero for every admissible angle
realization, uniformly for all positive powers up to Q_s=m_s^((7/10)m_s). -/
theorem sourceSampling_tail_error_tendsto :
    Tendsto (fun s => 4*(sourceBlockSize s : ℝ)^(-(sourceBlockSize s : ℝ)/20)) atTop (𝓝 0) := by
  have ht : Tendsto (fun s => 4*(sourceBlockSize s : ℝ)⁻¹) atTop (𝓝 0) := by
    have hi : Tendsto (fun s => (sourceBlockSize s : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
    simpa using hi.const_mul (4 : ℝ)
  apply squeeze_zero (fun s => by positivity) _ ht
  intro s
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [← Real.rpow_neg_one]
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

end
end FiniteFactor

end OAI
