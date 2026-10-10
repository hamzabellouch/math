import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseFirst
import OAI.Analysis.FiniteFactor.CrossedProduct.PhaseDecay

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology Classical
noncomputable section

def sourcePhaseUpper (s : ℕ) : ℝ :=
  (sourceBlockSize s : ℝ)^((4/5 : ℝ)*(sourceBlockSize s : ℝ))

def sourcePhaseLower (s : ℕ) : ℝ :=
  ((sourceBlockSize s : ℝ)*(sourceStageState s).K)/4

def sourcePhaseFailure (s : ℕ) : Set (SourceCoordinate → ℝ) :=
  ⋃ n ∈ Finset.Icc 1 (Nat.floor (sourcePhaseUpper s)),
    if sourcePhaseLower s ≤ (n : ℝ) then sourceFewPhases s (n : ℤ) else ∅

theorem sourcePhaseFailure_bound (s : ℕ) :
    sourceAngleLaw (sourcePhaseFailure s) ≤ ENNReal.ofReal (sourcePhaseFailureMajorant s) := by
  let B : ℝ≥0∞ := (2 : ℝ≥0∞)^sourceBlockSize s *
    (ENNReal.ofReal (10*sourceWidth s 1))^sourceMissCount s
  have hn (n : ℕ) : sourceAngleLaw
      (if sourcePhaseLower s ≤ (n : ℝ) then sourceFewPhases s (n : ℤ) else ∅) ≤ B := by
    split_ifs with h
    · apply sourceFewPhases_probability
      simpa only [sourcePhaseLower, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)] using h
    · simp
  have hQ : 0 ≤ sourcePhaseUpper s := by unfold sourcePhaseUpper; positivity
  have hc : ((Finset.Icc 1 (Nat.floor (sourcePhaseUpper s))).card : ℝ≥0∞) ≤
      ENNReal.ofReal (sourcePhaseUpper s) := by
    simp only [Nat.card_Icc, Nat.add_sub_cancel]
    exact_mod_cast ENNReal.ofReal_le_ofReal (Nat.floor_le hQ)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nat.floor (sourcePhaseUpper s)), sourceAngleLaw
        (if sourcePhaseLower s ≤ (n : ℝ) then sourceFewPhases s (n : ℤ) else ∅) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 (Nat.floor (sourcePhaseUpper s)), B :=
      Finset.sum_le_sum (fun n _ => hn n)
    _ = ((Finset.Icc 1 (Nat.floor (sourcePhaseUpper s))).card : ℝ≥0∞)*B := by simp [nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (sourcePhaseUpper s)*B := by gcongr
    _ = ENNReal.ofReal (sourcePhaseFailureMajorant s) := by
      have hw : 0 ≤ 10*sourceWidth s 1 := by unfold sourceWidth; dsimp; positivity
      dsimp [B]
      rw [show (2 : ℝ≥0∞)^sourceBlockSize s = ENNReal.ofReal ((2 : ℝ)^sourceBlockSize s) by simp,
        ← ENNReal.ofReal_pow hw,
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2^sourceBlockSize s),
        ← ENNReal.ofReal_mul hQ]
      congr 1
      unfold sourcePhaseFailureMajorant sourcePhaseUpper
      ring

theorem sourcePhaseFailure_finite :
    ∀ᵐ θ ∂sourceAngleLaw, {s | θ ∈ sourcePhaseFailure s}.Finite := by
  apply ae_finite_setOfPred_mem
  apply ne_of_lt
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum sourcePhaseFailure_bound)
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (fun s => by unfold sourcePhaseFailureMajorant sourceWidth; dsimp; positivity)
    sourcePhaseFailureMajorant_summable]
  exact ENNReal.ofReal_lt_top

theorem sourcePhaseMissSet_natAbs (s : ℕ) (k : ℤ) :
    sourcePhaseMissSet s (k.natAbs : ℤ) = sourcePhaseMissSet s k := by
  ext t
  simp only [sourcePhaseMissSet, Set.mem_ofPred_eq, threshold_middle_iff]
  rcases le_total 0 k with hp | hn
  · have he : (k.natAbs : ℤ) = k := by rw [Int.natCast_natAbs, abs_of_nonneg hp]
    rw [he]
  · have he : (k.natAbs : ℤ) = -k := by rw [Int.natCast_natAbs, abs_of_nonpos hn]
    rw [he, Int.cast_neg, neg_mul, fract_neg_middle_iff]

/-- Proposition phases, assertion 2, for all signed integer powers at every
sufficiently late stage on one probability-one event. -/
theorem sourceAngleLaw_second_phases : ∀ᵐ θ ∂sourceAngleLaw,
    ∀ᶠ s in atTop, ∀ k : ℤ, sourcePhaseLower s ≤ |(k : ℝ)| →
      |(k : ℝ)| ≤ sourcePhaseUpper s →
      (sourceBlockSize s : ℝ)/20 ≤
        (((sourceBlockCoordinates s).filter (fun i => θ i ∉ sourcePhaseMissSet s k)).card : ℝ) := by
  filter_upwards [sourcePhaseFailure_finite] with θ hθ
  have he : ∀ᶠ s in atTop, θ ∉ sourcePhaseFailure s := by
    apply Filter.eventually_atTop.mpr
    refine ⟨hθ.toFinset.sup id+1, ?_⟩
    intro s hs hm
    have hh := Finset.le_sup (f := id) (hθ.mem_toFinset.mpr hm)
    dsimp only [id] at hh
    omega
  filter_upwards [he] with s hs
  intro k hklo hkhi
  by_contra h
  have hcast : (k.natAbs : ℝ) = |(k : ℝ)| := by rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  have hnpos : 1 ≤ k.natAbs := by
    have hh : (0 : ℝ) < sourcePhaseLower s := by
      unfold sourcePhaseLower
      exact div_pos (mul_pos (sourceBlockSize_pos s) (sourceCutoff_pos s)) (by norm_num)
    have : (0 : ℝ) < k.natAbs := by rw [hcast]; exact hh.trans_le hklo
    exact_mod_cast this
  have hnupper : k.natAbs ≤ Nat.floor (sourcePhaseUpper s) := Nat.le_floor (by rwa [hcast])
  apply hs
  apply Set.mem_iUnion.mpr
  refine ⟨k.natAbs, Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hnpos, hnupper⟩, ?_⟩⟩
  rw [ite_eq_left (by rwa [hcast])]
  change (((sourceBlockCoordinates s).filter
    (fun i => θ i ∉ sourcePhaseMissSet s (k.natAbs : ℤ))).card : ℝ) < (sourceBlockSize s : ℝ)/20
  rw [sourcePhaseMissSet_natAbs]
  exact lt_of_not_ge h

end
end FiniteFactor

end OAI
