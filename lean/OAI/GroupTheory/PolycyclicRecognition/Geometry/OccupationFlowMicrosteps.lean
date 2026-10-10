import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationMicrostepLimit
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CoarseFlowBounds

namespace OAI

/-! # Exact microstep decomposition of a continuous one-parameter subgroup -/

noncomputable section

namespace PolycyclicRecognition

open Filter MeasureTheory
open scoped Topology NNReal

variable {G : Type*} [Group G] [PseudoMetricSpace G] [IsIsometricSMul G G]

/-- A fixed integer microstep leaves a remainder of uniformly bounded
length. The endpoint factorization is exact. -/
theorem exists_flow_microstep_bound (d : ℝ → G) (hd : Continuous d)
    (hd0 : d 0 = 1) (hmul : ∀ s t, d (s + t) = d s * d t) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L : ℕ, 0 < L → ∀ t : ℝ, 0 < t →
      let n := ⌊t / (L : ℝ)⌋₊
      (n : ℝ) * L ≤ t ∧ t ≤ ((n : ℝ) + 1) * L ∧
      dist 1 (d (t - (n : ℝ) * L)) ≤ D * L ∧
      d L ^ n * d (t - (n : ℝ) * L) = d t := by
  obtain ⟨C, hC, hbound⟩ := continuous_flow_coarse_bound d hd hd0 hmul
  have hpow (s : ℝ) (n : ℕ) : d ((n : ℝ) * s) = d s ^ n := by
    induction n with
    | zero => simp [hd0]
    | succ n ih => rw [Nat.cast_succ, add_mul, one_mul, hmul, ih, pow_succ]
  refine ⟨2 * C, by positivity, ?_⟩
  intro L hL t ht
  dsimp only
  let n := ⌊t / (L : ℝ)⌋₊
  have hLr : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hlo : (n : ℝ) * L ≤ t :=
    (le_div_iff₀ hLr).mp (Nat.floor_le (div_nonneg ht.le hLr.le))
  have hhi : t ≤ ((n : ℝ) + 1) * L :=
    ((div_lt_iff₀ hLr).mp (Nat.lt_floor_add_one (t / (L : ℝ)))).le
  refine ⟨hlo, hhi, ?_, ?_⟩
  · apply (hbound _).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    nlinarith
  · rw [← hpow, ← hmul]
    congr 1
    ring

end PolycyclicRecognition

end

end OAI
