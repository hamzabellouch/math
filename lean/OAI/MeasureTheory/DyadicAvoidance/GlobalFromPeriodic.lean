import OAI.MeasureTheory.DyadicAvoidance.PeriodicMeasure

namespace OAI

noncomputable section

open Set MeasureTheory

namespace Problem310Support

/-- A small open deletion from the unit interval leaves a compact set
whose volume is strictly greater than the requested threshold. -/
theorem compact_complement_volume {C : Set ℝ} (hC : IsOpen C)
    {η : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hsmall : volume (C ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (η / 2)) :
    IsCompact (Icc (0 : ℝ) 1 \ C) ∧
      ENNReal.ofReal (1 - η) < volume (Icc (0 : ℝ) 1 \ C) := by
  refine ⟨isCompact_Icc.diff hC, ?_⟩
  have hfinite : volume (C ∩ Icc (0 : ℝ) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hdiff : Icc (0 : ℝ) 1 \ C =
      Icc (0 : ℝ) 1 \ (C ∩ Icc (0 : ℝ) 1) := by
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rw [hdiff, measure_sdiff inter_subset_right
    (hC.measurableSet.inter measurableSet_Icc).nullMeasurableSet hfinite,
    Real.volume_Icc]
  norm_num only [sub_zero, ENNReal.ofReal_one]
  have hstrict : ENNReal.ofReal (1 - η) < ENNReal.ofReal (1 - η / 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  refine hstrict.trans_le ?_
  rw [ENNReal.ofReal_sub 1 (by positivity), ENNReal.ofReal_one]
  exact tsub_le_tsub_left hsmall 1

/-- Every positive scale can be moved into `[1,2]` by a natural power
of two followed by passage to a dyadic tail. -/
theorem positive_scale_normalization {s : ℝ} (hs : 0 < s) :
    ∃ j m : ℕ, (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) ∈ Icc (1 : ℝ) 2 := by
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (1 / s) (by norm_num : (1 : ℝ) < 2)
  have hlarge : 1 ≤ s * (2 : ℝ) ^ j := by
    have := (div_lt_iff₀ hs).mp hj
    nlinarith
  obtain ⟨m, hm₀, hm₁⟩ := exists_nat_pow_near hlarge (by norm_num : (1 : ℝ) < 2)
  refine ⟨j, m, ?_, ?_⟩
  · rw [inv_pow]
    exact (le_mul_inv_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).mpr (by simpa using hm₀)
  · rw [inv_pow]
    apply (mul_inv_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).mpr
    rw [pow_succ] at hm₁
    nlinarith

/-- The paired pullbacks used to cover all signed scales. -/
def signedDyadicUnion (H : ℕ → Set ℝ) : Set ℝ :=
  ⋃ j : ℕ, ({x : ℝ | (2 : ℝ) ^ j * x ∈ H j} ∪
    {x : ℝ | -((2 : ℝ) ^ j * x) ∈ H j})

theorem signedDyadicUnion_open {H : ℕ → Set ℝ} (hH : ∀ j, IsOpen (H j)) :
    IsOpen (signedDyadicUnion H) := by
  apply isOpen_iUnion
  intro j
  exact ((hH j).preimage (continuous_const.mul continuous_id)).union
    ((hH j).preimage (continuous_const.mul continuous_id).neg)

theorem signedDyadicUnion_neg {H : ℕ → Set ℝ} {x : ℝ}
    (hx : x ∈ signedDyadicUnion H) : -x ∈ signedDyadicUnion H := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  rcases hj with hj | hj
  · right
    simpa only [mem_ofPred_eq, mul_neg, neg_neg] using hj
  · left
    simpa only [mem_ofPred_eq, mul_neg] using hj

/-- The full signed-scale hitting property is a purely algebraic consequence
of a normalized hitting set at every dyadic magnification. -/
theorem signedDyadicUnion_hits {H : ℕ → Set ℝ}
    (hH : ∀ j (x t : ℝ), t ∈ Icc (1 : ℝ) 2 →
      ∃ n : ℕ, 1 ≤ n ∧ x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H j) :
    ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
      x + s * ((2 : ℝ)⁻¹ ^ n) ∈ signedDyadicUnion H := by
  have hpos : ∀ x s : ℝ, 0 < s → ∃ n : ℕ, 1 ≤ n ∧
      x + s * ((2 : ℝ)⁻¹ ^ n) ∈ signedDyadicUnion H := by
    intro x s hs
    obtain ⟨j, m, hscale⟩ := positive_scale_normalization hs
    obtain ⟨n, hn, hhit⟩ := hH j ((2 : ℝ) ^ j * x)
      (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) hscale
    refine ⟨m + n, by omega, mem_iUnion.mpr ⟨j, Or.inl ?_⟩⟩
    change (2 : ℝ) ^ j * (x + s * ((2 : ℝ)⁻¹ ^ (m + n))) ∈ H j
    have heq : (2 : ℝ) ^ j * (x + s * ((2 : ℝ)⁻¹ ^ (m + n))) =
        (2 : ℝ) ^ j * x +
          (s * (2 : ℝ) ^ j * ((2 : ℝ)⁻¹ ^ m)) * ((2 : ℝ)⁻¹ ^ n) := by
      rw [pow_add]
      ring
    rwa [heq]
  intro x s hs
  rcases lt_or_gt_of_ne hs with hs | hs
  · obtain ⟨n, hn, hhit⟩ := hpos (-x) (-s) (neg_pos.mpr hs)
    refine ⟨n, hn, ?_⟩
    have := signedDyadicUnion_neg hhit
    simpa only [neg_add, neg_neg, neg_mul] using this
  · exact hpos x s hs

/-- The cost of pairing and summing the dyadic pullbacks is at most
 twice the sum of the original period densities. -/
theorem signedDyadicUnion_volume_le {H : ℕ → Set ℝ}
    (hH : ∀ j, ∀ x : ℝ, x + 1 ∈ H j ↔ x ∈ H j) :
    volume (signedDyadicUnion H ∩ Icc (0 : ℝ) 1) ≤
      ∑' j : ℕ, 2 * volume (H j ∩ Icc (0 : ℝ) 1) := by
  rw [signedDyadicUnion, iUnion_inter]
  refine (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun j => ?_)
  rw [union_inter_distrib_right, two_mul]
  refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      periodic_dilate_unit_volume_le (hH j) (n := 2 ^ j) (by positivity)
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      periodic_neg_dilate_unit_volume_le (hH j) (n := 2 ^ j) (by positivity)

theorem dyadic_density_budget {η : ℝ} (hη : 0 ≤ η) :
    (∑' j : ℕ, (2 : ENNReal) *
      ENNReal.ofReal (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j)))) =
        ENNReal.ofReal (η / 2) := by
  have hterm (j : ℕ) : (2 : ENNReal) *
      ENNReal.ofReal (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j))) =
        ENNReal.ofReal (η / 4) * ((2 : ENNReal)⁻¹ ^ j) := by
    calc
      (2 : ENNReal) * ENNReal.ofReal (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j))) =
          ENNReal.ofReal (2 * (6 * (η / 48 * ((2 : ℝ)⁻¹ ^ j)))) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      _ = ENNReal.ofReal (η / 4 * ((2 : ℝ)⁻¹ ^ j)) := by
        congr 1
        ring
      _ = ENNReal.ofReal (η / 4) * ((2 : ENNReal)⁻¹ ^ j) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]
  calc
    ENNReal.ofReal (η / 4) * 2 = ENNReal.ofReal ((η / 4) * 2) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      norm_num
    _ = ENNReal.ofReal (η / 2) := by congr 1; ring

/-- The global compact avoidance theorem follows from the periodic hitting
lemma. All measure estimates, signed scales, and strict volume loss are
included in this implication. -/
theorem avoidance_of_periodic_hitting
    (hperiodic : ∀ p : ℝ, 0 < p → p < 1 → ∃ H : Set ℝ,
      IsOpen H ∧ (∀ x : ℝ, x + 1 ∈ H ↔ x ∈ H) ∧
      volume (H ∩ Icc (0 : ℝ) 1) ≤ ENNReal.ofReal (6 * p) ∧
      ∀ x t : ℝ, t ∈ Icc (1 : ℝ) 2 → ∃ n : ℕ, 1 ≤ n ∧
        x + t * ((2 : ℝ)⁻¹ ^ n) ∈ H) :
    ∀ η : ℝ, 0 < η → η < 1 → ∃ E : Set ℝ,
      E ⊆ Icc (0 : ℝ) 1 ∧ IsCompact E ∧
      volume E > ENNReal.ofReal (1 - η) ∧
      ∀ x s : ℝ, s ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧
        x + s * ((2 : ℝ)⁻¹ ^ n) ∉ E := by
  intro η hη hη1
  let p : ℕ → ℝ := fun j => η / 48 * ((2 : ℝ)⁻¹ ^ j)
  have hp₀ (j : ℕ) : 0 < p j := by dsimp [p]; positivity
  have hp₁ (j : ℕ) : p j < 1 := by
    have hpow : (2 : ℝ)⁻¹ ^ j ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    have hcoef : 0 ≤ η / 48 := by positivity
    have hp_le : p j ≤ η / 48 := by
      dsimp [p]
      exact mul_le_of_le_one_right hcoef hpow
    linarith
  choose H hOpen hPer hDensity hHit using fun j => hperiodic (p j) (hp₀ j) (hp₁ j)
  have hsmall : volume (signedDyadicUnion H ∩ Icc (0 : ℝ) 1) ≤
      ENNReal.ofReal (η / 2) := by
    refine (signedDyadicUnion_volume_le hPer).trans ?_
    calc
      (∑' j : ℕ, (2 : ENNReal) * volume (H j ∩ Icc (0 : ℝ) 1)) ≤
          ∑' j : ℕ, (2 : ENNReal) * ENNReal.ofReal (6 * p j) :=
        ENNReal.tsum_le_tsum fun j => mul_le_mul_right (hDensity j) 2
      _ = ENNReal.ofReal (η / 2) := dyadic_density_budget hη.le
  have hcompact := compact_complement_volume (signedDyadicUnion_open hOpen) hη hη1 hsmall
  refine ⟨Icc (0 : ℝ) 1 \ signedDyadicUnion H, sdiff_subset, hcompact.1, hcompact.2, ?_⟩
  intro x s hs
  obtain ⟨n, hn, hhit⟩ := signedDyadicUnion_hits hHit x s hs
  exact ⟨n, hn, fun hx => hx.2 hhit⟩

end Problem310Support

end

end OAI
