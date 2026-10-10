import OAI.Analysis.CircleDomains.Modulus.GridIncidence
import OAI.Analysis.CircleDomains.Modulus.BandIncidence
import OAI.Analysis.CircleDomains.Transfer.GridSummability

namespace OAI

/-!
# Finite terminal flags from actual independent grid shifts

For two different coordinate labels, their lattice-hit events have
product probability. Countably many flagged points and finitely many
label pairs can therefore be counted by Tonelli. Square-summable band
widths imply a finite expected collision count, hence only finitely many
flagged collisions for almost every choice of the grids.
-/

open Set MeasureTheory Function
open scoped ENNReal

namespace CircleDomainRigidity.FiniteTransfer

def pairedLatticeIncidence {n : ℕ} (h a b c d : ℝ) (i j : Fin n) :
    Set (Fin n → ℝ) :=
  {θ | θ i ∈ latticeBandIncidence h a b ∧ θ j ∈ latticeBandIncidence h c d}

theorem measurableSet_pairedLatticeIncidence {n : ℕ} {h : ℝ} (hh : 0 < h)
    (a b c d : ℝ) (i j : Fin n) :
    MeasurableSet (pairedLatticeIncidence h a b c d i j) :=
  ((measurableSet_latticeBandIncidence hh a b).preimage (measurable_pi_apply i)).inter
    ((measurableSet_latticeBandIncidence hh c d).preimage (measurable_pi_apply j))

theorem measure_pairedLatticeIncidence_le {n : ℕ} {h : ℝ} (hh : 0 < h)
    (a b c d : ℝ) {i j : Fin n} (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin n => shiftLaw h)) (pairedLatticeIncidence h a b c d i j) ≤
      ENNReal.ofReal (min 1 ((b - a) / h)) * ENNReal.ofReal (min 1 ((d - c) / h)) := by
  let := shiftLaw_isProbabilityMeasure hh
  have hprod := (measurePreserving_grid_pair (shiftLaw h) hij).measure_preimage
    (((measurableSet_latticeBandIncidence hh a b).prod
      (measurableSet_latticeBandIncidence hh c d)).nullMeasurableSet)
  change (Measure.pi (fun _ : Fin n => shiftLaw h))
    (pairedLatticeIncidence h a b c d i j) = _ at hprod
  rw [hprod, Measure.prod_prod]
  exact mul_le_mul' (shiftLaw_latticeBandIncidence_le hh a b)
    (shiftLaw_latticeBandIncidence_le hh c d)

noncomputable def gridCollisionCount {n : ℕ} {P S : Type*}
    (h : ℝ) (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ)
    (θ : Fin n → ℝ) : ℝ≥0∞ :=
  weightedBandIncidence
    (fun ps : P × S => pairedLatticeIncidence h (a (pairs ps.1).1 ps.2)
      (b (pairs ps.1).1 ps.2) (a (pairs ps.1).2 ps.2) (b (pairs ps.1).2 ps.2)
      (pairs ps.1).1 (pairs ps.1).2) (fun _ => 1) θ

/-- Exact pair laws and Tonelli yield the expected collision bound. -/
theorem lintegral_gridCollisionCount_le {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ) :
    (∫⁻ θ, gridCollisionCount h pairs a b θ
      ∂Measure.pi (fun _ : Fin n => shiftLaw h)) ≤
      ∑ p, ∑' s, ENNReal.ofReal (min 1 ((b (pairs p).1 s - a (pairs p).1 s) / h)) *
        ENNReal.ofReal (min 1 ((b (pairs p).2 s - a (pairs p).2 s) / h)) := by
  unfold gridCollisionCount
  rw [lintegral_weightedBandIncidence]
  · simp only [ENNReal.ofReal_one, one_mul]
    rw [ENNReal.tsum_prod', tsum_fintype]
    exact Finset.sum_le_sum (fun p _ => ENNReal.tsum_le_tsum fun s =>
      measure_pairedLatticeIncidence_le hh _ _ _ _ (hpairs p))
  · intro ps
    exact measurableSet_pairedLatticeIncidence hh _ _ _ _ _ _

/-- The product majorant for two square-summable band widths is
summable at every positive grid spacing. -/
theorem summable_grid_pair_probabilities {S : Type*} {h : ℝ} (hh : 0 < h)
    (a b : S → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (ha2 : Summable (fun s => a s ^ 2)) (hb2 : Summable (fun s => b s ^ 2)) :
    Summable (fun s => min 1 (a s / h) * min 1 (b s / h)) := by
  have hs := (LengthArea.summable_mul_of_squares ha2 hb2).div_const (h * h)
  apply hs.of_norm_bounded
  intro s
  have hma : 0 ≤ min 1 (a s / h) := le_min zero_le_one (div_nonneg (ha s) hh.le)
  have hmb : 0 ≤ min 1 (b s / h) := le_min zero_le_one (div_nonneg (hb s) hh.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hma hmb)]
  calc
    _ ≤ (a s / h) * (b s / h) :=
      mul_le_mul (min_le_right _ _) (min_le_right _ _) hmb (div_nonneg (ha s) hh.le)
    _ = (a s * b s) / (h * h) := by ring

theorem tsum_grid_pair_probabilities_lt_top {S : Type*} {h : ℝ} (hh : 0 < h)
    (a b : S → ℝ) (ha : ∀ s, 0 ≤ a s) (hb : ∀ s, 0 ≤ b s)
    (ha2 : Summable (fun s => a s ^ 2)) (hb2 : Summable (fun s => b s ^ 2)) :
    (∑' s, ENNReal.ofReal (min 1 (a s / h)) * ENNReal.ofReal (min 1 (b s / h))) < ∞ := by
  have hnonneg (s) : 0 ≤ min 1 (a s / h) * min 1 (b s / h) :=
    mul_nonneg (le_min zero_le_one (div_nonneg (ha s) hh.le))
      (le_min zero_le_one (div_nonneg (hb s) hh.le))
  have heq : (∑' s, ENNReal.ofReal (min 1 (a s / h)) *
      ENNReal.ofReal (min 1 (b s / h))) =
      ENNReal.ofReal (∑' s, min 1 (a s / h) * min 1 (b s / h)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hnonneg
      (summable_grid_pair_probabilities hh a b ha hb ha2 hb2)]
    apply tsum_congr
    intro s
    exact (ENNReal.ofReal_mul (le_min zero_le_one (div_nonneg (ha s) hh.le))).symm
  rw [heq]
  exact ENNReal.ofReal_lt_top

/-- Square-summable band widths make the actual expected collision
count finite, rather than merely a formal upper bound. -/
theorem lintegral_gridCollisionCount_lt_top {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (hpairs : ∀ p, (pairs p).1 ≠ (pairs p).2)
    (a b : Fin n → S → ℝ)
    (hwidth : ∀ i s, 0 ≤ b i s - a i s)
    (hwidth2 : ∀ i, Summable (fun s => (b i s - a i s) ^ 2)) :
    (∫⁻ θ, gridCollisionCount h pairs a b θ
      ∂Measure.pi (fun _ : Fin n => shiftLaw h)) < ∞ := by
  apply (lintegral_gridCollisionCount_le hh pairs hpairs a b).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro p _
  exact tsum_grid_pair_probabilities_lt_top hh
    (fun s => b (pairs p).1 s - a (pairs p).1 s)
    (fun s => b (pairs p).2 s - a (pairs p).2 s)
    (hwidth (pairs p).1) (hwidth (pairs p).2)
    (hwidth2 (pairs p).1) (hwidth2 (pairs p).2)

/-- A finite expected collision count has only finitely many active
pair/flag incidences almost surely. Thus its projection onto flagged
points is finite as well. -/
theorem ae_finite_grid_collision_flags {n : ℕ} {P S : Type*}
    [Fintype P] [Countable S] {h : ℝ} (hh : 0 < h)
    (pairs : P → Fin n × Fin n) (a b : Fin n → S → ℝ)
    (hfinite : (∫⁻ θ, gridCollisionCount h pairs a b θ
      ∂Measure.pi (fun _ : Fin n => shiftLaw h)) < ∞) :
    ∀ᵐ θ ∂Measure.pi (fun _ : Fin n => shiftLaw h),
      {s | ∃ p, θ ∈ pairedLatticeIncidence h (a (pairs p).1 s) (b (pairs p).1 s)
        (a (pairs p).2 s) (b (pairs p).2 s) (pairs p).1 (pairs p).2}.Finite := by
  have hmeas : Measurable (gridCollisionCount h pairs a b) :=
    measurable_weightedBandIncidence _ _ (fun ps =>
      measurableSet_pairedLatticeIncidence hh _ _ _ _ _ _)
  filter_upwards [ae_lt_top hmeas hfinite.ne] with θ hθ
  have hactive : {ps : P × S | θ ∈ pairedLatticeIncidence h
      (a (pairs ps.1).1 ps.2) (b (pairs ps.1).1 ps.2)
      (a (pairs ps.1).2 ps.2) (b (pairs ps.1).2 ps.2)
      (pairs ps.1).1 (pairs ps.1).2}.Finite := by
    have hf := ENNReal.finite_const_le_of_tsum_ne_top hθ.ne (by norm_num : (1 : ℝ≥0∞) ≠ 0)
    apply hf.subset
    intro ps hps
    change θ ∈ pairedLatticeIncidence h
      (a (pairs ps.1).1 ps.2) (b (pairs ps.1).1 ps.2)
      (a (pairs ps.1).2 ps.2) (b (pairs ps.1).2 ps.2)
      (pairs ps.1).1 (pairs ps.1).2 at hps
    change 1 ≤ (pairedLatticeIncidence h
      (a (pairs ps.1).1 ps.2) (b (pairs ps.1).1 ps.2)
      (a (pairs ps.1).2 ps.2) (b (pairs ps.1).2 ps.2)
      (pairs ps.1).1 (pairs ps.1).2).indicator (fun _ => ENNReal.ofReal 1) θ
    simp only [indicator_of_mem hps, ENNReal.ofReal_one, le_refl]
  convert hactive.image Prod.snd using 1
  ext s
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨(p, s), hp, rfl⟩
  · rintro ⟨⟨p, s'⟩, hp, rfl⟩
    exact ⟨p, hp⟩

end CircleDomainRigidity.FiniteTransfer

end OAI
