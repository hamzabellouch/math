import OAI.Analysis.IrrationalRotation.Analysis.RationalGraphTrimming
import OAI.Analysis.IrrationalRotation.Rotation.CircleWeightSupport

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem trimming_measurePreserving_coordinate (i : ℕ) :
    MeasurePreserving (p.coordinate i) circleMeasure
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  change MeasurePreserving
    (fun x : UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (p.q i • x)) : ℝ))
    volume (volume.restrict (Ico (0 : ℝ) 1))
  simpa only [natCast_zsmul] using
    CircleWeightSupport.measurePreserving_characterRepresentative (p.q i : ℤ)
      (by exact_mod_cast (hp.q_pos i).ne')

theorem measure_coordinate_boundary_le (i : ℕ) (b : ℝ) :
    circleMeasure {x | 1 - b ≤ p.coordinate i x} ≤ ENNReal.ofReal b := by
  change circleMeasure (p.coordinate i ⁻¹' Ici (1 - b)) ≤ _
  rw [(hp.trimming_measurePreserving_coordinate i).measure_preimage measurableSet_Ici.nullMeasurableSet,
    Measure.restrict_apply measurableSet_Ici]
  calc
    volume (Ici (1 - b) ∩ Ico 0 1) ≤ volume (Ico (1 - b) 1) := by
      apply measure_mono
      intro z hz
      exact ⟨hz.1, hz.2.2⟩
    _ = ENNReal.ofReal b := by rw [Real.volume_Ico]; congr 1; ring

theorem measure_finite_boundary_union_le (s : Finset ℕ) (b : ℝ) :
    circleMeasure (⋃ i ∈ s, {x | 1 - b ≤ p.coordinate i x}) ≤
      ENNReal.ofReal ((s.card : ℝ) * b) := by
  calc
    _ ≤ ∑ i ∈ s, circleMeasure {x | 1 - b ≤ p.coordinate i x} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal b :=
      Finset.sum_le_sum fun i _ => hp.measure_coordinate_boundary_le i b
    _ = ENNReal.ofReal ((s.card : ℝ) * b) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

theorem measure_future_block_boundary_le (j s : ℕ) (hs : 1 ≤ s) :
    circleMeasure (⋃ i ∈ p.block s,
      {x | 1 - 2 * p.Q j / p.N s ≤ p.coordinate i x}) ≤
      ENNReal.ofReal (2 * p.Q j / (p.K s : ℝ)) := by
  have h := hp.measure_finite_boundary_union_le (p.block s) (2 * p.Q j / p.N s)
  rw [p.card_block s hs] at h
  have hm : (p.m s : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos s hs).ne'
  convert h using 2
  unfold N
  field_simp

omit hp in

theorem rationalGraphBad_subset (A j : ℕ) :
    p.rationalGraphBad A j ⊆
      (⋃ i ∈ Finset.Icc A (p.blockEnd (j - 1)),
        {x | 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j ≤ p.coordinate i x}) ∪
      (⋃ n : ℕ, ⋃ i ∈ p.block (j + 1 + n),
        {x | 1 - 2 * p.Q j / p.N (j + 1 + n) ≤ p.coordinate i x}) := by
  intro x hx
  change ¬ ((∀ i, A ≤ i → i ≤ p.blockEnd (j - 1) →
    p.coordinate i x < 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j) ∧
    ∀ s, j < s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * p.Q j / p.N s) at hx
  by_cases hearly : ∀ i, A ≤ i → i ≤ p.blockEnd (j - 1) →
      p.coordinate i x < 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j
  · right
    have hfuture : ¬ ∀ s, j < s → ∀ i ∈ p.block s,
        p.coordinate i x < 1 - 2 * p.Q j / p.N s :=
      fun hf => hx ⟨hearly, hf⟩
    push Not at hfuture
    obtain ⟨s, hjs, i, hi, hbad⟩ := hfuture
    have hs : j + 1 + (s - (j + 1)) = s := by omega
    apply mem_iUnion.mpr
    refine ⟨s - (j + 1), ?_⟩
    rw [hs]
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hbad⟩⟩
  · left
    push Not at hearly
    obtain ⟨i, hAi, hia, hi⟩ := hearly
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hAi, hia⟩, hi⟩⟩

theorem measure_early_boundary_le {A : ℕ} (hA : 1 ≤ A) (j : ℕ) :
    circleMeasure (⋃ i ∈ Finset.Icc A (p.blockEnd (j - 1)),
      {x | 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j ≤ p.coordinate i x}) ≤
      ENNReal.ofReal ((p.blockEnd (j - 1) : ℝ) *
        (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j) := by
  have hcard : (Finset.Icc A (p.blockEnd (j - 1))).card ≤ p.blockEnd (j - 1) := by
    rw [Nat.card_Icc]
    omega
  have hb : 0 ≤ (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j := by
    unfold ell
    positivity
  calc
    _ ≤ ENNReal.ofReal (((Finset.Icc A (p.blockEnd (j - 1))).card : ℝ) *
        ((p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j)) :=
      hp.measure_finite_boundary_union_le _ _
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb)

theorem measure_future_boundary_le (j : ℕ) :
    circleMeasure (⋃ n : ℕ, ⋃ i ∈ p.block (j + 1 + n),
      {x | 1 - 2 * p.Q j / p.N (j + 1 + n) ≤ p.coordinate i x}) ≤
      ENNReal.ofReal (2 * p.Q j * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ))) := by
  have hK : Summable (fun n : ℕ => 1 / (p.K (j + 1 + n) : ℝ)) := by
    have h := (summable_nat_add_iff j).mpr hp.summable_reciprocal
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hsum : Summable (fun n : ℕ => 2 * p.Q j / (p.K (j + 1 + n) : ℝ)) := by
    simpa only [mul_one_div] using hK.mul_left (2 * p.Q j)
  calc
    _ ≤ ∑' n : ℕ, circleMeasure (⋃ i ∈ p.block (j + 1 + n),
        {x | 1 - 2 * p.Q j / p.N (j + 1 + n) ≤ p.coordinate i x}) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * p.Q j / (p.K (j + 1 + n) : ℝ)) :=
      ENNReal.tsum_le_tsum fun n => hp.measure_future_block_boundary_le j (j + 1 + n) (by omega)
    _ = ENNReal.ofReal (∑' n : ℕ, 2 * p.Q j / (p.K (j + 1 + n) : ℝ)) := by
      symm
      apply ENNReal.ofReal_tsum_of_nonneg _ hsum
      intro n
      exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Nat.cast_nonneg _)
    _ = _ := by
      congr 1
      simpa only [mul_one_div] using
        (tsum_mul_left : (∑' n : ℕ, (2 * p.Q j) *
          (1 / (p.K (j + 1 + n) : ℝ))) =
          (2 * p.Q j) * ∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ))

theorem measure_rationalGraphBad_le {A j : ℕ} (hA : 1 ≤ A) (hj : 1 ≤ j) :
    circleMeasure (p.rationalGraphBad A j) ≤
      ENNReal.ofReal (1 / ((j + 1 : ℕ) : ℝ)^2 +
        4 * p.Q j / (p.K (j + 1) : ℝ)) := by
  have hearly := hp.measure_early_boundary_le hA j
  have hfuture := hp.measure_future_boundary_le j
  calc
    _ ≤ circleMeasure ((⋃ i ∈ Finset.Icc A (p.blockEnd (j - 1)),
        {x | 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j ≤ p.coordinate i x}) ∪
        (⋃ n : ℕ, ⋃ i ∈ p.block (j + 1 + n),
        {x | 1 - 2 * p.Q j / p.N (j + 1 + n) ≤ p.coordinate i x})) :=
      measure_mono (rationalGraphBad_subset (p := p) A j)
    _ ≤ _ := (measure_union_le _ _).trans ((add_le_add hearly hfuture).trans (by
      rw [← ENNReal.ofReal_add (by unfold ell; positivity) (by
        apply mul_nonneg
        · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        · exact tsum_nonneg fun n => one_div_nonneg.mpr (Nat.cast_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (hp.discarded_mass_bound j hj)))

theorem tendsto_measure_rationalGraphBad {A : ℕ} (hA : 1 ≤ A) :
    Filter.Tendsto (fun n : ℕ => circleMeasure (p.rationalGraphBad A (n + 1)))
      Filter.atTop (nhds 0) := by
  have hbound := ENNReal.tendsto_ofReal hp.tendsto_discarded_mass_bound
  simp only [ENNReal.ofReal_zero] at hbound
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
  · intro n
    exact zero_le
  · intro n
    simpa only [Nat.add_assoc] using hp.measure_rationalGraphBad_le hA (show 1 ≤ n + 1 by omega)

end Invariant233.CircleParameterLaws

end

end OAI
