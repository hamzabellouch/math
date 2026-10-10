import OAI.Analysis.IrrationalRotation.Model.ParameterSmoothing
import OAI.Analysis.IrrationalRotation.Rotation.CircleSmoothing
import OAI.Analysis.IrrationalRotation.Analysis.ContinuityCoboundary
import OAI.Analysis.IrrationalRotation.Sampling.CirclePhaseSummability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import OAI.Analysis.IrrationalRotation.Analysis.BackgroundCost

namespace OAI

namespace Invariant233

open MeasureTheory Set InvariantProjection.Continuity
open scoped ENNReal

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem block_phase_pos (j : ℕ) (hj : 1 ≤ j) (i : ℕ) (hi : i ∈ p.block j) :
    0 < p.alpha θ i := by
  have hN : 0 < p.N j := by
    unfold CircleParameterData.N
    exact mul_pos (Nat.cast_pos.mpr (hp.m_pos j hj)) (Nat.cast_pos.mpr (hp.K_pos j hj))
  exact (one_div_pos.mpr hN).trans (hp.phase_bounds j hj i hi).1

omit hp in

theorem continuous_smoothBlock (p : CircleParameterData) (θ : ℝ) (j : ℕ) :
    Continuous (p.smoothBlock θ j) := by
  unfold CircleParameterData.smoothBlock
  exact continuous_finsetSum _ (fun i _ => continuous_characterSmoothedDrop _ _ _ _)

omit hp in

theorem measurable_smoothBlockTransfer (p : CircleParameterData) (θ : ℝ) (j : ℕ) :
    Measurable (p.smoothBlockTransfer θ j) := by
  unfold CircleParameterData.smoothBlockTransfer
  apply Finset.measurable_sum
  intro i _hi
  exact (measurable_circleSmoothingTransfer _ _).comp
    (continuous_id.zsmul (p.q i : ℤ)).measurable

theorem smoothBlock_nonneg (j : ℕ) (hj : 1 ≤ j) (x : Circle) :
    0 ≤ p.smoothBlock θ j x := by
  apply Finset.sum_nonneg
  intro i hi
  apply circleSmoothedDrop_nonneg (hp.C_pos j hj).le
    (hp.block_phase_pos j hj i hi).le
  exact div_pos (hp.block_phase_pos j hj i hi) (by norm_num)

theorem integral_smoothBlock (j : ℕ) :
    (∫ x, p.smoothBlock θ j x) = p.C j * ∑ i ∈ p.block j, p.alpha θ i := by
  unfold CircleParameterData.smoothBlock
  rw [integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact integral_characterSmoothedDrop _ _ _ (by exact_mod_cast (hp.q_pos i).ne')
  · intro i hi
    exact (continuous_characterSmoothedDrop _ _ _ _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

omit hp in

theorem smoothBlock_eq_add_coboundary (j : ℕ) (x : Circle) :
    p.smoothBlock θ j x = p.rawBlock θ j x + p.smoothBlockTransfer θ j x -
      p.smoothBlockTransfer θ j (x + (θ : Circle)) := by
  unfold CircleParameterData.smoothBlock CircleParameterData.rawBlock
    CircleParameterData.smoothBlockTransfer
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  convert characterSmoothedDrop_eq_add_coboundary (p.C j) θ (p.alpha θ i / 4)
    (p.q i : ℤ) x using 1 <;>
    simp only [CircleParameterData.alpha, CircleParameterData.coordinate,
      CircleParameterData.rep, Int.cast_natCast, natCast_zsmul]

omit hp in

theorem continuous_relocatedBlock (j : ℕ) : Continuous (p.relocatedBlock θ j) := by
  exact continuous_relocated (Homeomorph.addRight (θ : Circle)) _ _ _
    (continuous_smoothBlock p θ j) (fun n _ => (p.partition j n).continuous)

omit hp in
theorem continuous_relocatedBlockTransfer (j : ℕ) :
    Continuous (p.relocatedBlockTransfer θ j) := by
  exact continuous_relocationTransfer (Homeomorph.addRight (θ : Circle)) _ _ _
    (continuous_smoothBlock p θ j) (fun n _ => (p.partition j n).continuous)

theorem relocatedBlock_nonneg (j : ℕ) (hj : 1 ≤ j) (x : Circle) :
    0 ≤ p.relocatedBlock θ j x := by
  exact relocated_nonneg _ _ _ _ (hp.smoothBlock_nonneg j hj)
    (hp.partition_nonneg j hj) x

theorem relocatedBlock_eq_add_coboundary (j : ℕ) (hj : 1 ≤ j) (x : Circle) :
    p.relocatedBlock θ j x = p.smoothBlock θ j x + p.relocatedBlockTransfer θ j x -
      p.relocatedBlockTransfer θ j (x + (θ : Circle)) := by
  exact relocated_eq_add_coboundary _ _ _ _ x (hp.partition_sum j hj x)

omit hp in
private theorem measure_support_finsetSum_le {ι : Type*} (s : Finset ι)
    (f : ι → Circle → ℝ) :
    volume (Function.support (fun x => ∑ i ∈ s, f i x)) ≤
      ∑ i ∈ s, volume (Function.support (f i)) := by
  have hsub : Function.support (fun x => ∑ i ∈ s, f i x) ⊆
      ⋃ i ∈ s, Function.support (f i) := by
    intro x hx
    by_contra hn
    apply hx
    apply Finset.sum_eq_zero
    intro i hi
    by_contra hne
    exact hn (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hne⟩⟩)
  exact (measure_mono hsub).trans (measure_biUnion_finset_le s _)

theorem measure_smoothBlock_support_le (j : ℕ) (hj : 1 ≤ j) :
    volume (Function.support (p.smoothBlock θ j)) ≤ ENNReal.ofReal (3 / (p.K j : ℝ)) := by
  have hα (i : ℕ) (hi : i ∈ p.block j) := hp.block_phase_pos j hj i hi
  calc
    _ ≤ ∑ i ∈ p.block j, volume (Function.support (fun x : Circle =>
        circleSmoothedDrop (p.C j) (p.alpha θ i) (p.alpha θ i / 4) ((p.q i : ℤ) • x))) :=
      measure_support_finsetSum_le _ _
    _ ≤ ∑ i ∈ p.block j, ENNReal.ofReal (p.alpha θ i + 2 * (p.alpha θ i / 4)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact measure_characterSmoothedDrop_support_le _ (hα i hi).le
        (div_pos (hα i hi) (by norm_num)) (by exact_mod_cast (hp.q_pos i).ne')
    _ = ENNReal.ofReal (∑ i ∈ p.block j, (p.alpha θ i + 2 * (p.alpha θ i / 4))) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i hi
      have := (hα i hi).le
      positivity
    _ ≤ ENNReal.ofReal (3 / (p.K j : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (3 / 2 : ℝ) * ∑ i ∈ p.block j, p.alpha θ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ (3 / 2 : ℝ) * (2 / (p.K j : ℝ)) :=
          mul_le_mul_of_nonneg_left (hp.block_phase_sum_le j hj) (by norm_num)
        _ = _ := by ring

theorem measure_smoothBlockTransfer_support_le (j : ℕ) (hj : 1 ≤ j) :
    volume (Function.support (p.smoothBlockTransfer θ j)) ≤
      ENNReal.ofReal (1 / (p.K j : ℝ)) := by
  have hα (i : ℕ) (hi : i ∈ p.block j) := hp.block_phase_pos j hj i hi
  calc
    _ ≤ ∑ i ∈ p.block j, volume (Function.support (fun x : Circle =>
        circleSmoothingTransfer (p.C j) (p.alpha θ i / 4) ((p.q i : ℤ) • x))) :=
      measure_support_finsetSum_le _ _
    _ ≤ ∑ i ∈ p.block j, ENNReal.ofReal (2 * (p.alpha θ i / 4)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact measure_characterSmoothingTransfer_support_le _
        (div_pos (hα i hi) (by norm_num)) (by exact_mod_cast (hp.q_pos i).ne')
    _ = ENNReal.ofReal (∑ i ∈ p.block j, 2 * (p.alpha θ i / 4)) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro i hi
      have := (hα i hi).le
      positivity
    _ ≤ ENNReal.ofReal (1 / (p.K j : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = (1 / 2 : ℝ) * ∑ i ∈ p.block j, p.alpha θ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ ≤ (1 / 2 : ℝ) * (2 / (p.K j : ℝ)) :=
          mul_le_mul_of_nonneg_left (hp.block_phase_sum_le j hj) (by norm_num)
        _ = _ := by ring

theorem measure_relocatedBlockTransfer_support_le (j : ℕ) (hj : 1 ≤ j) :
    volume (Function.support (p.relocatedBlockTransfer θ j)) ≤
      ENNReal.ofReal (3 * ((p.height j : ℝ) / p.K j)) := by
  calc
    _ ≤ (p.height j : ℝ≥0∞) * volume (Function.support (p.smoothBlock θ j)) := by
      exact measure_support_relocationTransfer_le (MeasurableEquiv.addRight (θ : Circle))
        (measurePreserving_add_right volume _) _ (continuous_smoothBlock p θ j).measurable _ _
    _ ≤ (p.height j : ℝ≥0∞) * ENNReal.ofReal (3 / (p.K j : ℝ)) :=
      mul_le_mul_right (hp.measure_smoothBlock_support_le j hj) _
    _ = ENNReal.ofReal (3 * ((p.height j : ℝ) / p.K j)) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring

theorem support_relocatedBlock_subset (j : ℕ) (hj : 1 ≤ j) :
    Function.support (p.relocatedBlock θ j) ⊆
      Metric.ball (0 : Circle) (1 / (10 * (j : ℝ))) := by
  apply support_relocated_subset
  intro n hn
  rintro y ⟨x, hx, rfl⟩
  change dist (((fun z : Circle => z + (θ : Circle))^[n]) x) 0 < _
  rw [add_right_iterate]
  have hs := hp.partition_support j hj n hn x (subset_tsupport _ hx)
  simpa only [← AddCircle.coe_nsmul, nsmul_eq_mul] using hs

theorem tsupport_relocatedBlock_subset (j : ℕ) (hj : 1 ≤ j) :
    tsupport (p.relocatedBlock θ j) ⊆
      Metric.ball (0 : Circle) (1 / (10 * (j : ℝ))) := by
  apply tsupport_relocated_subset (Homeomorph.addRight (θ : Circle))
  intro n hn
  rintro y ⟨x, hx, rfl⟩
  change dist (((fun z : Circle => z + (θ : Circle))^[n]) x) 0 < _
  rw [add_right_iterate]
  have hs := hp.partition_support j hj n hn x hx
  simpa only [← AddCircle.coe_nsmul, nsmul_eq_mul] using hs

theorem integral_relocatedBlock (j : ℕ) (hj : 1 ≤ j) :
    (∫ x, p.relocatedBlock θ j x) = p.C j * ∑ i ∈ p.block j, p.alpha θ i := by
  have ht : (∫ x, p.relocatedBlock θ j x) = ∫ x, p.smoothBlock θ j x := by
    apply integral_relocated (MeasurableEquiv.addRight (θ : Circle))
      (measurePreserving_add_right volume _)
    · intro n hn
      exact ((continuous_smoothBlock p θ j).mul (p.partition j n).continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact hp.partition_sum j hj
  exact ht.trans (hp.integral_smoothBlock j)

theorem block_phase_sum_ge (j : ℕ) (hj : 1 ≤ j) :
    1 / (p.K j : ℝ) ≤ ∑ i ∈ p.block j, p.alpha θ i := by
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  calc
    _ = ∑ _i ∈ p.block j, 1 / p.N j := by
      simp only [Finset.sum_const, nsmul_eq_mul, p.card_block j hj, CircleParameterData.N]
      field_simp
    _ ≤ _ := Finset.sum_le_sum (fun i hi => (hp.phase_bounds j hj i hi).1.le)

theorem integral_relocatedBlock_ge_K (j : ℕ) (hj : 1 ≤ j) :
    (p.K j : ℝ) ≤ ∫ x, p.relocatedBlock θ j x := by
  have hK : 0 < (p.K j : ℝ) := Nat.cast_pos.mpr (hp.K_pos j hj)
  have hC : (p.K j : ℝ) ^ 2 ≤ p.C j := by
    rw [hp.C_eq j hj]
    exact le_max_right _ _
  rw [hp.integral_relocatedBlock j hj]
  calc
    (p.K j : ℝ) ≤ p.C j * (1 / (p.K j : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ hK]
      nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left (hp.block_phase_sum_ge j hj) (hp.C_pos j hj).le

theorem tsum_smoothBlock_support_ne_top :
    (∑' n : ℕ, volume (Function.support (p.smoothBlock θ (n + 1)))) ≠ ⊤ := by
  have hsum := (hp.summable_reciprocal.mul_left 3).tsum_ofReal_ne_top
  apply ne_top_of_le_ne_top hsum
  apply ENNReal.tsum_le_tsum
  intro n
  simpa only [mul_one_div] using hp.measure_smoothBlock_support_le (n + 1) (by omega)

theorem tsum_smoothBlockTransfer_support_ne_top :
    (∑' n : ℕ, volume (Function.support (p.smoothBlockTransfer θ (n + 1)))) ≠ ⊤ := by
  apply ne_top_of_le_ne_top hp.summable_reciprocal.tsum_ofReal_ne_top
  exact ENNReal.tsum_le_tsum (fun n =>
    hp.measure_smoothBlockTransfer_support_le (n + 1) (by omega))

theorem tsum_height_mul_smoothBlock_support_ne_top :
    (∑' n : ℕ, (p.height (n + 1) : ℝ≥0∞) *
      volume (Function.support (p.smoothBlock θ (n + 1)))) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (hp.summable_partition_cost.mul_left 3).tsum_ofReal_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  have hK : 0 < (p.K (n + 1) : ℝ) := hp.shifted_K_pos n
  calc
    _ ≤ (p.height (n + 1) : ℝ≥0∞) * ENNReal.ofReal (3 / (p.K (n + 1) : ℝ)) :=
      mul_le_mul_right (hp.measure_smoothBlock_support_le (n + 1) (by omega)) _
    _ = ENNReal.ofReal (3 * ((p.height (n + 1) : ℝ) / p.K (n + 1))) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (3 * ((1 + (p.height (n + 1) : ℝ)) / p.K (n + 1))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right (by linarith) hK.le

theorem tsum_relocatedBlockTransfer_support_ne_top :
    (∑' n : ℕ, volume (Function.support (p.relocatedBlockTransfer θ (n + 1)))) ≠ ⊤ := by
  apply ne_top_of_le_ne_top hp.tsum_height_mul_smoothBlock_support_ne_top
  apply ENNReal.tsum_le_tsum
  intro n
  exact measure_support_relocationTransfer_le (MeasurableEquiv.addRight (θ : Circle))
    (measurePreserving_add_right volume _) _ (continuous_smoothBlock p θ (n + 1)).measurable _ _

theorem ae_finite_smoothing_and_relocation_support :
    ∀ᵐ x : Circle, (Function.support (fun n : ℕ => p.smoothBlock θ (n + 1) x)).Finite ∧
      (Function.support (fun n : ℕ => p.smoothBlockTransfer θ (n + 1) x)).Finite ∧
      (Function.support (fun n : ℕ => p.relocatedBlockTransfer θ (n + 1) x)).Finite := by
  have h1 := ae_finite_setOfPred_mem hp.tsum_smoothBlock_support_ne_top
  have h2 := ae_finite_setOfPred_mem hp.tsum_smoothBlockTransfer_support_ne_top
  have h3 := ae_finite_setOfPred_mem hp.tsum_relocatedBlockTransfer_support_ne_top
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  exact ⟨hx1, hx2, hx3⟩

omit hp in
private theorem shrinking_radius_tendsto_zero :
    Filter.Tendsto (fun n : ℕ => 1 / (10 * ((n + 1 : ℕ) : ℝ)))
      Filter.atTop (nhds 0) := by
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 10
  convert ht using 1
  · funext n
    push_cast
    field_simp
  · norm_num

theorem relocatedBlock_locally_finite :
    ∀ x : Circle, x ≠ 0 → ∃ s : Finset ℕ,
      ∀ᶠ y in nhds x, ∀ n ∉ s, p.relocatedBlock θ (n + 1) y = 0 := by
  apply BackgroundCost.locally_finite_of_support_shrinks 0 _ _ shrinking_radius_tendsto_zero
  intro n x hx
  exact (hp.support_relocatedBlock_subset (n + 1) (by omega) hx).le

theorem summable_relocatedBlock_of_ne_zero {x : Circle} (hx : x ≠ 0) :
    Summable (fun n : ℕ => p.relocatedBlock θ (n + 1) x) := by
  obtain ⟨s, hs⟩ := hp.relocatedBlock_locally_finite x hx
  exact summable_of_ne_finset_zero (mem_of_mem_nhds hs)

theorem continuousOn_relocatedCost : ContinuousOn (p.relocatedCost θ) ({0}ᶜ : Set Circle) := by
  exact BackgroundCost.continuousOn_tsum_of_locally_finite _ _
    (fun n => continuous_relocatedBlock (p := p) (θ := θ) (n + 1))
    (fun x hx => hp.relocatedBlock_locally_finite x hx)

theorem relocatedCost_nonneg (x : Circle) : 0 ≤ p.relocatedCost θ x :=
  tsum_nonneg (fun n => hp.relocatedBlock_nonneg (n + 1) (by omega) x)

theorem ae_summable_relocatedBlock :
    ∀ᵐ x : Circle, Summable (fun n : ℕ => p.relocatedBlock θ (n + 1) x) := by
  have hzero : volume ({0} : Set Circle) = 0 := by
    rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
    norm_num
  have hne : ∀ᵐ x : Circle, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using hzero
  exact hne.mono (fun x hx => hp.summable_relocatedBlock_of_ne_zero hx)

theorem lintegral_relocatedCost_eq_top :
    (∫⁻ x : Circle, ENNReal.ofReal (p.relocatedCost θ x)) = ⊤ := by
  have hsum : (∫⁻ x : Circle, ENNReal.ofReal (p.relocatedCost θ x)) =
      ∑' n : ℕ, ∫⁻ x : Circle, ENNReal.ofReal (p.relocatedBlock θ (n + 1) x) := by
    calc
      _ = ∫⁻ x : Circle, ∑' n : ℕ, ENNReal.ofReal (p.relocatedBlock θ (n + 1) x) := by
        apply lintegral_congr_ae
        exact hp.ae_summable_relocatedBlock.mono (fun x hx =>
          ENNReal.ofReal_tsum_of_nonneg
            (fun n => hp.relocatedBlock_nonneg (n + 1) (by omega) x) hx)
      _ = _ := lintegral_tsum (fun n =>
        (continuous_relocatedBlock (p := p) (θ := θ) (n + 1)).measurable.ennreal_ofReal.aemeasurable)
  rw [hsum]
  apply top_unique
  calc
    ⊤ = ∑' _n : ℕ, (1 : ℝ≥0∞) :=
      (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ ∑' n : ℕ, ∫⁻ x : Circle, ENNReal.ofReal (p.relocatedBlock θ (n + 1) x) := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((continuous_relocatedBlock (p := p) (θ := θ) (n + 1)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
        (Filter.Eventually.of_forall (hp.relocatedBlock_nonneg (n + 1) (by omega)))]
      apply ENNReal.one_le_ofReal.mpr
      have hK : (1 : ℝ) ≤ p.K (n + 1) := by
        exact_mod_cast hp.K_pos (n + 1) (by omega)
      exact hK.trans (hp.integral_relocatedBlock_ge_K (n + 1) (by omega))

end CircleParameterLaws
end Invariant233

end OAI
