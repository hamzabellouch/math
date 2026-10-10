import OAI.Analysis.CircleDomains.Modulus.CriticalFiberLength
import Mathlib.Tactic.Finiteness

namespace OAI

/-! Bounded plane sets have finite two-dimensional Hausdorff measure;
exhaustion therefore removes the finite-measure restriction in the
critical-fiber argument. -/
open Set Function Filter MeasureTheory Metric Bornology
open scoped ENNReal NNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

lemma bounded_plane_hausdorff_two_lt_top {A : Set ℂ} (hA : IsBounded A) :
    (μH[2] : Measure ℂ) A < ∞ := by
  have h := Complex.antilipschitz_equivRealProd.le_hausdorffMeasure_image
    (by norm_num : (0 : ℝ) ≤ 2) A
  rw [MeasureTheory.hausdorffMeasure_prod_real] at h
  apply h.trans_lt
  apply ENNReal.mul_lt_top
  · finiteness
  · exact (Complex.lipschitz_equivRealProd.isBounded_image hA).measure_lt_top

lemma measurableSet_planar_critical {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    MeasurableSet (D ∩ {z | fderiv ℝ f z = 0}) := by
  let g : ℂ → ℝ := D.piecewise (fun z => ‖fderiv ℝ f z‖) (fun _ => 0)
  have hc := (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).norm
  have hg : Measurable g := hc.measurable_piecewise continuousOn_const hD.measurableSet
  have heq : D ∩ {z | fderiv ℝ f z = 0} = D ∩ g ⁻¹' {0} := by
    ext z
    by_cases hz : z ∈ D <;> simp [g, hz]
  rw [heq]
  exact hD.measurableSet.inter (hg (measurableSet_singleton _))

lemma ae_zero_planar_critical_fiber {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) :
    ∀ᵐ y, (μH[1] : Measure ℂ) ((D ∩ {z | fderiv ℝ f z = 0}) ∩ f ⁻¹' {y}) = 0 := by
  let A : Set ℂ := D ∩ {z | fderiv ℝ f z = 0}
  have hA : MeasurableSet A := measurableSet_planar_critical hD hf
  let S : ℕ → Set ℂ := fun n => A ∩ closedBall 0 n
  have hS : ∀ n, MeasurableSet (S n) := fun _ => hA.inter isClosed_closedBall.measurableSet
  have hcover : (⋃ n, S n) = A := by
    simp only [S, ← inter_iUnion, iUnion_closedBall_nat, inter_univ]
  have hn : ∀ n, ∀ᵐ y, (μH[1] : Measure ℂ) (S n ∩ f ⁻¹' {y}) = 0 := by
    intro n
    apply ae_zero_critical_fiber_length hD hf (hS n)
    · exact inter_subset_left.trans inter_subset_left
    · exact bounded_plane_hausdorff_two_lt_top (isBounded_closedBall.subset inter_subset_right)
    · exact fun z hz => hz.1.2
  filter_upwards [ae_all_iff.mpr hn] with y hy
  change (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) = 0
  apply le_antisymm _ bot_le
  calc
    (μH[1] : Measure ℂ) (A ∩ f ⁻¹' {y}) =
        (μH[1] : Measure ℂ) (⋃ n, S n ∩ f ⁻¹' {y}) := by rw [← iUnion_inter, hcover]
    _ ≤ ∑' n, (μH[1] : Measure ℂ) (S n ∩ f ⁻¹' {y}) := measure_iUnion_le _
    _ = 0 := by simp only [hy, tsum_zero]

lemma ae_zero_weighted_planar_critical_fiber {D : Set ℂ} (hD : IsOpen D)
    {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D) (q : ℂ → ℝ≥0∞) :
    ∀ᵐ y, (∫⁻ z in ((D ∩ {z | fderiv ℝ f z = 0}) ∩ f ⁻¹' {y}), q z ∂μH[1]) = 0 := by
  filter_upwards [ae_zero_planar_critical_fiber hD hf] with y hy
  rw [Measure.restrict_eq_zero.mpr hy]
  exact lintegral_zero_measure q

end CircleDomainRigidity

end

end OAI
