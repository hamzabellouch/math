import OAI.NumberTheory.DukePrimeDegree.Geometry.RootTranslateLeaves
import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootOrbitRebase

namespace OAI

/-!
# Lebesgue normalization for invariant roots

A preserving root action fixes its intrinsic leaf. The pointwise rebasing
law turns this into projective translation periods; diagonal covariance
removes their multipliers. Arbitrarily small periods identify Lebesgue
measure, giving the exact mean information coefficient one.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace DukePrimeDegree
open PrimeDegreePackets

variable (d : ℕ) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)

include hA in
lemma ae_based_fixed_of_root_invariant (a : ℝ)
    (hinv : μ.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, basedRealMeasure (intrinsicRootLeaf hij μ x) a = intrinsicRootLeaf hij μ x := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  obtain ⟨N, hN, hz, hrebase⟩ := exists_nullset_root_orbit_rebase d hij μ hA
  have hn : ∀ᵐ x ∂μ, x ∉ N := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hz
  have hpre : ∀ᵐ x ∂μ, rightAction x (Matrix.SpecialLinearGroup.transvection hij a) ∉ N := by
    have hm : ∀ᵐ y ∂μ.map (fun x => rightAction x
        (Matrix.SpecialLinearGroup.transvection hij a)), y ∉ N := by rwa [hinv]
    exact ae_of_ae_map (continuous_rightAction
      (Matrix.SpecialLinearGroup.transvection hij a)).measurable.aemeasurable hm
  filter_upwards [hn, hpre, ae_intrinsicRootLeaf_translate hij a μ hfree hinv] with x hx htx he
  exact (hrebase x hx a htx).symm.trans he

include hA in
/-- Every invariant root has translation-invariant intrinsic conditionals. -/
theorem ae_rootLeaf_invariant_of_root_invariant
    (hinv : ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, ∀ a : ℝ,
      (intrinsicRootLeaf hij μ x).map (fun t => t + a) = intrinsicRootLeaf hij μ x := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  have hfixed : ∀ᵐ x ∂μ, ∀ k : ℕ,
      basedRealMeasure (intrinsicRootLeaf hij μ x) (-(1 / ((k : ℝ) + 1))) =
        intrinsicRootLeaf hij μ x :=
    ae_all_iff.mpr fun k => ae_based_fixed_of_root_invariant d hij μ hA _ (hinv _)
  filter_upwards [hfixed, ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_intrinsic_projective_multiplier_zero d hij μ hA] with x hx hs hm
  let ν := intrinsicRootLeaf hij μ x
  let : IsLocallyFiniteMeasure ν := hs.1
  apply realLeaf_invariant_of_small_periods ν
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  let a : ℝ := 1 / ((k : ℝ) + 1)
  have hp := projectivePeriod_of_based_fixed ν hs.2 (-a) (hx k)
  have hz := hm _ hp
  have hper := leaf_period_of_projective_multiplier_zero ν _ hp hz
  refine ⟨a, ?_, by dsimp [a]; positivity, hk⟩
  simpa only [neg_neg] using hper

include hA in
/-- Unit mass on the unit ball fixes the Haar scalar to one half. -/
theorem ae_rootLeaf_eq_half_volume
    (hinv : ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) :
    ∀ᵐ x ∂μ, intrinsicRootLeaf hij μ x = (2 : ℝ≥0∞)⁻¹ • (volume : Measure ℝ) := by
  have hfree : ∀ᵐ x ∂μ, ∀ t : ℝ,
      rightAction x (Matrix.SpecialLinearGroup.transvection hij t) = x → t = 0 :=
    (ae_root_stabilizer_trivial d μ hA).mono fun x hx => hx i j hij
  filter_upwards [ae_intrinsicRootLeaf_spec hij μ hfree,
    ae_rootLeaf_invariant_of_root_invariant d hij μ hA hinv] with x hs hi
  let : IsLocallyFiniteMeasure (intrinsicRootLeaf hij μ x) := hs.1
  obtain ⟨c, hc, hcV⟩ := normalized_translation_invariant_measure
    (intrinsicRootLeaf hij μ x) (Metric.ball 0 1) hs.2 hi
  rw [hc, ENNReal.smul_def, hcV, Real.volume_ball]
  norm_num

include hA in
theorem ae_rootInformation_of_invariant
    (hinv : ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) (t : ℝ) :
    ∀ᵐ x ∂μ, rootInformation hij μ t x = t := by
  filter_upwards [ae_rootLeaf_eq_half_volume d hij μ hA hinv] with x hx
  change -Real.log ((intrinsicRootLeaf hij μ x) (Metric.ball 0 (Real.exp (-t)))).toReal = t
  rw [hx, Measure.smul_apply, smul_eq_mul, Real.volume_ball,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have he : (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal 2 * ENNReal.ofReal (Real.exp (-t))) =
      ENNReal.ofReal (Real.exp (-t)) := by
    rw [ENNReal.ofReal_ofNat, ← mul_assoc,
      ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_mul]
  rw [he, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp, neg_neg]

include hA in
/-- Haar root conditionals give coefficient one in the actual leaf information. -/
theorem rootInformationMean_of_invariant [IsProbabilityMeasure μ]
    (hinv : ∀ a : ℝ, μ.map (fun x => rightAction x
      (Matrix.SpecialLinearGroup.transvection hij a)) = μ) (t : ℝ) :
    rootInformationMean hij μ t = ENNReal.ofReal t := by
  unfold rootInformationMean
  have he : (fun x => ENNReal.ofReal (rootInformation hij μ t x)) =ᵐ[μ]
      fun _ => ENNReal.ofReal t :=
    (ae_rootInformation_of_invariant d hij μ hA hinv t).mono fun _ h => congrArg ENNReal.ofReal h
  rw [lintegral_congr_ae he]
  simp

end DukePrimeDegree

end

end OAI
