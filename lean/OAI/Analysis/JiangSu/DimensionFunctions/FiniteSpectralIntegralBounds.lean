import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzRescaling
import OAI.Analysis.JiangSu.CuntzSemigroup.FiniteCuntzOrthogonal
import OAI.Analysis.JiangSu.Comparison.ContinuousSupportComparison
import OAI.Analysis.JiangSu.CuntzSemigroup.PositiveCutOrder

namespace OAI

noncomputable section
namespace Pureness
open TraceCone MeasureTheory Set
open scoped ENNReal NNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma positive_cut_zero_of_norm_le {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (M : Positive D) (ε : ℝ≥0)
    (h : ‖M.1‖ ≤ ε) : Positive.cut ε M = Positive.zero := by
  apply Subtype.ext
  change cfcₙ (fun t : ℝ => max (t-ε) 0) M.1 = 0
  refine (cfcₙ_congr ?_).trans (cfcₙ_zero ℝ M.1)
  intro t ht
  have htN : t ≤ ‖M.1‖ := (le_abs_self t).trans
    (NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le M.1 ht
      (IsSelfAdjoint.of_nonneg M.2))
  exact max_eq_right (sub_nonpos.mpr (htN.trans h))

lemma positive_projection_cut_zero {D : Type*} [NonUnitalCStarAlgebra D]
    [PartialOrder D] [StarOrderedRing D] (p : Positive D) (hp : IsIdempotentElem p.1)
    (ε : ℝ≥0) (hε : 1 ≤ ε) : Positive.cut ε p = Positive.zero := by
  apply Subtype.ext
  change cfcₙ (fun t : ℝ => max (t-ε) 0) p.1 = 0
  refine (cfcₙ_congr ?_).trans (cfcₙ_zero ℝ p.1)
  intro t ht
  have hs : t = 0 ∨ t = 1 := by
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hp.quasispectrum_subset ℝ ht
  rcases hs with rfl | rfl
  · simp
  · exact max_eq_right (sub_nonpos.mpr hε)

lemma positive_halfline_indicator_integral (r : ℝ) (v : ℝ≥0∞) :
    (∫⁻ t in Ioi (0 : ℝ), (Iio r).indicator (fun _ => v) t) = v * ENNReal.ofReal r := by
  rw [lintegral_indicator measurableSet_Iio,lintegral_const,
    Measure.restrict_restrict measurableSet_Iio,Measure.restrict_apply_univ]
  have heq : Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r := by ext t; simp [and_comm]
  rw [heq,Real.volume_Ioo,sub_zero]

theorem finiteSpectralIntegral_le
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) :
    finiteSpectralIntegral d n M ≤ d (finitePositiveClass n M)*ENNReal.ofReal ‖M.1‖ := by
  rw [← positive_halfline_indicator_integral]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  by_cases htN : t < ‖M.1‖
  · rw [Set.indicator_of_mem (show t ∈ Iio ‖M.1‖ from htN)]
    apply hd
    apply (finitePositiveClass_le_iff n _ _).mpr
    exact (cuntzSubequiv_iff_shared _ _).mpr (TraceCone.CuntzBelow.of_le _ _ (Positive.cut_le _ M))
  · rw [Set.indicator_of_notMem (show t ∉ Iio ‖M.1‖ from htN)]
    have hcut := positive_cut_zero_of_norm_le M t.toNNReal
      ((le_of_not_gt htN).trans (Real.le_coe_toNNReal t))
    simp only [finiteDimensionDistribution,hcut,finitePositiveClass_zero,map_zero,le_refl]

theorem finiteSpectralIntegral_ne_top
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (M : Positive (FinMatrix A n)) (hfinite : d (finitePositiveClass n M) ≠ ⊤) :
    finiteSpectralIntegral d n M ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top hfinite ENNReal.ofReal_ne_top)
    (finiteSpectralIntegral_le d hd n M)

theorem finiteSpectralIntegral_projection
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (p : Positive (FinMatrix A n)) (hp : IsIdempotentElem p.1) :
    finiteSpectralIntegral d n p = d (finitePositiveClass n p) := by
  calc
    finiteSpectralIntegral d n p =
        ∫⁻ t in Ioi (0 : ℝ), (Iio (1 : ℝ)).indicator (fun _ => d (finitePositiveClass n p)) t := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : 0 < t := ht
      by_cases ht1 : t < 1
      · rw [Set.indicator_of_mem (show t ∈ Iio (1 : ℝ) from ht1)]
        unfold finiteDimensionDistribution
        rw [finiteProjection_cut_class n p hp t.toNNReal (by
          change (t.toNNReal : ℝ) < 1
          rwa [Real.coe_toNNReal t ht0.le])]
      · rw [Set.indicator_of_notMem (show t ∉ Iio (1 : ℝ) from ht1)]
        have hcut := positive_projection_cut_zero p hp t.toNNReal (by
          change (1 : ℝ) ≤ t.toNNReal
          rw [Real.coe_toNNReal t ht0.le]
          exact le_of_not_gt ht1)
        simp only [finiteDimensionDistribution,hcut,finitePositiveClass_zero,map_zero]
    _ = d (finitePositiveClass n p) := by rw [positive_halfline_indicator_integral]; simp

theorem finiteDimensionDistribution_mono
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (t : ℝ) : Monotone (fun M : Positive (FinMatrix A n) => finiteDimensionDistribution d n M t) := by
  intro M N hMN
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  exact (cuntzSubequiv_iff_shared _ _).mpr
    (positive_cut_cuntzBelow_of_le M N hMN t.toNNReal)

theorem finiteSpectralIntegral_monotone
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d) (n : ℕ) :
    Monotone (finiteSpectralIntegral d n) := by
  intro M N hMN
  exact lintegral_mono (fun t => finiteDimensionDistribution_mono d hd n t hMN)

end Pureness

namespace Pureness
open TraceCone Set MeasureTheory
open scoped ComplexOrder NNReal ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def finiteContinuousDimension (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f : C(X, ℝ≥0)) : ℝ≥0∞ :=
  d (finitePositiveClass n (Positive.map φ (continuousNNRealPositive f)))

lemma finiteContinuousDimension_monotone
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) : Monotone (finiteContinuousDimension d n φ) := by
  intro f g hfg
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  apply (cuntzSubequiv_iff_shared _ _).mpr
  exact (CuntzBelow.of_le _ _ (continuousNNRealPositive_mono hfg)).map φ

lemma positiveMap_continuousNNReal_add (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n)
    (f g : C(X, ℝ≥0)) :
    Positive.map φ (continuousNNRealPositive (f+g)) =
      Positive.add (Positive.map φ (continuousNNRealPositive f)) (Positive.map φ (continuousNNRealPositive g)) := by
  rw [continuousNNRealPositive_add]
  apply Subtype.ext
  exact map_add φ _ _

lemma finiteContinuousDimension_add_le
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f g : C(X, ℝ≥0)) :
    finiteContinuousDimension d n φ (f+g) ≤ finiteContinuousDimension d n φ f+finiteContinuousDimension d n φ g := by
  unfold finiteContinuousDimension
  rw [positiveMap_continuousNNReal_add,← map_add]
  exact hd (finitePositiveClass_sum_le n _ _)

lemma finiteContinuousDimension_add_orthogonal
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f g : C(X, ℝ≥0)) (h : f*g = 0) :
    finiteContinuousDimension d n φ (f+g) = finiteContinuousDimension d n φ f+finiteContinuousDimension d n φ g := by
  unfold finiteContinuousDimension
  rw [positiveMap_continuousNNReal_add,finitePositiveClass_orthogonal_add,map_add]
  change φ (continuousNNRealPositive f).1*φ (continuousNNRealPositive g).1 = 0
  rw [← map_mul,continuousNNRealPositive_mul_zero f g h,map_zero]

lemma finiteContinuousDimension_support_mono
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f g : C(X, ℝ≥0))
    (h : ∀ x, 0 < f x → 0 < g x) :
    finiteContinuousDimension d n φ f ≤ finiteContinuousDimension d n φ g := by
  apply hd
  apply (finitePositiveClass_le_iff n _ _).mpr
  apply (cuntzSubequiv_iff_shared _ _).mpr
  exact (continuousNNRealPositive_cuntzBelow_of_support f g h).map φ

lemma finiteContinuousDimension_cuts
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (n : ℕ) (φ : C(X, ℂ) →⋆ₙₐ[ℂ] FinMatrix A n) (f : C(X, ℝ≥0)) :
    finiteContinuousDimension d n φ f = ⨆ (ε : ℝ≥0) (_ : 0 < ε), finiteContinuousDimension d n φ (continuousNNRealCut ε f) := by
  have hreg := congrArg (fun e : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞ =>
    e (finitePositiveClass n (Positive.map φ (continuousNNRealPositive f))))
    (regularizedFiniteDimension_eq_of_lowerSemicontinuous d hd hlsc)
  rw [regularizedFiniteDimension_eval] at hreg
  unfold finiteContinuousDimension
  rw [← hreg]
  simp only [finiteRegularizedValue,continuousNNRealPositive_cut,Positive.map_cut]

end Pureness
end

end OAI
