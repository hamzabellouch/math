import OAI.Analysis.CircleDomains.Selection.FlagIntersectionCount
import OAI.Analysis.CircleDomains.Selection.SquareVisitTolls

namespace OAI

/-! The countable flags contribute finitely many distinct intersections
for almost every independently chosen level. Repeated visits are paid
only through the actual path law's square bound.
-/

open Set Function Filter MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]
  [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]

theorem measurable_flag_intersection_count
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (S : Set X) (hS : S.Countable) :
    Measurable (fun p : C(PathTime, X) × UnitAddCircle =>
      pathImageCount (S ∩ {x | (p.2, x) ∈ H}) p.1) := by
  let : Countable S := hS.to_subtype
  simp_rw [pathImageCount_inter_eq_tsum]
  apply Measurable.tsum
  intro x
  apply measurable_const.piecewise _ measurable_const
  exact (((isClosed_paths_hitting x.val).preimage continuous_fst).inter
    (hH.preimage (continuous_snd.prodMk continuous_const))).measurableSet

theorem ae_flag_intersection_count_finite_of_sum
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (S : Set X) (hS : S.Countable) (a : X → ℝ≥0∞)
    (hband : ∀ x ∈ S, volume {t : UnitAddCircle | (t, x) ∈ H} ≤ a x)
    (μ : ProbabilityMeasure C(PathTime, X))
    (hsum : (∑' x : S, a x.val * pathHitProbability μ x.val) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), ∀ᵐ t : UnitAddCircle ∂volume,
      pathImageCount (S ∩ {x | (t, x) ∈ H}) γ < ∞ := by
  let : Countable S := hS.to_subtype
  have hmean : (∫⁻ t : UnitAddCircle, ∫⁻ γ,
      pathImageCount (S ∩ {x | (t, x) ∈ H}) γ ∂(μ : Measure _)) < ∞ :=
    (mean_flag_intersection_count_le hH S hS a hband μ).trans_lt hsum
  have hc := measurable_flag_intersection_count hH S hS
  have hm := (hc.comp measurable_swap).lintegral_prod_right' (ν := (μ : Measure _))
  have hg : ∀ᵐ t : UnitAddCircle ∂volume, ∀ᵐ γ ∂(μ : Measure _),
      pathImageCount (S ∩ {x | (t, x) ∈ H}) γ < ∞ := by
    filter_upwards [ae_lt_top hm hmean.ne] with t ht
    exact ae_lt_top (hc.comp (measurable_id.prodMk measurable_const)) ht.ne
  have hmeas : MeasurableSet {p : C(PathTime, X) × UnitAddCircle |
      pathImageCount (S ∩ {x | (p.2, x) ∈ H}) p.1 < ∞} :=
    measurableSet_lt hc measurable_const
  exact (Measure.ae_ae_comm hmeas).mpr hg

theorem ae_flag_intersection_count_finite
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (S : Set X) (hS : S.Countable) (a : X → ℝ≥0∞)
    (hband : ∀ x ∈ S, volume {t : UnitAddCircle | (t, x) ∈ H} ≤ a x)
    (μ : ProbabilityMeasure C(PathTime, X))
    (ha : countingSquareNorm (fun x : S => a x.val) < ∞)
    (hhit : countingSquareNorm (fun x : S => pathHitProbability μ x.val) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), ∀ᵐ t : UnitAddCircle ∂volume,
      pathImageCount (S ∩ {x | (t, x) ∈ H}) γ < ∞ := by
  let : Countable S := hS.to_subtype
  exact ae_flag_intersection_count_finite_of_sum hH S hS a hband μ
    ((tsum_mul_le_countingSquareNorm _ _).trans_lt (ENNReal.mul_lt_top ha hhit))

theorem tsum_flag_weight_hit_finite
    (S : Set X) (m : X → ℝ≥0∞) (μ : ProbabilityMeasure C(PathTime, X))
    (hm : (support m).Countable)
    (ha : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    (∑' x : S, m x.val * pathHitProbability μ x.val) < ∞ := by
  let : Countable (support m) := hm.to_subtype
  have hs : (∑' x : X, m x * pathHitProbability μ x) =
      ∑' x : support m, m x.val * pathHitProbability μ x.val := by
    symm
    apply tsum_subtype_eq_of_support_subset
      (f := fun x : X => m x * pathHitProbability μ x)
    intro x hx
    by_contra hn
    have hz : m x = 0 := notMem_support.mp hn
    simp only [mem_support, hz, zero_mul, ne_eq, not_true_eq_false] at hx
  calc
    _ ≤ ∑' x : X, m x * pathHitProbability μ x :=
      ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _
    _ = _ := hs
    _ ≤ countingSquareNorm (fun x : support m => m x.val) *
        countingSquareNorm (fun x : support m => pathHitProbability μ x.val) :=
      tsum_mul_le_countingSquareNorm _ _
    _ ≤ countingSquareNorm (fun x : support m => m x.val) *
        countingSquareNorm (fun x : support m => meanVisitCount μ x.val) :=
      mul_le_mul' le_rfl (countingSquareNorm_mono fun x => pathHitProbability_le_meanVisitCount μ x.val)
    _ < ∞ := ENNReal.mul_lt_top ha hvisits

theorem ae_flag_intersection_count_finite_of_support
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (S : Set X) (hS : S.Countable) (m : X → ℝ≥0∞)
    (hband : ∀ x ∈ S, volume {t : UnitAddCircle | (t, x) ∈ H} ≤ m x)
    (μ : ProbabilityMeasure C(PathTime, X))
    (hm : (support m).Countable)
    (ha : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    ∀ᵐ γ ∂(μ : Measure _), ∀ᵐ t : UnitAddCircle ∂volume,
      pathImageCount (S ∩ {x | (t, x) ∈ H}) γ < ∞ := by
  exact ae_flag_intersection_count_finite_of_sum hH S hS m hband μ
    (tsum_flag_weight_hit_finite S m μ hm ha hvisits)

theorem mean_flag_intersection_count_finite_of_support
    {H : Set (UnitAddCircle × X)} (hH : IsClosed H)
    (S : Set X) (hS : S.Countable) (m : X → ℝ≥0∞)
    (hband : ∀ x ∈ S, volume {t : UnitAddCircle | (t, x) ∈ H} ≤ m x)
    (μ : ProbabilityMeasure C(PathTime, X))
    (hm : (support m).Countable)
    (ha : countingSquareNorm (fun x : support m => m x.val) < ∞)
    (hvisits : countingSquareNorm (fun x : support m => meanVisitCount μ x.val) < ∞) :
    (∫⁻ t : UnitAddCircle, ∫⁻ γ, pathImageCount (S ∩ {x | (t, x) ∈ H}) γ
      ∂(μ : Measure _)) < ∞ :=
  (mean_flag_intersection_count_le hH S hS m hband μ).trans_lt
    (tsum_flag_weight_hit_finite S m μ hm ha hvisits)

end CircleDomainRigidity

end

end OAI
