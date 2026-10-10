import OAI.Analysis.CircleDomains.Topology.SimpleArcToll
import OAI.Analysis.CircleDomains.Sobolev.ExtendedWeightedCoarea

namespace OAI

/-! Square-summable point weights and level-incidence bounds give finite
atomic payment on almost every prior level. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem ae_finite_atomic_level_payment
    {X T : Type*} [MeasurableSpace X] [MeasurableSpace T]
    (ν : Measure T) (H : T → Set X)
    (hH : ∀t, MeasurableSet (H t))
    (hsection : ∀x, MeasurableSet {t | x ∈ H t})
    (m a : X → ℝ≥0∞)
    (hm : (∑'x, m x ^ 2) ≠ ∞) (ha : (∑'x, a x ^ 2) ≠ ∞)
    (hincidence : ∀x, ν {t | x ∈ H t} ≤ a x) :
    ∀ᵐt ∂ν, atomicBoundaryMeasure m (H t) < ∞ := by
  have hcount : (support m).Countable := by
    simpa only [support, ne_eq, sq_eq_zero_iff] using
      (Summable.countable_support_ennreal hm)
  let : Countable (support m) := hcount.to_subtype
  let L : T → ℝ≥0∞ := fun t => ∑'x : support m,
    ({t | x.val ∈ H t}).indicator (fun _ => m x.val) t
  have hL : Measurable L := Measurable.tsum fun x =>
    measurable_const.indicator (hsection x.val)
  have hmass (t : T) : atomicBoundaryMeasure m (H t) = L t := by
    rw [atomicBoundaryMeasure_apply m (hH t)]
    have he : (∑'x : support m, (H t).indicator m x.val) = ∑'x, (H t).indicator m x := by
      apply tsum_subtype_eq_of_support_subset
      intro x hx
      by_contra hmzero
      have hz : m x = 0 := not_not.mp hmzero
      simp only [mem_support] at hx
      exact hx (by simp [hz])
    rw [← he]
    apply tsum_congr
    intro x
    by_cases hx : x.val ∈ H t <;> simp [hx]
  have hfinite : (∫⁻t, L t ∂ν) < ∞ := by
    calc
      _ = ∑'x : support m, m x.val * ν {t | x.val ∈ H t} := by
        rw [show (∫⁻t, L t ∂ν) =
          ∫⁻t, ∑'x : support m, ({t | x.val ∈ H t}).indicator (fun _ => m x.val) t ∂ν from rfl,
          lintegral_tsum]
        · exact tsum_congr fun x => lintegral_indicator_const (hsection x.val) _
        · intro x
          exact (measurable_const.indicator (hsection x.val)).aemeasurable
      _ ≤ ∑'x : support m, (m x.val ^ 2 + a x.val ^ 2) := by
        apply ENNReal.tsum_le_tsum
        intro x
        exact (mul_le_mul_right (hincidence x.val) (m x.val)).trans
          (ennreal_mul_le_sq_add_sq (m x.val) (a x.val))
      _ = (∑'x : support m, m x.val ^ 2) + ∑'x : support m, a x.val ^ 2 :=
        ENNReal.tsum_add
      _ ≤ (∑'x, m x ^ 2) + ∑'x, a x ^ 2 := add_le_add
        (ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun x : support m => (x.val : X)) Subtype.val_injective (fun x => m x ^ 2))
        (ENNReal.tsum_comp_le_tsum_of_injective
          (f := fun x : support m => (x.val : X)) Subtype.val_injective (fun x => a x ^ 2))
      _ < ∞ := ENNReal.add_lt_top.mpr ⟨hm.lt_top, ha.lt_top⟩
  filter_upwards [ae_lt_top hL hfinite.ne] with t ht
  rwa [hmass]

end CircleDomainRigidity

end

end OAI
