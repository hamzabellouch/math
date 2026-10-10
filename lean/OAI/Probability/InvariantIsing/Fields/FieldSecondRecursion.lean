import OAI.Probability.InvariantIsing.Fields.FieldSecondMeanBounds

namespace OAI

/-! Closure of the actual finite scalar recursion under two derivatives
on every interval with positive, bounded affine variances. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing
namespace FieldSecondFamily

variable {I : Set ℝ} (F : FieldSecondFamily I)

def secondTransform (hI : IsOpen I) (a v ζ : ℝ) {m V : ℝ} (hm : 0 < m)
    (hlo : ∀ t ∈ I, m ≤ a + v * t) (hhi : ∀ t ∈ I, a + v * t ≤ V) :
    FieldSecondFamily I :=
  let R := |v| / (2 * Real.sqrt m)
  let D := (|v| / 2) * m⁻¹ * R
  { toFieldSmoothFamily := F.toFieldSmoothFamily.transform hI a v ζ
      (fun t ht => hm.trans_le (hlo t ht))
    TX := F.mixedMean a v ζ
    TT := F.secondMean a v ζ
    KTX := F.mixedMeanCap R ζ V
    KTT := F.secondMeanCap R D ζ V
    mTX := F.measurable_mixedMean a v ζ
    mTT := F.measurable_secondMean a v ζ
    bTX := fun p hp => F.mixedMean_bound a v ζ hp (by dsimp only [R]; positivity)
      (abs_div_two_sqrt_le hm (hlo p.1 hp) v) (hhi p.1 hp)
    bTT := fun p hp => F.secondMean_bound a v ζ hp (by dsimp only [R]; positivity)
      (by dsimp only [D]; positivity) (abs_div_two_sqrt_le hm (hlo p.1 hp) v)
      (fieldAmplitudeCurvature_abs_le a v p.1 hm (hlo p.1 hp)) (hhi p.1 hp)
    derivativeX := fun p hp => F.mean_hasFDerivAt hI a v ζ hm hlo hhi hp
    derivativeT := fun p hp => F.tangent_hasFDerivAt hI a v ζ hm hlo hhi hp }

end FieldSecondFamily

def fieldAffineSecondFamily (I : Set ℝ) (hI : IsOpen I) (m V : ℝ) (hm : 0 < m) :
    (L : List FieldAffineStep) →
      (∀ av ∈ L, ∀ t ∈ I, m ≤ av.base + av.slope * t ∧ av.base + av.slope * t ≤ V) →
      FieldSecondFamily I
  | [], _ => fieldLogCoshSecondFamily I
  | av :: L, hL =>
      (fieldAffineSecondFamily I hI m V hm L
        (fun bv hb => hL bv (List.mem_cons_of_mem av hb))).secondTransform
        hI av.base av.slope av.exponent hm
        (fun t ht => (hL av List.mem_cons_self t ht).1)
        (fun t ht => (hL av List.mem_cons_self t ht).2)

theorem fieldAffineSecondFamily_value (I : Set ℝ) (hI : IsOpen I) (m V : ℝ) (hm : 0 < m)
    (L : List FieldAffineStep)
    (hL : ∀ av ∈ L, ∀ t ∈ I, m ≤ av.base + av.slope * t ∧ av.base + av.slope * t ≤ V) :
    (fieldAffineSecondFamily I hI m V hm L hL).U = fieldAffineValue L := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    funext p
    simp only [fieldAffineSecondFamily, FieldSecondFamily.secondTransform,
      FieldSmoothFamily.transform, FieldSmoothFamily.value, fieldAffineValue]
    rw [ih]

end InvariantIsing

end

end OAI
