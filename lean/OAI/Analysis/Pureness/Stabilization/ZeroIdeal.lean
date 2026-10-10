import OAI.Analysis.Pureness.Stabilization.Idempotents

namespace OAI
noncomputable section
open scoped ENNReal NNReal
namespace CuntzTrace

theorem lowerSemicontinuous_idealIndicator {α : Type*} [TopologicalSpace α]
    {I : Set α} (hI : IsClosed I) : LowerSemicontinuous (idealIndicator I) := by
  classical
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  intro r
  by_cases hr : r = ∞
  · subst r
    simp
  · have heq : idealIndicator I ⁻¹' Set.Iic r = I := by
      ext a
      simp only [Set.mem_preimage, Set.mem_Iic, idealIndicator]
      by_cases ha : a ∈ I <;> simp [ha, top_le_iff, hr]
    rw [heq]
    exact hI

variable (A : Type*) [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def zeroIdealWeight : ExtendedTrace A where
  toFun := idealIndicator {a : Positive A | a.1 = 0}
  map_zero := by simp [idealIndicator, Positive.zero]
  map_add a b := by
    classical
    have hz : a.1 + b.1 = 0 ↔ a.1 = 0 ∧ b.1 = 0 :=
      add_eq_zero_iff_of_nonneg a.2 b.2
    change (if a.1 + b.1 = 0 then (0 : ℝ≥0∞) else ∞) =
      (if a.1 = 0 then 0 else ∞) + (if b.1 = 0 then 0 else ∞)
    by_cases ha : a.1 = 0 <;> by_cases hb : b.1 = 0 <;> simp [hz, ha, hb]
  map_smul r a := by
    classical
    by_cases hr : r = 0
    · subst r
      simp [idealIndicator, Positive.smul]
    · have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
      by_cases ha : a.1 = 0
      · simp [idealIndicator, Positive.smul, ha]
      · simp [idealIndicator, Positive.smul, ha, hr, hr']
  tracial x := by
    classical
    change (if star x * x = 0 then (0 : ℝ≥0∞) else ∞) =
      (if x * star x = 0 then 0 else ∞)
    rw [CStarRing.star_mul_self_eq_zero_iff, CStarRing.mul_star_self_eq_zero_iff]
  lowerSemicontinuous := lowerSemicontinuous_idealIndicator
    (isClosed_eq continuous_subtype_val continuous_const)

@[simp] theorem zeroIdealWeight_eq_zero (a : Positive A) :
    zeroIdealWeight A a = 0 ↔ a.1 = 0 := by
  exact idealIndicator_eq_zero _ _

theorem zeroIdealWeight_lt_top (a : Positive A) :
    zeroIdealWeight A a < ∞ ↔ a.1 = 0 := by
  classical
  change idealIndicator _ a < ∞ ↔ _
  by_cases ha : a.1 = 0 <;> simp [idealIndicator, ha]

theorem zeroIdealWeight_detects (x : A) (hx : x ≠ 0) :
    zeroIdealWeight A (Positive.starMul x) = ∞ := by
  classical
  change idealIndicator _ _ = ∞
  simp [idealIndicator, Positive.starMul, CStarRing.star_mul_self_eq_zero_iff, hx]

end CuntzTrace

end

end OAI
