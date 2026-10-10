import OAI.Analysis.KadisonSimilarity.Representation.KaplanskyTransform
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

namespace OAI

/-! Contractive approximate polar factors inside the original C-star algebra.
These avoid any bidual extension in the row-bound argument. -/

noncomputable section
namespace KadisonSimilarity
open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def positiveShiftReciprocal (h : A) (ε : ℝ) : A :=
  cfc (fun t : ℝ => (t + ε)⁻¹) h

theorem positiveShiftReciprocal_continuous (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ContinuousOn (fun t : ℝ => (t + ε)⁻¹) (spectrum ℝ h) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro t ht
  exact ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε)

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_selfAdjoint (h : A) (ε : ℝ) :
    IsSelfAdjoint (positiveShiftReciprocal h ε) := cfc_predicate _ h

omit [PartialOrder A] [StarOrderedRing A] in
theorem positiveShiftReciprocal_commute (h : A) (ε : ℝ) :
    Commute (positiveShiftReciprocal h ε) h := (Commute.refl h).cfc_real _

theorem positiveShiftReciprocal_inverse (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    (h + ε • (1 : A)) * positiveShiftReciprocal h ε = 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  have hid : cfc (fun t : ℝ => t + ε) h = h + ε • (1 : A) := by
    rw [cfc_add h (fun t : ℝ => t) (fun _ => ε) continuousOn_id continuousOn_const,
      cfc_id' ℝ h hh.isSelfAdjoint, cfc_const ε h hh.isSelfAdjoint]
    simp only [Algebra.algebraMap_eq_smul_one]
  rw [positiveShiftReciprocal, ← hid, ← cfc_mul _ _ h (by fun_prop) hc]
  calc
    cfc (fun t : ℝ => (t + ε) * (t + ε)⁻¹) h = cfc (fun _ : ℝ => 1) h := by
      apply cfc_congr
      intro t ht
      exact mul_inv_cancel₀ (ne_of_gt
        (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hh ht) hε))
    _ = 1 := cfc_const_one ℝ h hh.isSelfAdjoint

theorem positiveShiftReciprocal_mul_norm_le (h : A) (hh : 0 ≤ h) {ε : ℝ} (hε : 0 < ε) :
    ‖h * positiveShiftReciprocal h ε‖ ≤ 1 := by
  have hc := positiveShiftReciprocal_continuous h hh hε
  change ‖h * cfc (fun t : ℝ => (t + ε)⁻¹) h‖ ≤ 1
  conv_lhs => arg 1; arg 1; rw [← cfc_id' ℝ h hh.isSelfAdjoint]
  rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (t + ε)⁻¹) h continuousOn_id hc]
  apply norm_cfc_le zero_le_one
  intro t ht
  have ht0 := spectrum_nonneg_of_nonneg hh ht
  have hp : 0 < t + ε := add_pos_of_nonneg_of_pos ht0 hε
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht0 (inv_nonneg.mpr hp.le))]
  change t / (t + ε) ≤ 1
  exact (div_le_one hp).mpr (by linarith)

/-- The regularized polar factor is contractive without leaving the algebra. -/
theorem norm_positiveShiftReciprocal_mul_le (x h : A) (hh : 0 ≤ h)
    (hsq : x * star x = h * h) {ε : ℝ} (hε : 0 < ε) :
    ‖positiveShiftReciprocal h ε * x‖ ≤ 1 := by
  let r := positiveShiftReciprocal h ε
  have hr : star r = r := (positiveShiftReciprocal_selfAdjoint h ε).star_eq
  have hc : r * h = h * r := (positiveShiftReciprocal_commute h ε).eq
  have he : (r * x) * star (r * x) = (h * r) * (h * r) := by
    rw [star_mul, hr]
    calc
      (r * x) * (star x * r) = r * (x * star x) * r := by noncomm_ring
      _ = r * (h * h) * r := by rw [hsq]
      _ = (r * h) * (h * r) := by noncomm_ring
      _ = (h * r) * (h * r) := by rw [hc]
  have hsa : IsSelfAdjoint (h * r) :=
    (hh.isSelfAdjoint.commute_iff (positiveShiftReciprocal_selfAdjoint h ε)).mp
      (positiveShiftReciprocal_commute h ε).symm
  have heq : ‖r * x‖ ^ 2 = ‖h * r‖ ^ 2 := by
    rw [sq, ← CStarRing.norm_self_mul_star, he, hsa.norm_mul_self]
  have hn := positiveShiftReciprocal_mul_norm_le h hh hε
  nlinarith [norm_nonneg (r * x), norm_nonneg (h * r)]

/-- The error in the polar factorization has norm at most the regularizer. -/
theorem regularizedPolar_error (x h : A) (hh : 0 ≤ h)
    (hsq : x * star x = h * h) {ε : ℝ} (hε : 0 < ε) :
    ‖x - h * (positiveShiftReciprocal h ε * x)‖ ≤ ε := by
  let v := positiveShiftReciprocal h ε * x
  have hi := congrArg (fun z : A => z * x) (positiveShiftReciprocal_inverse h hh hε)
  have he : x - h * v = ε • v := by
    change (h + ε • (1 : A)) * positiveShiftReciprocal h ε * x = 1 * x at hi
    simp only [add_mul, smul_mul_assoc, one_mul, mul_assoc] at hi
    change h * v + ε • v = x at hi
    rw [← hi]
    abel
  change ‖x - h * v‖ ≤ ε
  rw [he, norm_smul, Real.norm_of_nonneg hε.le]
  exact (mul_le_mul_of_nonneg_left
    (norm_positiveShiftReciprocal_mul_le x h hh hsq hε) hε.le).trans_eq (mul_one ε)

end KadisonSimilarity

end

end OAI
