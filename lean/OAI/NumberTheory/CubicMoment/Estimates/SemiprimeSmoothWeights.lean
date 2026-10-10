import OAI.NumberTheory.CubicMoment.Estimates.SemiprimeBilinear
import OAI.NumberTheory.CubicMoment.Estimates.CompactParameterWeights
import OAI.NumberTheory.CubicMoment.Estimates.SmoothPartitionCount

namespace OAI

/-! The roughness transition in each actual semiprime norm piece belongs
to a single uniform smooth family. Capping its scale ratio at two is an
identity on the fixed norm support, so all logarithmic derivatives are
uniform even when the original ratio is unbounded. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def semiprimeSmoothWeight (r x : ℝ) : ℂ :=
  normPartitionWeight x*(1-(primeDetectorCutoff (r*x):ℂ))

lemma semiprimeSmoothWeight_low (r : ℝ) {x : ℝ} (hx : x < 1) :
    semiprimeSmoothWeight r x = 0 := by
  rw [semiprimeSmoothWeight,normPartitionWeight_low hx,zero_mul]

lemma semiprimeSmoothWeight_high (r : ℝ) {x : ℝ} (hx : 2 < x) :
    semiprimeSmoothWeight r x = 0 := by
  rw [semiprimeSmoothWeight,normPartitionWeight_high hx,zero_mul]

lemma semiprimeSmoothWeight_norm (r x : ℝ) : ‖semiprimeSmoothWeight r x‖ ≤ 1 := by
  have hc : ‖1-(primeDetectorCutoff (r*x):ℂ)‖ ≤ 1 := by
    have he : (1-(primeDetectorCutoff (r*x):ℂ)) =
        ((1-primeDetectorCutoff (r*x):ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg
      (sub_nonneg.mpr (primeDetectorCutoff_le_one _))]
    linarith [primeDetectorCutoff_nonneg (r*x)]
  rw [semiprimeSmoothWeight,norm_mul]
  exact (mul_le_mul (normPartitionWeight_norm x) hc (_root_.norm_nonneg _) zero_le_one).trans_eq
    (one_mul 1)

lemma semiprimeSmoothWeight_capped (r x : ℝ) :
    semiprimeSmoothWeight (min r 2) x = semiprimeSmoothWeight r x := by
  by_cases hr : r ≤ 2
  · rw [min_eq_left hr]
  · rw [min_eq_right (le_of_not_ge hr)]
    by_cases hx : x < 1
    · rw [semiprimeSmoothWeight_low _ hx,semiprimeSmoothWeight_low _ hx]
    · have hx1 : 1 ≤ x := le_of_not_gt hx
      have hr2 : 2 ≤ r := le_of_not_ge hr
      rw [semiprimeSmoothWeight,semiprimeSmoothWeight,
        primeDetectorCutoff_zero (by nlinarith : 2 ≤ 2*x),
        primeDetectorCutoff_zero (by nlinarith : 2 ≤ r*x)]

def semiprimeSmoothWeights :
    UniformLogWeights (fun r : Ici (0:ℝ) => semiprimeSmoothWeight r) := by
  have hcont : ContDiff ℝ ∞ (Function.uncurry semiprimeSmoothWeight) := by
    exact (normPartitionWeight_smooth.comp contDiff_snd).mul
      (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp
        (primeDetectorCutoff_smooth.comp (contDiff_fst.mul contDiff_snd))))
  let h := uniformLogWeights_compactParameter (Icc (0:ℝ) 2) isCompact_Icc
    semiprimeSmoothWeight normPartitionWeight normPartitionWeight_compact
    normPartitionWeight_positive_support normPartitionWeight_smooth hcont
    (fun r _ _ hx => (mul_ne_zero_iff.mp hx).1)
  let c : Ici (0:ℝ) → Icc (0:ℝ) 2 := fun r =>
    ⟨min (r:ℝ) 2,le_min r.property (by norm_num),min_le_right _ _⟩
  have he : (fun r : Ici (0:ℝ) => semiprimeSmoothWeight (c r)) =
      (fun r : Ici (0:ℝ) => semiprimeSmoothWeight r) := by
    funext r x
    exact semiprimeSmoothWeight_capped r x
  rw [← he]
  refine ⟨fun r => h.compact (c r),fun r => h.positive (c r),fun r => h.smooth (c r),
    h.radius,h.radius_nonneg,fun r => h.support_bound (c r),?_⟩
  intro n
  obtain ⟨B,hB,hbound⟩ := h.derivative_bound n
  exact ⟨B,hB,fun r => hbound (c r)⟩

lemma semiprimeSmoothWeight_at_prime (X : ℝ) {A : ℝ} (hA : 0 < A)
    (p : Eisenstein) :
    semiprimeSmoothWeight (A/(X^(2/5:ℝ))) (norm p/A) =
      semiprimeRoughWeight X p*normPartitionWeight (norm p/A) := by
  have he : (A/(X^(2/5:ℝ)))*(norm p/A) = norm p/(X^(2/5:ℝ)) := by
    simp only [div_eq_mul_inv]
    calc
      A*(X^(2/5:ℝ))⁻¹*(norm p*A⁻¹) = (A*A⁻¹)*(norm p*(X^(2/5:ℝ))⁻¹) := by ring
      _ = norm p*(X^(2/5:ℝ))⁻¹ := by rw [mul_inv_cancel₀ hA.ne',one_mul]
  rw [semiprimeSmoothWeight,he,semiprimeRoughWeight,mul_comm]

end CubicFirstMoment

end

end OAI
