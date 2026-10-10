import OAI.NumberTheory.CubicMoment.Transform.MetaplecticAuxiliary

namespace OAI

/-! The raw HB2000 Lemma 1 input and its elementary fixed-level
specialization. The divisor restriction remains literal; reindexing to
the original Gauss series is proved below. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticDivisorPartialSum (r : Eisenstein) (X : ℝ) : ℂ :=
  ∑' c : {c : PrimaryArgument // r ∣ (c:Eisenstein)},
    if norm (c:PrimaryArgument) ≤ X then gauss (c:PrimaryArgument) else 0

/-- HB2000 Lemma 1, angular index zero and epsilon 1/12. -/
def HeathBrownGaussPartialSums : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Eisenstein, primary r → Squarefree r → ∀ X : ℝ, 1 ≤ X →
    norm r ≤ X^(1/3:ℝ) →
    ‖metaplecticDivisorPartialSum r X‖ ≤
      C*(X^(5/6:ℝ)/norm r+X^(3/4:ℝ)/Real.sqrt (norm r))

def primaryMultiplesEquiv {r : Eisenstein} (hr : primary r) :
    PrimaryArgument ≃ {c : PrimaryArgument // r ∣ (c:Eisenstein)} :=
  Equiv.ofBijective (fun u => ⟨⟨r*u,primary_mul hr u.property⟩,dvd_mul_right _ _⟩) (by
    constructor
    · intro u v h
      apply Subtype.ext
      apply mul_left_cancel₀ (primary_ne_zero hr)
      exact congrArg (fun c : {c : PrimaryArgument // r ∣ (c:Eisenstein)} =>
        (c.val:Eisenstein)) h
    · intro c
      obtain ⟨u,hu⟩ := c.property
      have hp : primary (r*u) := by rw [← hu]; exact c.val.property
      refine ⟨⟨u,primary_of_mul hr hp⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hu.symm)

lemma metaplecticDivisorPartialSum_scaled {r : Eisenstein} (hr : primary r) (U : ℝ) :
    metaplecticDivisorPartialSum r (norm r*U) = metaplecticPartialSum r U := by
  have hR : 0 < norm r := norm_pos_of_ne_zero (primary_ne_zero hr)
  rw [metaplecticDivisorPartialSum,← (primaryMultiplesEquiv hr).tsum_eq]
  apply tsum_congr
  intro u
  change (if norm (r*u) ≤ norm r*U then gauss (r*u) else 0) =
    (if norm u ≤ U then gauss (r*u) else 0)
  simp only [norm_mul_eq,mul_le_mul_iff_right₀ hR]

lemma heathBrown_partial_sum_large {r : Eisenstein} (hr : primary r) (hs : Squarefree r)
    (hHB : HeathBrownGaussPartialSums) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U : ℝ, max 1 (norm r)^2 ≤ U →
      ‖metaplecticPartialSum r U‖ ≤ C*U^(5/6:ℝ) := by
  obtain ⟨C,hC,hHB⟩ := hHB
  have hR : 1 ≤ norm r := one_le_norm (primary_ne_zero hr)
  refine ⟨C*(norm r^(-1/6:ℝ)+norm r^(1/4:ℝ)),by positivity,?_⟩
  intro U hU
  have hU1 : 1 ≤ U := (show (1:ℝ) ≤ norm r^2 from one_le_pow₀ hR).trans
    (by simpa only [max_eq_right hR] using hU)
  have hRU : 1 ≤ norm r*U := one_le_mul_of_one_le_of_one_le hR hU1
  have hcube : norm r ≤ (norm r*U)^(1/3:ℝ) := by
    have hR3 : norm r^3 ≤ norm r*U := by
      have hU' : norm r^2 ≤ U := by simpa only [max_eq_right hR] using hU
      nlinarith [mul_le_mul_of_nonneg_left hU' (norm_nonneg r)]
    have h := (Real.le_rpow_inv_iff_of_pos (norm_nonneg r)
      (mul_nonneg (norm_nonneg r) (zero_le_one.trans hU1)) (by norm_num : (0:ℝ) < 3)).mpr
      (by simpa only [Real.rpow_ofNat] using hR3)
    simpa only [one_div] using h
  have hb := hHB r hr hs (norm r*U) hRU hcube
  rw [metaplecticDivisorPartialSum_scaled hr] at hb
  have hUexp : U^(3/4:ℝ) ≤ U^(5/6:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hU1 (by norm_num)
  have hRpos : 0 < norm r := zero_lt_one.trans_le hR
  have he1 : (norm r*U)^(5/6:ℝ)/norm r = norm r^(-1/6:ℝ)*U^(5/6:ℝ) := by
    rw [Real.mul_rpow (norm_nonneg _) (zero_le_one.trans hU1),div_eq_mul_inv,
      ← Real.rpow_neg_one,← mul_right_comm,← Real.rpow_add hRpos]
    norm_num
  have he2 : (norm r*U)^(3/4:ℝ)/Real.sqrt (norm r) =
      norm r^(1/4:ℝ)*U^(3/4:ℝ) := by
    rw [Real.mul_rpow (norm_nonneg _) (zero_le_one.trans hU1),Real.sqrt_eq_rpow,
      div_eq_mul_inv,← Real.rpow_neg (norm_nonneg _),← mul_right_comm,← Real.rpow_add hRpos]
    norm_num
  rw [he1,he2] at hb
  have hcomp := mul_le_mul_of_nonneg_left hUexp
    (Real.rpow_nonneg (norm_nonneg r) (1/4:ℝ))
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hcomp hC])

end CubicFirstMoment

end

end OAI
