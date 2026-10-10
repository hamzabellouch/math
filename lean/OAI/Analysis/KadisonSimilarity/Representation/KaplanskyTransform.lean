import OAI.Analysis.KadisonSimilarity.Representation.SpectralStepDischarge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

namespace OAI

/-! # A bounded rational transform for Kaplansky approximation

The function `2t/(1+t²)` maps the real line into the unit interval. Its
operator difference is controlled on two fixed vectors without a bound on
the approximating selfadjoint operators. This is the bounded-transform
step in Kaplansky approximation.
-/

noncomputable section
namespace KadisonSimilarity
open ContinuousLinearMap
open scoped CStarAlgebra

variable {B : Type*} [CStarAlgebra B]

def kaplanskyReciprocal (A : B) : B :=
  cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) A

def kaplanskyTransform (A : B) : B :=
  (2 : ℝ) • (A * kaplanskyReciprocal A)

private theorem reciprocal_continuous : Continuous (fun t : ℝ => (1 + t ^ 2)⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro t
    positivity

theorem kaplanskyReciprocal_norm_le (A : B) :
    ‖kaplanskyReciprocal A‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro t _
  have ht : 0 < 1 + t ^ 2 := by positivity
  simp only [Real.norm_eq_abs, abs_inv, abs_of_pos ht]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg t])

theorem kaplanskyReciprocal_mul_norm_le (A : B) (hA : IsSelfAdjoint A) :
    ‖A * kaplanskyReciprocal A‖ ≤ 1 / 2 := by
  have hf := reciprocal_continuous.continuousOn (s := spectrum ℝ A)
  change ‖A * cfc (fun t : ℝ => (1 + t ^ 2)⁻¹) A‖ ≤ _
  conv_lhs => arg 1; arg 1; rw [← cfc_id' ℝ A hA]
  rw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => (1 + t ^ 2)⁻¹) A continuousOn_id hf]
  apply norm_cfc_le (by norm_num)
  intro t _
  have ht : 0 < 1 + t ^ 2 := by positivity
  have habs : |t| ≤ (1 + t ^ 2) / 2 := by
    nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht]
  change |t| / (1 + t ^ 2) ≤ 1 / 2
  apply (div_le_iff₀ ht).mpr
  linarith

theorem kaplanskyTransform_norm_le (A : B) (hA : IsSelfAdjoint A) :
    ‖kaplanskyTransform A‖ ≤ 1 := by
  rw [kaplanskyTransform, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [kaplanskyReciprocal_mul_norm_le A hA]

theorem kaplanskyReciprocal_right_inverse (A : B) (hA : IsSelfAdjoint A) :
    kaplanskyReciprocal A * (1 + A ^ 2) = 1 := by
  have hf := reciprocal_continuous.continuousOn (s := spectrum ℝ A)
  have hg : ContinuousOn (fun t : ℝ => 1 + t ^ 2) (spectrum ℝ A) := by fun_prop
  have he : cfc (fun t : ℝ => 1 + t ^ 2) A = 1 + A ^ 2 := by
    rw [cfc_add A (fun _ : ℝ => 1) (fun t : ℝ => t ^ 2) continuousOn_const (by fun_prop),
      cfc_const_one ℝ A hA, cfc_pow (fun t : ℝ => t) 2 A continuousOn_id hA, cfc_id' ℝ A hA]
  rw [kaplanskyReciprocal, ← he, ← cfc_mul _ _ A hf hg]
  have hone : (fun t : ℝ => (1 + t ^ 2)⁻¹ * (1 + t ^ 2)) = fun _ => 1 := by
    funext t
    exact inv_mul_cancel₀ (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)
  rw [hone, cfc_const_one ℝ A hA]

theorem kaplanskyReciprocal_commute (A : B) :
    Commute (kaplanskyReciprocal A) A :=
  (Commute.refl A).cfc_real _

theorem kaplanskyReciprocal_left_inverse (A : B) (hA : IsSelfAdjoint A) :
    (1 + A ^ 2) * kaplanskyReciprocal A = 1 := by
  calc
    (1 + A ^ 2) * kaplanskyReciprocal A = kaplanskyReciprocal A * (1 + A ^ 2) := by
      calc
        _ = kaplanskyReciprocal A + A ^ 2 * kaplanskyReciprocal A := by noncomm_ring
        _ = kaplanskyReciprocal A + kaplanskyReciprocal A * A ^ 2 := by
          rw [((kaplanskyReciprocal_commute A).symm.pow_left 2).eq]
        _ = _ := by noncomm_ring
    _ = 1 := kaplanskyReciprocal_right_inverse A hA

/-- The two error vectors are tested after fixed functions of B. No norm
bound on A occurs in the resulting strong approximation argument. -/
theorem kaplanskyReciprocal_difference (A D : B)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint D) :
    A * kaplanskyReciprocal A - D * kaplanskyReciprocal D =
      kaplanskyReciprocal A *
        ((A - D) - A * (A - D) * D) * kaplanskyReciprocal D := by
  let G := kaplanskyReciprocal A
  let F := kaplanskyReciprocal D
  have hG : G * (1 + A ^ 2) = 1 := kaplanskyReciprocal_right_inverse A hA
  have hF : (1 + D ^ 2) * F = 1 := kaplanskyReciprocal_left_inverse D hB
  have hGA : G * A = A * G := (kaplanskyReciprocal_commute A).eq
  change A * G - D * F = G * ((A - D) - A * (A - D) * D) * F
  calc
    A * G - D * F = (G * A) * ((1 + D ^ 2) * F) -
        (G * (1 + A ^ 2)) * (D * F) := by rw [hF, hG, mul_one, one_mul, hGA]
    _ = G * ((A - D) - A * (A - D) * D) * F := by noncomm_ring

/-- The scalar transform used in bounded approximation. -/
def kaplanskyFunction (t : ℝ) : ℝ := 2 * (t * (1 + t ^ 2)⁻¹)

private theorem kaplanskyFunction_continuous : Continuous kaplanskyFunction := by
  exact continuous_const.mul (continuous_id.mul reciprocal_continuous)

theorem kaplanskyTransform_eq_cfc (A : B) (hA : IsSelfAdjoint A) :
    kaplanskyTransform A = cfc kaplanskyFunction A := by
  change kaplanskyTransform A = cfc (fun t : ℝ => 2 * (t * (1 + t ^ 2)⁻¹)) A
  rw [cfc_const_mul (2 : ℝ) (fun t : ℝ => t * (1 + t ^ 2)⁻¹) A
    (continuous_id.mul reciprocal_continuous).continuousOn,
    cfc_mul (fun t : ℝ => t) (fun t : ℝ => (1 + t ^ 2)⁻¹) A
      continuousOn_id reciprocal_continuous.continuousOn,
    cfc_id' ℝ A hA]
  rfl

private def kaplanskyInverseFunction (t : ℝ) : ℝ :=
  t / (1 + Real.sqrt (1 - t ^ 2))

private theorem kaplanskyInverseFunction_continuous :
    Continuous kaplanskyInverseFunction := by
  apply Continuous.div continuous_id
  · fun_prop
  · intro t
    positivity

private theorem kaplanskyFunction_inverse (t : ℝ) (ht : |t| ≤ 1) :
    kaplanskyFunction (kaplanskyInverseFunction t) = t := by
  have hts := abs_le.mp ht
  have hs : 0 ≤ 1 - t ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 - t) (by linarith : 0 ≤ 1 + t)]
  have he := Real.sq_sqrt hs
  have hp : 0 < 1 + Real.sqrt (1 - t ^ 2) := by positivity
  have hq : 0 < 1 + (t / (1 + Real.sqrt (1 - t ^ 2))) ^ 2 := by positivity
  unfold kaplanskyFunction kaplanskyInverseFunction
  field_simp
  nlinarith

/-- The bounded inverse branch, defined by functional calculus. -/
def kaplanskyPreimage (T : B) : B := cfc kaplanskyInverseFunction T

theorem kaplanskyPreimage_selfAdjoint (T : B) : IsSelfAdjoint (kaplanskyPreimage T) :=
  cfc_predicate _ T

theorem kaplanskyPreimage_mem (S : StarSubalgebra ℂ B) (hS : IsClosed (S : Set B))
    (T : B) (hT : T ∈ S) : kaplanskyPreimage T ∈ S := by
  let := hS
  exact cfc_mem (𝕜' := ℂ) (s := S) kaplanskyInverseFunction hT

/-- Every selfadjoint contraction is a bounded transform of a selfadjoint
member of its own generated C-star algebra. -/
theorem kaplanskyTransform_preimage (T : B) (hT : IsSelfAdjoint T)
    (hn : ‖T‖ ≤ 1) : kaplanskyTransform (kaplanskyPreimage T) = T := by
  let D := kaplanskyPreimage T
  have hD : IsSelfAdjoint D := kaplanskyPreimage_selfAdjoint T
  change kaplanskyTransform D = T
  rw [kaplanskyTransform_eq_cfc D hD]
  change cfc kaplanskyFunction (cfc kaplanskyInverseFunction T) = T
  rw [← cfc_comp _ _ T hT kaplanskyFunction_continuous.continuousOn
    kaplanskyInverseFunction_continuous.continuousOn]
  calc
    cfc (kaplanskyFunction ∘ kaplanskyInverseFunction) T = cfc id T := by
      apply cfc_congr
      intro t ht
      apply kaplanskyFunction_inverse
      by_cases hnt : Nontrivial B
      · let : Nontrivial B := hnt
        exact (show |t| ≤ ‖T‖ from spectrum.norm_le_norm_of_mem ht).trans hn
      · let : Subsingleton B := not_nontrivial_iff_subsingleton.mp hnt
        have he : spectrum ℝ T = ∅ := spectrum.of_subsingleton T
        exact False.elim ((Set.notMem_empty t) (he ▸ ht))
    _ = T := cfc_id' ℝ T hT

theorem map_kaplanskyTransform {C : Type*} [CStarAlgebra C]
    (σ : B →⋆ₐ[ℂ] C) (A : B) (hA : IsSelfAdjoint A) :
    σ (kaplanskyTransform A) = kaplanskyTransform (σ A) := by
  rw [kaplanskyTransform_eq_cfc A hA,
    σ.map_cfc kaplanskyFunction A kaplanskyFunction_continuous.continuousOn,
    kaplanskyTransform_eq_cfc (σ A) (hA.map σ)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kaplanskyReciprocal_difference_apply_le (A B : H →L[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (x : H) :
    ‖(A * kaplanskyReciprocal A - B * kaplanskyReciprocal B) x‖ ≤
      ‖(A - B) (kaplanskyReciprocal B x)‖ +
        (1 / 2) * ‖(A - B) (B (kaplanskyReciprocal B x))‖ := by
  rw [kaplanskyReciprocal_difference A B hA hB]
  have he : (kaplanskyReciprocal A *
      ((A - B) - A * (A - B) * B) * kaplanskyReciprocal B) x =
      kaplanskyReciprocal A ((A - B) (kaplanskyReciprocal B x)) -
        (kaplanskyReciprocal A * A) ((A - B) (B (kaplanskyReciprocal B x))) := by
    simp only [mul_apply_eq_comp, sub_apply, map_sub]
  rw [he]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · exact (le_opNorm _ _).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (kaplanskyReciprocal_norm_le A) (norm_nonneg _))
  · exact (le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (by simpa only [(kaplanskyReciprocal_commute A).eq] using
        kaplanskyReciprocal_mul_norm_le A hA) (norm_nonneg _))

end KadisonSimilarity

end

end OAI
