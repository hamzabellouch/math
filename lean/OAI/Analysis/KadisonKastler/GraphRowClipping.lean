import OAI.Analysis.KadisonKastler.GraphRowSelection
import OAI.Analysis.KadisonKastler.HilbertRows
import OAI.Analysis.KadisonKastler.RandomizedRMS

namespace OAI

/-! # A common spectral cutoff for a replicated graph row

The cutoff acts on the left square of the entire row. Its norm is bounded
independently of the number of columns, while its normalized graph error
is controlled by the two fourth-moment sums in `graphRowCost`.
-/

namespace KadisonKastler

open scoped BigOperators CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable {I : Type*} [Fintype I]

local instance graphRowClipOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance graphRowClipStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

theorem graphRowSquare_nonneg (Y : I → H →L[ℂ] H) : 0 ≤ graphRowSquare Y := by
  apply Finset.sum_nonneg
  intro i _
  simpa only [star_star] using star_mul_self_nonneg (star (Y i))

/-- The common positive left multiplier used to clip the entire row. -/
def graphRowClipFactor (β : ℝ) (Y : I → H →L[ℂ] H) : H →L[ℂ] H :=
  cfc (clippingFunction β) (CFC.sqrt (graphRowSquare Y))

/-- Spectral clipping of a rectangular row on its left square. -/
def clippedGraphRow (β : ℝ) (Y : I → H →L[ℂ] H) (i : I) : H →L[ℂ] H :=
  graphRowClipFactor β Y * Y i

private theorem graphRowClipFactor_selfadjoint (β : ℝ) (Y : I → H →L[ℂ] H) :
    IsSelfAdjoint (graphRowClipFactor β Y) :=
  cfc_predicate (clippingFunction β) (CFC.sqrt (graphRowSquare Y))

private theorem rowSquare_clip (β : ℝ) (Y : I → H →L[ℂ] H) :
    graphRowSquare (clippedGraphRow β Y) =
      graphRowClipFactor β Y * graphRowSquare Y * graphRowClipFactor β Y := by
  simp only [graphRowSquare, clippedGraphRow, star_mul,
    (graphRowClipFactor_selfadjoint β Y).star_eq, Finset.mul_sum, Finset.sum_mul, mul_assoc]

private theorem norm_operatorRow_sq (Y : I → H →L[ℂ] H) :
    ‖operatorRow Y‖ ^ 2 = ‖graphRowSquare Y‖ := by
  rw [← norm_rectangular_mul_star]
  have he : operatorRow Y * (operatorRow Y).conjTranspose =
      diagonalStarAlgHom Unit (fun _ => graphRowSquare Y) := by
    ext i j
    simp only [CStarMatrix.mul_apply, CStarMatrix.conjTranspose_apply,
      operatorRow_apply, diagonalStarAlgHom_apply]
    simp [graphRowSquare]
  rw [he, norm_diagonalStarAlgHom]
  simp

/-- The whole clipped row has norm at most the cutoff. -/
theorem norm_clippedGraphRow_le {β : ℝ} (hβ : 0 < β) (Y : I → H →L[ℂ] H) :
    ‖operatorRow (clippedGraphRow β Y)‖ ≤ β := by
  let S := CFC.sqrt (graphRowSquare Y)
  have hS : 0 ≤ S := CFC.sqrt_nonneg _
  have hSS : S * S = graphRowSquare Y := CFC.sqrt_mul_sqrt_self _ (graphRowSquare_nonneg Y)
  have he : graphRowSquare (clippedGraphRow β Y) =
      star (spectralClip β S) * spectralClip β S := by
    rw [rowSquare_clip]
    simp only [spectralClip, CFC.abs_of_nonneg S hS, star_mul, hS.isSelfAdjoint.star_eq]
    change graphRowClipFactor β Y * graphRowSquare Y * graphRowClipFactor β Y =
      star (graphRowClipFactor β Y) * S * (S * graphRowClipFactor β Y)
    rw [(graphRowClipFactor_selfadjoint β Y).star_eq]
    rw [← hSS]
    simp only [mul_assoc]
  have hb := spectralClip_norm_le hβ S
  have hn := norm_operatorRow_sq (clippedGraphRow β Y)
  rw [he, CStarRing.norm_star_mul_self] at hn
  nlinarith [norm_nonneg (operatorRow (clippedGraphRow β Y)), norm_nonneg (spectralClip β S)]

private theorem clipping_remainder_sq_le {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t) :
    (1 - clippingFunction β t) ^ 2 ≤ t ^ 2 / β ^ 2 := by
  have hf0 := clippingFunction_nonneg hβ t
  have hf1 := clippingFunction_le_one hβ t
  have hle : 1 - clippingFunction β t ≤ t / β := by
    by_cases h : t ≤ β
    · simp only [clippingFunction, max_eq_left h, div_self (ne_of_gt hβ), sub_self]
      exact div_nonneg ht hβ.le
    · have hb : β ≤ t := (lt_of_not_ge h).le
      have hr : 1 ≤ t / β := (le_div_iff₀ hβ).mpr (by simpa using hb)
      linarith
  have hsq := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - clippingFunction β t) hle 2
  simpa only [div_pow] using hsq

private theorem rowClip_remainder_sq_le {β : ℝ} (hβ : 0 < β)
    (Y : I → H →L[ℂ] H) :
    (1 - graphRowClipFactor β Y) ^ 2 ≤ (β ^ 2)⁻¹ • graphRowSquare Y := by
  let S := CFC.sqrt (graphRowSquare Y)
  have hS : 0 ≤ S := CFC.sqrt_nonneg _
  have hq : 1 - graphRowClipFactor β Y = cfc (fun t => 1 - clippingFunction β t) S := by
    rw [cfc_sub _ _ S (by fun_prop) (clippingFunction_continuous hβ).continuousOn,
      cfc_const_one ℝ S hS.isSelfAdjoint]
    rfl
  have hSS : S ^ 2 = graphRowSquare Y := by
    rw [pow_two]
    exact CFC.sqrt_mul_sqrt_self _ (graphRowSquare_nonneg Y)
  have hr : (β ^ 2)⁻¹ • graphRowSquare Y = cfc (fun t : ℝ => t ^ 2 / β ^ 2) S := by
    simp_rw [div_eq_mul_inv, mul_comm (_ ^ 2)]
    rw [cfc_const_mul _ _ S (by fun_prop), cfc_pow_id (R := ℝ) S 2 hS.isSelfAdjoint,
      hSS]
  have hcont : Continuous (fun t : ℝ => 1 - clippingFunction β t) :=
    continuous_const.sub (clippingFunction_continuous hβ)
  rw [hq, ← cfc_pow _ 2 _ hcont.continuousOn, hr]
  apply (cfc_le_iff _ _ _ (hcont.pow 2).continuousOn (by fun_prop)).mpr
  intro t ht
  exact clipping_remainder_sq_le hβ (spectrum_nonneg_of_nonneg hS ht)

private theorem rowClip_remainder_sandwich_le {β : ℝ} (hβ : 0 < β)
    (Y : I → H →L[ℂ] H) :
    (1 - graphRowClipFactor β Y) * graphRowSquare Y * (1 - graphRowClipFactor β Y) ≤
      (β ^ 2)⁻¹ • (graphRowSquare Y) ^ 2 := by
  let S := CFC.sqrt (graphRowSquare Y)
  have hS : 0 ≤ S := CFC.sqrt_nonneg _
  have he : S - spectralClip β S = S * (1 - graphRowClipFactor β Y) := by
    simp only [spectralClip, CFC.abs_of_nonneg S hS, mul_sub, mul_one]
    rfl
  have h := spectralClip_discard_fourth_bound hβ S
  rw [he, star_mul, star_sub, star_one, (graphRowClipFactor_selfadjoint β Y).star_eq,
    hS.isSelfAdjoint.star_eq] at h
  have hSS : S * S = graphRowSquare Y := CFC.sqrt_mul_sqrt_self _ (graphRowSquare_nonneg Y)
  simpa only [mul_assoc, ← hSS] using h

/-- The squared normalized rescaled-graph error of the single row cutoff
is at most its moment cost divided by the cutoff squared. -/
theorem clippedGraphRow_graph_error_le {k : ℕ} (hk : 0 < k)
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) {β : ℝ} (hβ : 0 < β)
    (Y : Fin k → H →L[ℂ] H) :
    (𝔼 i, ‖rescaledGraphVector J Ω (Real.sqrt (k : ℝ))
      (Y i - clippedGraphRow β Y i)‖ ^ 2) ≤ graphRowCost Ω Y / β ^ 2 := by
  let Q := 1 - graphRowClipFactor β Y
  have hQ : IsSelfAdjoint Q :=
    (IsSelfAdjoint.one (H →L[ℂ] H)).sub (graphRowClipFactor_selfadjoint β Y)
  have hdiff (i : Fin k) : Y i - clippedGraphRow β Y i = Q * Y i := by
    simp only [Q, clippedGraphRow, sub_mul, one_mul]
  have hright (i : Fin k) :
      ‖(Q * Y i) Ω‖ ^ 2 ≤ (β ^ 2)⁻¹ *
        realVectorState Ω (star (Y i) * graphRowSquare Y * Y i) := by
    have h := star_left_conjugate_le_conjugate (rowClip_remainder_sq_le hβ Y) (Y i)
    have hφ := realVectorState_mono Ω h
    have he : star (Y i) * (1 - graphRowClipFactor β Y) ^ 2 * Y i =
        star (Q * Y i) * (Q * Y i) := by
      change star (Y i) * Q ^ 2 * Y i = _
      simp only [pow_two, star_mul, hQ.star_eq, mul_assoc]
    rw [he, realVectorState_star_mul_self] at hφ
    simpa only [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul] using hφ
  have hleft : (∑ i, ‖star (Q * Y i) Ω‖ ^ 2) ≤
      (β ^ 2)⁻¹ * realVectorState Ω ((graphRowSquare Y) ^ 2) := by
    have h := realVectorState_mono Ω (rowClip_remainder_sandwich_le hβ Y)
    have he : (∑ i, ‖star (Q * Y i) Ω‖ ^ 2) =
        realVectorState Ω (Q * graphRowSquare Y * Q) := by
      simp only [graphRowSquare, Finset.mul_sum, Finset.sum_mul, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hp : Q * (Y i * star (Y i)) * Q = star (star (Q * Y i)) * star (Q * Y i) := by
        simp only [star_mul, star_star, hQ.star_eq, mul_assoc]
      rw [hp, realVectorState_star_mul_self]
    rw [he]
    simpa only [map_smul, smul_eq_mul] using h
  simp_rw [hdiff, norm_rescaledGraphVector_sq, Real.sq_sqrt (Nat.cast_nonneg k)]
  rw [Fintype.expect_eq_sum_div_card, Finset.sum_add_distrib, ← Finset.mul_sum,
    Fintype.card_fin]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hright i)
  rw [← Finset.mul_sum] at hs
  unfold graphRowCost
  simp only [Fintype.card_fin]
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hb := add_le_add hs (mul_le_mul_of_nonneg_left hleft hkR.le)
  have hd := div_le_div_of_nonneg_right hb hkR.le
  convert hd using 1
  field_simp
  ring

end

end KadisonKastler

end OAI
