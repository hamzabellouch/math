import OAI.Analysis.Nuclearity.CPNormFromPositive

namespace OAI

/-! A contractive two-copy map supported on one positive contraction. The
support is enough; the initial relative isometries need not be central. -/

noncomputable section
open scoped BigOperators CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {B D : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra D]
  [PartialOrder B] [StarOrderedRing B] [PartialOrder D] [StarOrderedRing D]

def twoInnerMap (β : B →⋆ₙₐ[ℂ] D) (v : Fin 2 → D) : B →L[ℂ] D :=
  innerHomCompression β (v 0) + innerHomCompression β (v 1)

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder D] [StarOrderedRing D] in
lemma twoInnerMap_apply (β : B →⋆ₙₐ[ℂ] D) (v : Fin 2 → D) (b : B) :
    twoInnerMap β v b = star (v 0) * β b * v 0 + star (v 1) * β b * v 1 := rfl

lemma twoInnerMap_cp (β : B →⋆ₙₐ[ℂ] D) (v : Fin 2 → D) :
    CompletelyPositive (twoInnerMap β v) := by
  intro n M hM
  exact add_nonneg (innerHomCompression_cp β (v 0) n M hM)
    (innerHomCompression_cp β (v 1) n M hM)

lemma twoInnerMap_norm_le_one (β : B →⋆ₙₐ[ℂ] D) (v : Fin 2 → D)
    (hv : ∀ i, ‖v i‖ ≤ 1) (horth : v 0 * star (v 1) = 0) :
    ‖twoInnerMap β v‖ ≤ 1 := by
  let Q := star (v 0) * v 0 + star (v 1) * v 1
  have hQQ : (star (v 0) * v 0) * (star (v 1) * v 1) = 0 := by
    calc
      _ = star (v 0) * (v 0 * star (v 1)) * v 1 := by noncomm_ring
      _ = 0 := by rw [horth, mul_zero, zero_mul]
  have hQ : ‖Q‖ ≤ 1 := by
    rw [show Q = star (v 0) * v 0 + star (v 1) * v 1 from rfl,
      (IsSelfAdjoint.star_mul_self (v 0)).norm_add_eq_max
        (IsSelfAdjoint.star_mul_self (v 1)) hQQ]
    apply max_le
    · rw [CStarRing.norm_star_mul_self]
      nlinarith [hv 0, norm_nonneg (v 0)]
    · rw [CStarRing.norm_star_mul_self]
      nlinarith [hv 1, norm_nonneg (v 1)]
  apply cp_norm_le_one_of_positive_bound_nonunital _ (twoInnerMap_cp β v)
  intro b hb
  have hle : twoInnerMap β v b ≤ ‖β b‖ • Q := by
    have h := add_le_add
      (CStarAlgebra.star_left_conjugate_le_norm_smul (v 0) (β b) (hb.isSelfAdjoint.map β))
      (CStarAlgebra.star_left_conjugate_le_norm_smul (v 1) (β b) (hb.isSelfAdjoint.map β))
    simpa only [twoInnerMap_apply, Q, smul_add] using h
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hle
    (map_nonneg (twoInnerMap_cp β v).toMap hb)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hn
  exact hn.trans ((mul_le_mul_of_nonneg_left hQ (norm_nonneg _)).trans
    (by simpa only [mul_one] using NonUnitalStarAlgHom.norm_apply_le β b))

def supportedTwoCopyMap (β : B →⋆ₙₐ[ℂ] D) (e : B) (r : Fin 2 → D) : B →L[ℂ] D :=
  twoInnerMap β (fun i => β e * star (r i))

lemma supportedTwoCopyMap_norm_le_one (β : B →⋆ₙₐ[ℂ] D)
    (e : B) (he : 0 ≤ e) (hen : ‖e‖ ≤ 1) (r : Fin 2 → D)
    (hr : ∀ i, ‖r i‖ ≤ 1)
    (hrel : ∀ i j, (star (r i) * r j) * β e = if i = j then β e else 0) :
    ‖supportedTwoCopyMap β e r‖ ≤ 1 := by
  apply twoInnerMap_norm_le_one
  · intro i
    exact (norm_mul_le _ _).trans (by
      rw [norm_star]
      exact (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le β e) (hr i)
        (norm_nonneg _) (norm_nonneg e)).trans (by nlinarith [norm_nonneg e]))
  · simp only [star_mul, star_star, ← map_star, he.isSelfAdjoint.star_eq]
    have h := hrel 0 1
    simp only [show (0 : Fin 2) ≠ 1 by decide, ite_false] at h
    calc
      _ = β e * ((star (r 0) * r 1) * β e) := by noncomm_ring
      _ = 0 := by rw [h, mul_zero]

omit [PartialOrder B] [StarOrderedRing B] [PartialOrder D] [StarOrderedRing D] in
lemma supportedTwoCopyMap_corner (β : B →⋆ₙₐ[ℂ] D)
    (e : B) (he : IsSelfAdjoint e) (r : Fin 2 → D)
    (hrel : ∀ i j, (star (r i) * r j) * β e = if i = j then β e else 0)
    (b : B) (i j : Fin 2) :
    star (r i) * supportedTwoCopyMap β e r b * r j =
      if i = j then β (e * b * e) else 0 := by
  have hright (k j : Fin 2) : β e * (star (r k) * r j) =
      if j = k then β e else 0 := by
    have h := congrArg star (hrel j k)
    simpa only [star_mul, star_star, ← map_star, he.star_eq, apply_ite, star_zero] using h
  have hterm (k : Fin 2) :
      star (r i) * innerHomCompression β (β e * star (r k)) b * r j =
        (if i = k then β e else 0) * β b * (if j = k then β e else 0) := by
    rw [innerHomCompression_apply, star_mul, star_star, ← map_star, he.star_eq]
    calc
      _ = ((star (r i) * r k) * β e) * β b * (β e * (star (r k) * r j)) := by noncomm_ring
      _ = _ := by rw [hrel, hright]
  change star (r i) * (innerHomCompression β (β e * star (r 0)) b +
    innerHomCompression β (β e * star (r 1)) b) * r j = _
  rw [mul_add, add_mul, hterm, hterm]
  fin_cases i <;> fin_cases j <;> simp [map_mul]

end WeakPureInfiniteness

end

end OAI
