import OAI.Analysis.PureInfiniteness.CuntzGramMap

namespace OAI

/-! # Matrix-valued Gram return maps for the O∞ tensor approximation

The corner formulation also works in a nonunital tensor completion: the common
initial projection need only act identically on the matrix coefficients.
-/

noncomputable section
open scoped CStarAlgebra ComplexOrder

namespace WeakPureInfiniteness

variable {B E I : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra E]
  [Fintype I] [DecidableEq I]

local instance oInfinityTensorGramLocal1 : PartialOrder B := CStarAlgebra.spectralOrder _
local instance oInfinityTensorGramLocal2 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing _

def supportedCuntzMatrixLinear (r : I → E) (σ : B →⋆ₙₐ[ℂ] E) :
    CStarMatrix I I B →ₗ[ℂ] E where
  toFun M := ∑ i, ∑ j, r i * σ (M i j) * star (r j)
  map_add' M N := by
    simp only [CStarMatrix.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c M := by
    simp only [CStarMatrix.smul_apply, map_smul, mul_smul_comm, smul_mul_assoc,
      Finset.smul_sum, RingHom.id_apply]

omit [Fintype I] in
lemma supportedCuntzMatrix_term_mul (r : I → E) (e : E) (σ : B →⋆ₙₐ[ℂ] E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (he : ∀ b, e * σ b = σ b) (M N : CStarMatrix I I B) (i j k l : I) :
    (r i * σ (M i j) * star (r j)) * (r k * σ (N k l) * star (r l)) =
      if j = k then r i * σ (M i j * N k l) * star (r l) else 0 := by
  calc
    _ = r i * σ (M i j) * (star (r j) * r k) * σ (N k l) * star (r l) := by
      noncomm_ring
    _ = _ := by
      rw [hr]
      split_ifs with h
      · rw [mul_assoc (r i * σ (M i j)) e, he, map_mul]
        simp only [mul_assoc]
      · simp

def supportedCuntzMatrixHom (r : I → E) (e : E) (σ : B →⋆ₙₐ[ℂ] E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (he : ∀ b, e * σ b = σ b) : CStarMatrix I I B →⋆ₙₐ[ℂ] E where
  toFun := supportedCuntzMatrixLinear r σ
  map_zero' := by simp [supportedCuntzMatrixLinear]
  map_add' := map_add _
  map_smul' := map_smul _
  map_mul' M N := by
    change (∑ i, ∑ j, r i * σ ((M * N) i j) * star (r j)) =
      (∑ i, ∑ j, r i * σ (M i j) * star (r j)) *
        (∑ i, ∑ j, r i * σ (N i j) * star (r j))
    simp only [CStarMatrix.mul_apply, map_sum, Finset.mul_sum, Finset.sum_mul]
    simp only [supportedCuntzMatrix_term_mul r e σ hr he, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    calc
      _ = ∑ i, ∑ k, ∑ j, r i * σ (M i k * N k j) * star (r j) := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ k, ∑ i, ∑ j, r i * σ (M i k * N k j) * star (r j) := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        exact Finset.sum_comm
  map_star' M := by
    change (∑ i, ∑ j, r i * σ ((star M) i j) * star (r j)) =
      star (∑ i, ∑ j, r i * σ (M i j) * star (r j))
    simp only [CStarMatrix.star_apply, map_star, star_sum, star_mul, star_star, mul_assoc]
    exact Finset.sum_comm

lemma supportedCuntzMatrixHom_apply (r : I → E) (e : E) (σ : B →⋆ₙₐ[ℂ] E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (he : ∀ b, e * σ b = σ b) (M : CStarMatrix I I B) :
    supportedCuntzMatrixHom r e σ hr he M =
      ∑ i, ∑ j, r i * σ (M i j) * star (r j) := rfl

lemma supportedCuntzMatrixHom_entry (r : I → E) (e : E) (σ : B →⋆ₙₐ[ℂ] E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (he : ∀ b, e * σ b = σ b) (heStar : star e = e)
    (M : CStarMatrix I I B) (i j : I) :
    star (r i) * supportedCuntzMatrixHom r e σ hr he M * r j = σ (M i j) := by
  have he' (b : B) : σ b * e = σ b := by
    simpa only [star_mul, map_star, star_star, heStar] using congrArg star (he (star b))
  have hterm (k l : I) :
      star (r i) * (r k * σ (M k l) * star (r l)) * r j =
        if i = k then (if l = j then σ (M k l) else 0) else 0 := by
    calc
      _ = (star (r i) * r k) * σ (M k l) * (star (r l) * r j) := by noncomm_ring
      _ = _ := by
        rw [hr, hr]
        split_ifs <;> simp [he, he']
  rw [supportedCuntzMatrixHom_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, hterm, Finset.sum_ite_irrel,
    Finset.sum_const_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true]

lemma supportedCuntzMatrixHom_injective (r : I → E) (e : E) (σ : B →⋆ₙₐ[ℂ] E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (he : ∀ b, e * σ b = σ b) (heStar : star e = e)
    (hσ : Function.Injective σ) :
    Function.Injective (supportedCuntzMatrixHom r e σ hr he) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro M hM
  ext i j
  apply hσ
  have h := supportedCuntzMatrixHom_entry r e σ hr he heStar M i j
  rw [hM, mul_zero, zero_mul] at h
  simpa only [CStarMatrix.zero_apply, map_zero] using h.symm

lemma supportedCuntz_rangeProjection (r : I → E) (e : E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (hre : ∀ i, r i * e = r i) : IsStarProjection (∑ i, r i * star (r i)) := by
  apply isStarProjection_iff'.mpr
  constructor
  · have hterm (i j : I) : (r i * star (r i)) * (r j * star (r j)) =
        if i = j then r i * star (r i) else 0 := by
      calc
        _ = r i * (star (r i) * r j) * star (r j) := by noncomm_ring
        _ = _ := by
          rw [hr]
          split_ifs with hij
          · subst j; rw [hre]
          · simp
    simp only [Finset.sum_mul, Finset.mul_sum, hterm, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  · simp only [star_sum, star_mul, star_star]

lemma supportedCuntzMatrixHom_of_entries (r : I → E) (e : E) (σ : B →⋆ₙₐ[ℂ] E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (he : ∀ b, e * σ b = σ b) (x : E) (M : CStarMatrix I I B)
    (hentry : ∀ i j, star (r i) * x * r j = σ (M i j)) :
    supportedCuntzMatrixHom r e σ hr he M =
      (∑ i, r i * star (r i)) * x * (∑ i, r i * star (r i)) := by
  rw [supportedCuntzMatrixHom_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hentry]
  simp only [mul_assoc]

lemma supportedCuntz_compression_norm_le (r : I → E) (e : E) (σ : B →⋆ₙₐ[ℂ] E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (he : ∀ b, e * σ b = σ b) (heStar : star e = e)
    (hre : ∀ i, r i * e = r i) (hσ : Function.Injective σ)
    (x : E) (M : CStarMatrix I I B)
    (hentry : ∀ i j, star (r i) * x * r j = σ (M i j)) : ‖M‖ ≤ ‖x‖ := by
  let P := ∑ i, r i * star (r i)
  have hP : ‖P‖ ≤ 1 := IsStarProjection.norm_le _ (supportedCuntz_rangeProjection r e hr hre)
  have hnorm := NonUnitalStarAlgHom.norm_map (supportedCuntzMatrixHom r e σ hr he)
    (supportedCuntzMatrixHom_injective r e σ hr he heStar hσ) M
  rw [← hnorm, supportedCuntzMatrixHom_of_entries r e σ hr he x M hentry]
  calc
    ‖P * x * P‖ ≤ ‖P‖ * ‖x‖ * ‖P‖ := norm_mul₃_le
    _ ≤ 1 * ‖x‖ * 1 := mul_le_mul (mul_le_mul_of_nonneg_right hP (norm_nonneg _)) hP
      (norm_nonneg _) (by positivity)
    _ = ‖x‖ := by ring

lemma supportedCuntz_gram_apply (r v : I → E) (e : E) (σ : B →⋆ₙₐ[ℂ] E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (he : ∀ b, e * σ b = σ b) (heStar : star e = e)
    (hv : ∀ i, e * v i = v i) (M : CStarMatrix I I B) :
    star (∑ i, r i * v i) * supportedCuntzMatrixHom r e σ hr he M *
      (∑ i, r i * v i) = ∑ i, ∑ j, star (v i) * σ (M i j) * v j := by
  have hv' (i : I) : star (v i) * e = star (v i) := by
    simpa only [star_mul, heStar] using congrArg star (hv i)
  have hl (i : I) : star (∑ j, r j * v j) * r i = star (v i) := by
    simp only [star_sum, Finset.sum_mul, star_mul, mul_assoc, hr]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, hv']
  have hh (j : I) : star (r j) * (∑ i, r i * v i) = v j := by
    simp only [Finset.mul_sum, ← mul_assoc, hr]
    simp [hv]
  rw [supportedCuntzMatrixHom_apply]
  conv_lhs => arg 1; rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => arg 1; rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  calc
    _ = (star (∑ k, r k * v k) * r i) * σ (M i j) *
        (star (r j) * (∑ k, r k * v k)) := by noncomm_ring
    _ = _ := by rw [hl, hh]

lemma supportedCuntz_gram_norm_le (r v : I → E) (e : E) (σ : B →⋆ₙₐ[ℂ] E)
    (hr : ∀ i j, star (r i) * r j = if i = j then e else 0)
    (he : ∀ b, e * σ b = σ b) (hv : ∀ i, e * v i = v i)
    (M : CStarMatrix I I B) :
    ‖star (∑ i, r i * v i) * supportedCuntzMatrixHom r e σ hr he M *
      (∑ i, r i * v i)‖ ≤ ‖∑ i, star (v i) * v i‖ * ‖M‖ := by
  let t := ∑ i, r i * v i
  have ht : star t * t = ∑ i, star (v i) * v i := by
    simp only [t, star_sum, Finset.sum_mul, Finset.mul_sum, star_mul]
    have hh (i j : I) : (star (v i) * star (r i)) * (r j * v j) =
        if i = j then star (v i) * v i else 0 := by
      rw [mul_assoc, ← mul_assoc (star (r i)), hr]
      split_ifs with hij
      · subst j
        rw [hv]
      · simp
    simp only [hh, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  calc
    _ ≤ (‖t‖ * ‖t‖) * ‖supportedCuntzMatrixHom r e σ hr he M‖ := by
      exact norm_mul₃_le.trans_eq (by rw [norm_star]; ring)
    _ = ‖∑ i, star (v i) * v i‖ * ‖supportedCuntzMatrixHom r e σ hr he M‖ := by
      rw [← CStarRing.norm_star_mul_self, ht]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (NonUnitalStarAlgHom.norm_apply_le _ M) (norm_nonneg _)

end WeakPureInfiniteness

end

end OAI
