import OAI.InformationTheory.AmplitudeDamping.MatrixDifferentiation

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Trace commutes with differentiation of finite-dimensional matrix curves. -/
theorem hasDerivAt_trace {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) :
    HasDerivAt (fun s ↦ (A s).trace) H.trace t := by
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ ↦
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hA i) i) using 1
  ext s
  simp [Matrix.trace]

/-- The first derivative term in Jacobi's formula has the expected noncommutative derivative. -/
theorem hasDerivAt_trace_inv_mul {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s ↦ (Matrix.trace ((A s)⁻¹ * H)).re)
      (-(Matrix.trace (((A t)⁻¹ * H) * ((A t)⁻¹ * H))).re) t := by
  have hi := hasDerivAt_matrix_inv hA hdet
  have ht := hasDerivAt_trace (hasDerivAt_matrix_mul hi (hasDerivAt_const t H))
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ht
  convert! hr using 1
  simp [Matrix.mul_assoc]

/-- The skew-shift log-determinant deficit, including non-real determinants. -/
def skewLogDet (Z D : Matrix ι ι ℂ) : ℝ :=
  Real.log ‖(D + Z).det‖ - Real.log ‖D.det‖

omit [Fintype ι] [DecidableEq ι] in
/-- Positivity is preserved throughout a segment, including both endpoints. -/
theorem posDef_segment {D E : Matrix ι ι ℂ} (hD : D.PosDef) (hE : E.PosDef)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a • D + b • E).PosDef := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · have : b = 1 := by linarith
    simpa [this] using hE
  · exact (hD.smul ha).add_posSemidef (hE.posSemidef.smul hb)

/-- Joint convexity mechanism: a fixed skew-Hermitian perturbation has convex logdet deficit. -/
theorem convexOn_skewLogDet (Z : Matrix ι ι ℂ) (hZ : Z.conjTranspose = -Z) :
    ConvexOn ℝ {D : Matrix ι ι ℂ | D.PosDef} (skewLogDet Z) := by
  refine ⟨?_, ?_⟩
  · intro D hD E hE a b ha hb hab
    exact posDef_segment hD hE ha hb hab
  intro D hD E hE a b ha hb hab
  let A : ℝ → Matrix ι ι ℂ := fun t ↦ (1 - t) • D + t • E
  let H := E - D
  have hH : H.IsHermitian := hE.isHermitian.sub hD.isHermitian
  have hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (A t).PosDef :=
    posDef_segment hD hE (sub_nonneg.2 ht.2) ht.1 (by ring)
  have hA (t : ℝ) : HasDerivAt A H t := by
    convert! (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).smul_const D).add
      ((hasDerivAt_id t).smul_const E) using 1
    simp [H, sub_eq_add_neg, add_comm]
  let f : ℝ → ℝ := fun t ↦ skewLogDet Z (A t)
  let f' : ℝ → ℝ := fun t ↦
    (Matrix.trace ((A t + Z)⁻¹ * H)).re - (Matrix.trace ((A t)⁻¹ * H)).re
  let f'' : ℝ → ℝ := fun t ↦
    (Matrix.trace (((A t)⁻¹ * H) * ((A t)⁻¹ * H))).re -
      (Matrix.trace (((A t + Z)⁻¹ * H) * ((A t + Z)⁻¹ * H))).re
  have hunit (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    skew_shift_trace_bound (A t) Z H (hpos t ht) hZ hH
  have hnD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (A t).det ≠ 0 :=
    isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 (hpos t ht).isUnit)
  have hnC (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (A t + Z).det ≠ 0 :=
    isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 (hunit t ht).1)
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f (f' t) t := by
    have hd := hasDerivAt_logNormDet (hA t) (hnD t ht)
    have hc := hasDerivAt_logNormDet ((hA t).add_const Z) (hnC t ht)
    convert! hc.sub hd using 1
    simp [f', Matrix.trace_mul_comm H]
  have hf' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f' (f'' t) t := by
    have hd := hasDerivAt_trace_inv_mul (hA t) (hnD t ht)
    have hc := hasDerivAt_trace_inv_mul ((hA t).add_const Z) (hnC t ht)
    convert! hc.sub hd using 1
    dsimp [f'']
    ring
  have hf'' (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 ≤ f'' t :=
    sub_nonneg.2 (hunit t ht).2
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) f :=
    convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc _ _)
      (fun t ht ↦ (hf t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hf t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ (hf' t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht ↦ hf'' t (interior_subset ht))
  have h := hconv.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ha hb hab
  have hea : 1 - b = a := by linarith
  simpa [f, A, hea] using h

end GAD

open scoped ComplexOrder MatrixOrder
open Matrix Set
namespace GAD
variable {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- A direct sum of strictly positive matrices is strictly positive. -/
theorem posDef_fromBlocks_zero {D : Matrix ι ι ℂ} {E : Matrix κ κ ℂ}
    (hD : D.PosDef) (hE : E.PosDef) :
    (Matrix.fromBlocks D 0 0 E).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.IsHermitian.fromBlocks hD.isHermitian (by simp) hE.isHermitian)
  intro x hx
  have hxsplit : x = Sum.elim (fun i ↦ x (.inl i)) (fun j ↦ x (.inr j)) := by
    ext i
    cases i <;> rfl
  rw [hxsplit, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add, Function.star_sumElim, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim]
  have hnon : (fun i ↦ x (.inl i)) ≠ 0 ∨ (fun j ↦ x (.inr j)) ≠ 0 := by
    by_contra h
    simp only [not_or, ne_eq, not_not] at h
    apply hx
    rw [hxsplit, h.1, h.2]
    ext i
    cases i <;> rfl
  rcases hnon with h | h
  · exact add_pos_of_pos_of_nonneg (hD.dotProduct_mulVec_pos h)
      (hE.posSemidef.dotProduct_mulVec_nonneg _)
  · exact add_pos_of_nonneg_of_pos (hD.posSemidef.dotProduct_mulVec_nonneg _)
      (hE.dotProduct_mulVec_pos h)


def blockLogDet (Z : Matrix ι κ ℂ) (D : Matrix ι ι ℂ) (E : Matrix κ κ ℂ) : ℝ :=
  Real.log ‖(D + Z * E⁻¹ * Zᴴ).det‖ - Real.log ‖D.det‖

theorem skewLogDet_fromBlocks (Z : Matrix ι κ ℂ)
    {D : Matrix ι ι ℂ} {E : Matrix κ κ ℂ} (hD : D.PosDef) (hE : E.PosDef) :
    skewLogDet (Matrix.fromBlocks 0 Z (-Zᴴ) 0) (Matrix.fromBlocks D 0 0 E) =
      blockLogDet Z D E := by
  have hS : (D + Z * E⁻¹ * Zᴴ).PosDef :=
    hD.add_posSemidef (hE.inv.posSemidef.mul_mul_conjTranspose_same Z)
  have hnD : ‖D.det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hD.isUnit))
  have hnE : ‖E.det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hE.isUnit))
  have hnS : ‖(D + Z * E⁻¹ * Zᴴ).det‖ ≠ 0 := norm_ne_zero_iff.mpr
    (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hS.isUnit))
  let := hE.isUnit.invertible
  simp only [skewLogDet, blockLogDet, Matrix.fromBlocks_add, add_zero, zero_add]
  rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv,
    Matrix.mul_neg, sub_neg_eq_add, Matrix.det_fromBlocks_zero₁₂, norm_mul, norm_mul,
    Real.log_mul hnE hnS, Real.log_mul hnD hnE]
  ring

/-- Main log-determinant lemma, in all finite rectangular block dimensions. -/
theorem convexOn_blockLogDet (Z : Matrix ι κ ℂ) :
    ConvexOn ℝ {p : Matrix ι ι ℂ × Matrix κ κ ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p ↦ blockLogDet Z p.1 p.2) := by
  have hc := convexOn_skewLogDet (Matrix.fromBlocks 0 Z (-Zᴴ) 0) (by
    simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg])
  refine ⟨?_, ?_⟩
  · intro D hD E hE a b ha hb hab
    exact ⟨posDef_segment hD.1 hE.1 ha hb hab, posDef_segment hD.2 hE.2 ha hb hab⟩
  intro D hD E hE a b ha hb hab
  have h := hc.2 (posDef_fromBlocks_zero hD.1 hD.2)
    (posDef_fromBlocks_zero hE.1 hE.2) ha hb hab
  change blockLogDet Z (a • D.1 + b • E.1) (a • D.2 + b • E.2) ≤ _
  simpa only [Matrix.fromBlocks_smul, Matrix.fromBlocks_add, smul_zero, add_zero,
    skewLogDet_fromBlocks Z hD.1 hD.2, skewLogDet_fromBlocks Z hE.1 hE.2,
    skewLogDet_fromBlocks Z (posDef_segment hD.1 hE.1 ha hb hab)
      (posDef_segment hD.2 hE.2 ha hb hab), Prod.fst_add, Prod.snd_add,
    Prod.fst_smul, Prod.snd_smul] using h
end GAD

end

end OAI
