import OAI.Analysis.PureInfiniteness.OneStepContraction
import OAI.Analysis.WeakInfiniteness.ElementaryCP
import OAI.Analysis.WeakInfiniteness.MatrixTensorExact

namespace OAI

/-!
The particular approximately inner map to which KR02 Theorem 7.21 is applied
in the absorption argument: copy the upper-left corner into both diagonal
corners. Its approximately inner character is proved here by two explicit
coefficients and a nonunital approximate unit.
-/

noncomputable section
open Filter Topology
open scoped CStarAlgebra

namespace WeakPureInfiniteness

variable {A : Type*} [NonUnitalCStarAlgebra A]
local instance doubledCornerOrder : PartialOrder A := CStarAlgebra.spectralOrder A
local instance doubledCornerOrdered : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A

/-- A point-norm limit of completely positive maps is completely positive. -/
lemma completelyPositive_of_pointwise_limit
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {B C : Type*} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]
    [PartialOrder B] [StarOrderedRing B] [PartialOrder C] [StarOrderedRing C]
    (S : ι → B →L[ℂ] C) (T : B →L[ℂ] C)
    (hS : ∀ i, CompletelyPositive (S i))
    (hlim : ∀ b, Tendsto (fun i => S i b) l (𝓝 (T b))) :
    CompletelyPositive T := by
  intro n M hM
  have hmatrix : Tendsto (fun i => matrixLinearMap (S i) M) l
      (𝓝 (matrixLinearMap T M)) := by
    change Tendsto (fun i => fun j k => S i (M j k)) l
      (𝓝 (fun j k => T (M j k)))
    exact tendsto_pi_nhds.mpr fun j => tendsto_pi_nhds.mpr fun k => hlim (M j k)
  exact ge_of_tendsto hmatrix (Filter.Eventually.of_forall fun i => hS i n M hM)

/-- Approximation by finite sums of inner compressions (KR02 Definition 7.1). -/
def ApproximatelyInner {B : Type*} [NonUnitalCStarAlgebra B] (T : B → B) : Prop :=
  ∀ (F : Finset B) (ε : ℝ), 0 < ε →
    ∃ n : ℕ, ∃ v : Fin n → B, ∀ b ∈ F, ‖T b - finiteCompression v b‖ < ε

/-- Matrix-unit coefficient with its only nonzero entry in the top row. -/
def cornerCoefficient (f : A) (j : Fin 2) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (fun k l => if k = 0 ∧ l = j then f else 0)

lemma cornerCoefficient_apply (f : A) (j k l : Fin 2) :
    cornerCoefficient f j k l = if k = 0 ∧ l = j then f else 0 := rfl

lemma cornerCoefficient_compression (f : A)
    (X : CStarMatrix (Fin 2) (Fin 2) A) :
    finiteCompression (cornerCoefficient f) X = diagonalCopies 2 (star f * X 0 0 * f) := by
  ext k l
  change (∑ j : Fin 2, star (cornerCoefficient f j) * X * cornerCoefficient f j) k l = _
  simp only [Fin.sum_univ_two, CStarMatrix.add_apply, CStarMatrix.mul_apply,
    CStarMatrix.star_apply, cornerCoefficient_apply,
    Fin.sum_univ_two, diagonalCopies]
  fin_cases k <;> fin_cases l <;> simp

/-- Duplicate the upper-left matrix entry. -/
def doubledCornerLinear : CStarMatrix (Fin 2) (Fin 2) A →ₗ[ℂ]
    CStarMatrix (Fin 2) (Fin 2) A :=
  { toFun := fun X => diagonalCopies 2 (X 0 0)
    map_add' := fun X Y => by
      change diagonalHom 2 (X 0 0 + Y 0 0) = diagonalHom 2 (X 0 0) + diagonalHom 2 (Y 0 0)
      exact map_add (diagonalHom (A := A) 2) _ _
    map_smul' := fun c X => by
      change diagonalHom 2 (c • X 0 0) = c • diagonalHom 2 (X 0 0)
      exact map_smul (diagonalHom (A := A) 2) c _ }

lemma doubledCornerLinear_apply (X : CStarMatrix (Fin 2) (Fin 2) A) :
    doubledCornerLinear X = diagonalCopies 2 (X 0 0) := rfl

lemma doubledCornerLinear_norm_le (X : CStarMatrix (Fin 2) (Fin 2) A) :
    ‖doubledCornerLinear X‖ ≤ ‖X‖ :=
  (NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A) 2) _).trans
    (CStarMatrix.norm_entry_le_norm (M := X) (i := 0) (j := 0))

def doubledCorner : CStarMatrix (Fin 2) (Fin 2) A →L[ℂ]
    CStarMatrix (Fin 2) (Fin 2) A :=
  doubledCornerLinear.mkContinuous 1 (fun X => by
    simpa only [one_mul] using doubledCornerLinear_norm_le X)

lemma doubledCorner_apply (X : CStarMatrix (Fin 2) (Fin 2) A) :
    doubledCorner X = diagonalCopies 2 (X 0 0) := rfl

lemma doubledCorner_norm_le : ‖doubledCorner (A := A)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun X => by
    change ‖doubledCornerLinear X‖ ≤ 1 * ‖X‖
    simpa only [one_mul] using doubledCornerLinear_norm_le X)

lemma cornerCoefficient_tendsto (X : CStarMatrix (Fin 2) (Fin 2) A) :
    Tendsto (fun f => finiteCompressionContinuous (cornerCoefficient f) X)
      (CStarAlgebra.approximateUnit A) (𝓝 (doubledCorner X)) := by
  have hf := CStarAlgebra.increasingApproximateUnit A
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hl := Metric.tendsto_nhds.mp (hf.tendsto_mul_right (X 0 0)) (ε / 2) (by positivity)
  have hr := Metric.tendsto_nhds.mp (hf.tendsto_mul_left (X 0 0)) (ε / 2) (by positivity)
  filter_upwards [hf.eventually_norm, hf.eventually_star_eq, hl, hr] with f hfn hfs hl hr
  rw [dist_eq_norm, finiteCompressionContinuous_apply, cornerCoefficient_compression,
    doubledCorner_apply, hfs]
  have he : diagonalCopies 2 (f * X 0 0 * f) - diagonalCopies 2 (X 0 0) =
      diagonalHom 2 (f * X 0 0 * f - X 0 0) := (map_sub (diagonalHom (A := A) 2) _ _).symm
  rw [he]
  apply (NonUnitalStarAlgHom.norm_apply_le (diagonalHom (A := A) 2) _).trans_lt
  have he' : f * X 0 0 * f - X 0 0 =
      (f * X 0 0 - X 0 0) * f + (X 0 0 * f - X 0 0) := by noncomm_ring
  rw [he']
  simp only [dist_eq_norm] at hl hr
  calc
    _ ≤ ‖(f * X 0 0 - X 0 0) * f‖ + ‖X 0 0 * f - X 0 0‖ := norm_add_le _ _
    _ ≤ ‖f * X 0 0 - X 0 0‖ + ‖X 0 0 * f - X 0 0‖ := by
      apply add_le_add _ le_rfl
      exact (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (f * X 0 0 - X 0 0)])
    _ < ε / 2 + ε / 2 := add_lt_add hl hr
    _ = ε := by ring

lemma doubledCorner_completelyPositive : CompletelyPositive (doubledCorner (A := A)) := by
  let l := CStarAlgebra.approximateUnit A
  let : l.NeBot := (CStarAlgebra.increasingApproximateUnit A).toIsApproximateUnit.neBot
  let S (f : A) : CStarMatrix (Fin 2) (Fin 2) A →L[ℂ]
      CStarMatrix (Fin 2) (Fin 2) A := finiteCompressionContinuous (cornerCoefficient f)
  have hS (f : A) : CompletelyPositive (S f) := finiteCompressionContinuous_cp _
  exact completelyPositive_of_pointwise_limit (l := l) S
    (doubledCorner (A := A)) hS cornerCoefficient_tendsto

/-- The two explicit coefficients approximate the doubled-corner map on any
finite set. This is the approximately-inner input, not its one-step conclusion. -/
lemma doubledCorner_finite_inner_approximation
    (F : Finset (CStarMatrix (Fin 2) (Fin 2) A)) (ε : ℝ) (hε : 0 < ε) :
    ∃ v : Fin 2 → CStarMatrix (Fin 2) (Fin 2) A,
      ∀ X ∈ F, ‖doubledCorner X - finiteCompression v X‖ < ε := by
  let l := CStarAlgebra.approximateUnit A
  let : l.NeBot := (CStarAlgebra.increasingApproximateUnit A).toIsApproximateUnit.neBot
  have hF : ∀ᶠ f in l, ∀ X ∈ F,
      ‖doubledCorner X - finiteCompressionContinuous (cornerCoefficient f) X‖ < ε := by
    apply (Filter.eventually_all_finset F).mpr
    intro X _
    exact (Metric.tendsto_nhds.mp (cornerCoefficient_tendsto X) ε hε).mono fun f hf => by
      simpa only [dist_eq_norm, norm_sub_rev] using hf
  obtain ⟨f, hf⟩ := hF.exists
  exact ⟨cornerCoefficient f, hf⟩

lemma doubledCorner_approximatelyInner : ApproximatelyInner (doubledCorner (A := A)) := by
  intro F ε hε
  obtain ⟨v, hv⟩ := doubledCorner_finite_inner_approximation F ε hε
  exact ⟨2, v, hv⟩

/-- The input corner used for the two relative isometries. -/
def topLeftCorner (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix (fun i j => if i = 0 ∧ j = 0 then a else 0)

lemma topLeftCorner_apply (a : A) (i j : Fin 2) :
    topLeftCorner a i j = if i = 0 ∧ j = 0 then a else 0 := rfl

lemma doubledCorner_topLeftCorner (a : A) :
    doubledCorner (topLeftCorner a) = diagonalCopies 2 a := by
  rw [doubledCorner_apply]
  simp only [topLeftCorner_apply, and_self, ite_true]

lemma topLeftCorner_compression_entry
    (d : CStarMatrix (Fin 2) (Fin 2) A) (a : A) (i j : Fin 2) :
    (star d * topLeftCorner a * d) i j = star (d 0 i) * a * d 0 j := by
  simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, topLeftCorner_apply, Fin.sum_univ_two]
  simp

/-- Extract actual bounded relative Cuntz witnesses from a concrete
one-step matrix approximation. This step uses multiplicative matrix entries. -/
lemma relativePair_of_doubledCorner_witness
    (d : CStarMatrix (Fin 2) (Fin 2) A) (hd : ‖d‖ ≤ 1)
    (F : Finset A) (ε : ℝ)
    (happrox : ∀ a ∈ F,
      ‖doubledCorner (topLeftCorner a) - star d * topLeftCorner a * d‖ < ε) :
    ‖d 0 0‖ ≤ 1 ∧ ‖d 0 1‖ ≤ 1 ∧
      ∀ a ∈ F, ‖star (d 0 0) * a * d 0 0 - a‖ < ε ∧
        ‖star (d 0 1) * a * d 0 1 - a‖ < ε ∧
        ‖star (d 0 0) * a * d 0 1‖ < ε := by
  refine ⟨(CStarMatrix.norm_entry_le_norm (M := d) (i := 0) (j := 0)).trans hd,
    (CStarMatrix.norm_entry_le_norm (M := d) (i := 0) (j := 1)).trans hd, ?_⟩
  intro a ha
  have hentry (i j : Fin 2) := (CStarMatrix.norm_entry_le_norm
    (M := doubledCorner (topLeftCorner a) - star d * topLeftCorner a * d)
    (i := i) (j := j)).trans_lt (happrox a ha)
  have h00 := hentry 0 0
  have h11 := hentry 1 1
  have h01 := hentry 0 1
  simp only [CStarMatrix.sub_apply, doubledCorner_topLeftCorner,
    topLeftCorner_compression_entry, diagonalCopies, CStarMatrix.ofMatrix_apply,
    Matrix.diagonal_apply_eq] at h00 h11
  simp only [CStarMatrix.sub_apply, doubledCorner_topLeftCorner,
    topLeftCorner_compression_entry, diagonalCopies, CStarMatrix.ofMatrix_apply] at h01
  have hdiag01 : (Matrix.diagonal (fun _ : Fin 2 => a)) 0 1 = 0 := by simp
  rw [hdiag01, zero_sub, norm_neg] at h01
  exact ⟨by simpa only [norm_sub_rev] using h00,
    by simpa only [norm_sub_rev] using h11, h01⟩

end WeakPureInfiniteness

end

end OAI
