import OAI.Analysis.KadisonKastler.HaagerupContinuous
import OAI.Analysis.KadisonKastler.RectangularOperator
import OAI.Analysis.KadisonKastler.SquareCompleteBound

namespace OAI

/-! # A completely bounded cochain contraction on the full operator algebra

The rank-one last column realizes the usual Hochschild contraction while
retaining its norm at every matrix level.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance cochainColumnOperatorOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance cochainColumnOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _

def cochainColumn (φ : H →L[ℂ] ℂ) : H →L[ℂ] (H →L[ℂ] H) :=
  ContinuousLinearMap.smulRightL ℂ H H φ

omit [CompleteSpace H] in
@[simp] theorem cochainColumn_apply (φ : H →L[ℂ] ℂ) (x y : H) :
    cochainColumn φ x y = φ y • x := rfl

def cochainColumnEvaluation (φ : H →L[ℂ] ℂ) (ξ : H) :
    ((H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) →L[ℂ] (H →L[ℂ] H) :=
  (ContinuousLinearMap.compL ℂ H (H →L[ℂ] H) H (ContinuousLinearMap.apply ℂ H ξ)).comp
    ((ContinuousLinearMap.compL ℂ H (H →L[ℂ] H) (H →L[ℂ] H)).flip (cochainColumn φ))

@[simp] theorem cochainColumnEvaluation_apply (φ : H →L[ℂ] ℂ) (ξ : H)
    (F : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)) (y : H) :
    cochainColumnEvaluation φ ξ F y = F (cochainColumn φ y) ξ := rfl

def operatorCochainContraction
    {f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) (φ : H →L[ℂ] ℂ) (ξ : H) :
    (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H) :=
  (cochainColumnEvaluation φ ξ).comp (hf.toContinuousBilinear hc)

@[simp] theorem operatorCochainContraction_apply
    {f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) (φ : H →L[ℂ] ℂ) (ξ : H)
    (a : H →L[ℂ] H) (y : H) :
    operatorCochainContraction hf hc φ ξ a y = f a (cochainColumn φ y) ξ := rfl

def cochainColumnMatrix {p q : ℕ} (φ : H →L[ℂ] ℂ)
    (j : Fin q) (y : Generator.FiniteHilbert (Fin p) H) :
    CStarMatrix (Fin p) (Fin q) (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix fun i k => if k = j then cochainColumn φ (y i) else 0

omit [CompleteSpace H] in
@[simp] theorem cochainColumnMatrix_apply {p q : ℕ} (φ : H →L[ℂ] ℂ)
    (j : Fin q) (y : Generator.FiniteHilbert (Fin p) H) (i : Fin p) (k : Fin q) :
    cochainColumnMatrix φ j y i k = if k = j then cochainColumn φ (y i) else 0 := rfl

omit [CompleteSpace H] in
theorem hilbertMatrix_cochainColumnMatrix {p q : ℕ} (φ : H →L[ℂ] ℂ)
    (j : Fin q) (y : Generator.FiniteHilbert (Fin p) H)
    (z : Generator.FiniteHilbert (Fin q) H) :
    rectangularHilbertMatrix (cochainColumnMatrix φ j y) z = φ (z j) • y := by
  ext i
  simp only [rectangularHilbertMatrix_apply, cochainColumnMatrix_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp [hkj]
  · simp

theorem norm_cochainColumnMatrix_le {p q : ℕ} (φ : H →L[ℂ] ℂ)
    (j : Fin q) (y : Generator.FiniteHilbert (Fin p) H) :
    ‖cochainColumnMatrix φ j y‖ ≤ ‖φ‖ * ‖y‖ := by
  rw [← norm_rectangularHilbertMatrix]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg φ) (norm_nonneg y))
  intro z
  rw [hilbertMatrix_cochainColumnMatrix, norm_smul]
  calc
    ‖φ (z j)‖ * ‖y‖ ≤ (‖φ‖ * ‖z j‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right (φ.le_opNorm _) (norm_nonneg y)
    _ ≤ (‖φ‖ * ‖z‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le z j) (norm_nonneg φ)) (norm_nonneg y)
    _ = _ := by ring

/-- A matrix of contracted cochain values is obtained by applying the
bilinear amplification to one rank-one column. -/
theorem operatorCochainContraction_matrix_action
    {f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) (φ : H →L[ℂ] ℂ) (ξ : H)
    {p r q : ℕ} (j : Fin q) (X : CStarMatrix (Fin p) (Fin r) (H →L[ℂ] H))
    (y : Generator.FiniteHilbert (Fin r) H) :
    rectangularHilbertMatrix (CStarMatrix.mapₗ (operatorCochainContraction hf hc φ ξ).toLinearMap X) y =
      rectangularHilbertMatrix (bilinearProduct f X (cochainColumnMatrix φ j y))
        (Generator.tupleSingle j ξ) := by
  ext i
  simp only [rectangularHilbertMatrix_apply]
  have hsum : (∑ k, (bilinearProduct f X (cochainColumnMatrix φ j y)) i k
      (Generator.tupleSingle j ξ k)) =
      (bilinearProduct f X (cochainColumnMatrix φ j y)) i j ξ := by
    rw [Finset.sum_eq_single j]
    · simp [Generator.tupleSingle_apply]
    · intro k _ hkj
      simp [Generator.tupleSingle_apply, hkj]
    · simp
  rw [hsum]
  change (∑ k, f (X i k) (cochainColumn φ (y k)) ξ) = _
  simp [bilinearProduct_apply, sum_apply]

/-- The rank-one contraction has its exact complete bound. -/
theorem operatorCochainContraction_complete_bound
    {f : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H)} {c : ℝ}
    (hf : HaagerupBound f c) (hc : 0 ≤ c) (φ : H →L[ℂ] ℂ) (ξ : H) :
    CompletelyBoundedBy (operatorCochainContraction hf hc φ ξ).toLinearMap
      (c * ‖φ‖ * ‖ξ‖) := by
  intro p q X
  by_cases hq : q = 0
  · subst q
    have hX : X = 0 := by ext i j; exact Fin.elim0 j
    simp only [hX, map_zero, norm_zero, mul_zero, le_refl]
  let j : Fin q := ⟨0, Nat.pos_of_ne_zero hq⟩
  rw [← norm_rectangularHilbertMatrix]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro y
  rw [operatorCochainContraction_matrix_action hf hc φ ξ j]
  calc
    _ ≤ ‖bilinearProduct f X (cochainColumnMatrix φ j y)‖ * ‖Generator.tupleSingle j ξ‖ := by
      have h := (rectangularHilbertMatrix (bilinearProduct f X (cochainColumnMatrix φ j y))).le_opNorm
        (Generator.tupleSingle j ξ)
      rwa [norm_rectangularHilbertMatrix] at h
    _ ≤ (c * ‖X‖ * (‖φ‖ * ‖y‖)) * ‖ξ‖ := by
      rw [norm_tupleSingle]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg ξ)
      exact (hf p q q X _).trans
        (mul_le_mul_of_nonneg_left (norm_cochainColumnMatrix_le φ j y)
          (mul_nonneg hc (norm_nonneg X)))
    _ = _ := by ring

end

end KadisonKastler

end OAI
