import OAI.Geometry.Arnold.Deformation

namespace OAI

universe uE uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function

open scoped BigOperators ContDiff
open ContinuousAlternatingMap

namespace ArnoldCounterexample.Forms

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The alternating product of a bilinear form and an n-form, with an integer
normalization convenient for the six-dimensional obstruction. -/
def pairForm {n : ℕ} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (η : E [⋀^Fin n]→L[ℝ] ℝ) : E [⋀^Fin (n + 2)]→L[ℝ] ℝ :=
  alternatizeUncurryFin ((alternatizeUncurryFinCLM ℝ E ℝ).comp
    (((ContinuousLinearMap.smulRightL ℝ E (E [⋀^Fin n]→L[ℝ] ℝ)).flip η).comp B))

lemma pairForm_apply {n : ℕ} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (η : E [⋀^Fin n]→L[ℝ] ℝ) (v : Fin (n + 2) → E) :
    pairForm B η v = ∑ i : Fin (n + 2), ∑ j : Fin (n + 1),
      (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ j.val *
        B (v i) ((i.removeNth v) j) * η (j.removeNth (i.removeNth v)) := by
  simp [pairForm, alternatizeUncurryFin_apply, ContinuousLinearMap.smulRightL,
    ← Int.cast_smul_eq_zsmul ℝ,
    smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- If all contractions of each factor vanish in a direction, so does their
alternating product. Restricting to the unit-sphere tangent gives basicness. -/
lemma pairForm_radical {n : ℕ} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (η : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) (u : E)
    (hleft : ∀ v, B u v = 0) (hright : ∀ v, B v u = 0)
    (hη : ∀ v : Fin n → E, η (Matrix.vecCons u v) = 0)
    (v : Fin (n + 2) → E) :
    pairForm B η (Matrix.vecCons u v) = 0 := by
  have hr {k : ℕ} (i : Fin (k + 1)) (v : Fin (k + 1) → E) :
      i.succ.removeNth (Matrix.vecCons u v) = Matrix.vecCons u (i.removeNth v) :=
    Fin.cons_comp_succ_succAbove u v i
  rw [pairForm_apply, Fin.sum_univ_succ]
  have hzero : (∑ j : Fin (n + 2),
      (-1 : ℝ) ^ (0 : Fin (n + 3)).val * (-1 : ℝ) ^ j.val *
      B (Matrix.vecCons u v 0) ((0 : Fin (n + 3)).removeNth (Matrix.vecCons u v) j) *
      η (j.removeNth ((0 : Fin (n + 3)).removeNth (Matrix.vecCons u v)))) = 0 := by
    simp [hleft]
  rw [hzero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  rw [Fin.sum_univ_succ]
  simp only [hr, Matrix.cons_val_succ, Matrix.cons_val_zero, hright,
    mul_zero, zero_mul, zero_add]
  apply Finset.sum_eq_zero
  intro j _
  rw [hη]
  exact mul_zero _

lemma pairForm_pullback {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (B : F →L[ℝ] F →L[ℝ] ℝ) (η : F [⋀^Fin n]→L[ℝ] ℝ)
    (L : E →L[ℝ] F) (v : Fin (n + 2) → E) :
    pairForm B η (L ∘ v) =
      pairForm (B.bilinearComp L L) (η.compContinuousLinearMap L) v := by
  simp only [pairForm_apply, ContinuousLinearMap.bilinearComp_apply,
    compContinuousLinearMap_apply, Function.comp_apply]
  rfl

def squareForm (B : E →L[ℝ] E →L[ℝ] ℝ) : E [⋀^Fin 4]→L[ℝ] ℝ :=
  pairForm B (pairForm B (constOfIsEmpty ℝ E (Fin 0) 1))

def cubeForm (B : E →L[ℝ] E →L[ℝ] ℝ) : E [⋀^Fin 6]→L[ℝ] ℝ :=
  pairForm B (squareForm B)

lemma cubeForm_pullback {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ) (L : E →L[ℝ] F) :
    (cubeForm B).compContinuousLinearMap L = cubeForm (B.bilinearComp L L) := by
  have hpair {n : ℕ} (η : F [⋀^Fin n]→L[ℝ] ℝ) :
      (pairForm B η).compContinuousLinearMap L =
        pairForm (B.bilinearComp L L) (η.compContinuousLinearMap L) := by
    ext v
    exact pairForm_pullback B η L v
  simp only [cubeForm, squareForm, hpair]
  congr 3

lemma cubeForm_radical (B : E →L[ℝ] E →L[ℝ] ℝ)
    (u : E) (hl : ∀ v, B u v = 0) (hr : ∀ v, B v u = 0)
    (v : Fin 5 → E) : cubeForm B (Matrix.vecCons u v) = 0 := by
  apply pairForm_radical B (squareForm B) u hl hr
  intro w
  apply pairForm_radical B _ u hl hr
  intro w
  simp [pairForm_apply, Fin.sum_univ_succ, Fin.removeNth, hl, hr]

/-- The third symplectic power vanishes when one input lies in the radical
of the bilinear form on the span of all six inputs. -/
lemma cubeForm_radical_on (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hskew : ∀ u v, B u v = - B v u) (u : E) (v : Fin 5 → E)
    (horth : ∀ i, B u (v i) = 0) : cubeForm B (Matrix.vecCons u v) = 0 := by
  let S := (B u).ker
  have hu : u ∈ S := by
    change B u u = 0
    linarith [hskew u u]
  let u' : S := ⟨u, hu⟩
  let v' : Fin 5 → S := fun i ↦ ⟨v i, horth i⟩
  let B' := B.bilinearComp S.subtypeL S.subtypeL
  have hl (w : S) : B' u' w = 0 := w.property
  have hr (w : S) : B' w u' = 0 := by
    change B w u = 0
    rw [hskew]
    exact neg_eq_zero.mpr w.property
  have hzero := cubeForm_radical B' u' hl hr v'
  rw [← cubeForm_pullback B S.subtypeL] at hzero
  have heq : S.subtypeL ∘ Matrix.vecCons u' v' = Matrix.vecCons u v := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  simpa only [compContinuousLinearMap_apply, heq] using hzero

lemma squareForm_apply (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hskew : ∀ u v, B u v = -B v u) (v : Fin 4 → E) :
    squareForm B v = 8 * (B (v 0) (v 1) * B (v 2) (v 3) -
      B (v 0) (v 2) * B (v 1) (v 3) + B (v 0) (v 3) * B (v 1) (v 2)) := by
  simp only [squareForm, pairForm_apply, constOfIsEmpty_apply]
  simp +decide [Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove]
  rw [hskew (v 1) (v 0), hskew (v 2) (v 0), hskew (v 2) (v 1),
      hskew (v 3) (v 0), hskew (v 3) (v 1), hskew (v 3) (v 2)]
  ring

end ArnoldCounterexample.Forms

end

end OAI
