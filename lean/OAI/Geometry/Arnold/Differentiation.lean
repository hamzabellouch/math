import OAI.Geometry.Arnold.Haar

namespace OAI

universe uE uF uG

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample.CriticalBound

/-- Smooth evaluation including all moving vector arguments. -/
theorem contDiff_multilinear_apply {E : Type uE} {F : Type uF} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ∞ω} {n : ℕ} {f : E → F [×n]→L[ℝ] G}
    (hf : ContDiff ℝ k f) {v : Fin n → E → F} (hv : ∀ i, ContDiff ℝ k (v i)) :
    ContDiff ℝ k (fun x ↦ f x (v · x)) := by
  induction n with
  | zero =>
      convert! (continuousMultilinearCurryFin0 ℝ F G).contDiff.comp hf using 1
      ext x
      exact congrArg (f x) (Subsingleton.elim _ _)
  | succ n ih =>
      have hc : ContDiff ℝ k (fun x ↦ (f x).curryLeft (v 0 x)) := by
        convert! ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) ↦ F) G).contDiff.comp hf).clm_apply (hv 0) using 1
      convert! ih hc (fun i ↦ hv i.succ) using 1
      ext x
      exact congrArg (f x) (Fin.cons_self_tail (v · x)).symm

theorem contDiff_alternating_apply {E : Type uE} {F : Type uF} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ∞ω} {n : ℕ} {f : E → F [⋀^Fin n]→L[ℝ] G}
    (hf : ContDiff ℝ k f) {v : Fin n → E → F} (hv : ∀ i, ContDiff ℝ k (v i)) :
    ContDiff ℝ k (fun x ↦ f x (v · x)) := by
  convert! contDiff_multilinear_apply ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.comp hf) hv using 1

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open VectorField

/-- Matrix forms use the topology of the chosen operator norm. The orthogonal
group retains its original (definitionally distinct) product topology. -/
abbrev MatForm (n : ℕ) := by
  letI : TopologicalSpace RM :=
    (inferInstance : NormedAddCommGroup RM).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact RM [⋀^Fin n]→L[ℝ] ℝ

lemma fderiv_rightMul (X A B : RM) :
    fderiv ℝ (fun Y : RM ↦ Y * X) A B = B * X := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) A).mul_const' X).fderiv
  convert! congrArg (fun f : RM →L[ℝ] RM ↦ f B) h using 1

lemma lieBracket_rightMul (X Y A : RM) :
    lieBracket ℝ (fun B : RM ↦ B * X) (fun B : RM ↦ B * Y) A =
      A * (X * Y - Y * X) := by
  dsimp only [lieBracket]
  convert! congrArg₂ (fun P Q : RM ↦ P - Q) (fderiv_rightMul Y A (A * X))
    (fderiv_rightMul X A (A * Y)) using 1
  simp only [mul_sub, mul_assoc]

/-- Haar--Stokes on horizontal tuples of left-invariant fields. The bracket
hypothesis is basicness in the vertical directions; it is purely a pointwise
algebraic condition, not a Stokes or nonexactness assumption. -/
theorem integral_extDeriv_rightMul_eq_zero {n : ℕ}
    (W : RM → MatForm (n + 1)) (hW : ContDiff ℝ ∞ W)
    (X : Fin (n + 2) → RM) (hX : ∀ i, star (X i) = -X i)
    (hvertical : ∀ (A : O5) (i j : Fin (n + 1)),
      W A (Matrix.vecCons ((A : RM) * (X i.castSucc * X j.succ - X j.succ * X i.castSucc))
        (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * X k)))) = 0) :
    ∫ A : O5, extDeriv W (A : RM) (fun i ↦ (A : RM) * X i) ∂haar = 0 := by
  let F : Fin (n + 2) → RM → ℝ := fun i A ↦ W A (i.removeNth (fun k ↦ A * X k))
  have hF (i : Fin (n + 2)) : ContDiff ℝ ∞ (F i) := by
    exact contDiff_alternating_apply hW (fun _ ↦ contDiff_id.mul contDiff_const)
  have hpoint (A : O5) : extDeriv W (A : RM) (fun i ↦ (A : RM) * X i) =
      ∑ i, (-1 : ℝ) ^ i.val * fderiv ℝ (F i) (A : RM) ((A : RM) * X i) := by
    have h := extDeriv_apply_vectorField (V := fun i (A : RM) ↦ A * X i)
      (hW.differentiable (by simp) (A : RM))
      (fun i ↦ (contDiff_id.mul (contDiff_const (c := X i)) : ContDiff ℝ ∞ _).differentiable (by simp) _)
    convert! h.trans ?_ using 1
    simp only [lieBracket_rightMul, hvertical, smul_zero, Finset.sum_const_zero, sub_zero]
    simp only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul]
    congr! 2
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul]
    have hi := integral_fderiv_mul_skew_eq_zero (F i) (hF i) (X i) (hX i)
    convert! congrArg ((-1 : ℝ) ^ i.val * ·) hi using 1
    simp only [mul_zero]
  · intro i _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul
      (((hF i).continuous_fderiv (by simp)).comp continuous_subtype_val |>.clm_apply
        (continuous_subtype_val.mul continuous_const))

end ArnoldCounterexample.CriticalBound

end

end OAI
