import OAI.Analysis.CoulombTransport.AxisHessian

namespace OAI

universe uN

noncomputable section

namespace Problem356.LocalHessian

open Matrix
open scoped RealInnerProductSpace

/-- Invertible matrices induce invertible continuous linear maps in Euclidean coordinates. -/
lemma toEuclideanCLM_isInvertible {n : Type uN} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : IsUnit A) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).IsInvertible := by
  obtain ⟨u, hu⟩ := hA.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).toMonoidHom
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

abbrev AxisSpace := EuclideanSpace ℝ (Fin 3)
abbrev StateSpace := AxisSpace × AxisSpace
abbrev JointSpace := EuclideanSpace ℝ (Fin 3 ⊕ Fin 3)

/-- Passing from sum coordinates to the product coordinates used by the implicit function theorem. -/
def stateCoordinates : JointSpace ≃L[ℝ] StateSpace := EuclideanSpace.sumEquivProd

/-- The regularized state derivative as a continuous linear map on product space. -/
def stateOperator (k : Fin 3) : StateSpace →L[ℝ] StateSpace :=
  stateCoordinates.toContinuousLinearMap ∘L
    (Matrix.toEuclideanCLM (n := Fin 3 ⊕ Fin 3) (𝕜 := ℝ) (regularizedHessian k)) ∘L
      stateCoordinates.symm.toContinuousLinearMap

lemma stateOperator_isInvertible (k : Fin 3) : (stateOperator k).IsInvertible := by
  exact ContinuousLinearMap.IsInvertible.comp
    (ContinuousLinearMap.isInvertible_equiv (f := stateCoordinates))
    (ContinuousLinearMap.IsInvertible.comp
      (toEuclideanCLM_isInvertible _ (regularizedHessian_isUnit k))
      (ContinuousLinearMap.isInvertible_equiv (f := stateCoordinates.symm)))

lemma centralDerivativeCLM_isInvertible (k : Fin 3) :
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (centralDerivative k)).IsInvertible :=
  toEuclideanCLM_isInvertible _ (centralDerivative_isUnit k)

lemma oppositeDerivativeCLM_isInvertible (k : Fin 3) :
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (oppositeDerivative k)).IsInvertible :=
  toEuclideanCLM_isInvertible _ (oppositeDerivative_isUnit k)

lemma regularizedHessian_coercive (k : Fin 3) (v : JointSpace) :
    16 * ‖v‖ ^ 2 ≤ ⟪v, Matrix.toEuclideanCLM (n := Fin 3 ⊕ Fin 3) (𝕜 := ℝ) (regularizedHessian k) v⟫ := by
  rw [Matrix.inner_toEuclideanCLM]
  have hq := regularizedHessian_quadratic k (WithLp.ofLp v)
  simp only [star_trivial] at hq
  rw [hq, EuclideanSpace.real_norm_sq_eq, Fintype.sum_sum_type,
    mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simpa only [mul_add] using
    (scalar_quadratic_coercive (x := v (Sum.inl i)) (z := v (Sum.inr i))
      (eigenvalue_cases k i))

@[simp] lemma stateCoordinates_symm_inl (v : StateSpace) (i : Fin 3) :
    stateCoordinates.symm v (Sum.inl i) = v.1 i := rfl

@[simp] lemma stateCoordinates_symm_inr (v : StateSpace) (i : Fin 3) :
    stateCoordinates.symm v (Sum.inr i) = v.2 i := rfl

lemma stateOperator_fst_apply (k : Fin 3) (v : StateSpace) (i : Fin 3) :
    (stateOperator k v).1 i =
      (20 + 2 * eigenvalue k i) * v.1 i - eigenvalue k i * v.2 i := by
  change ((regularizedHessian k) *ᵥ (WithLp.ofLp (stateCoordinates.symm v)))
    (Sum.inl i) = _
  rw [regularizedHessian, fromBlocks_mulVec]
  simp [upperBlock, mixedBlock, mulVec_diagonal, sub_eq_add_neg]

lemma stateOperator_snd_apply (k : Fin 3) (v : StateSpace) (i : Fin 3) :
    (stateOperator k v).2 i =
      -eigenvalue k i * v.1 i + (20 + (9 / 8) * eigenvalue k i) * v.2 i := by
  change ((regularizedHessian k) *ᵥ (WithLp.ofLp (stateCoordinates.symm v)))
    (Sum.inr i) = _
  rw [regularizedHessian, fromBlocks_mulVec]
  simp [lowerBlock, mixedBlock, mulVec_diagonal]

lemma stateOperator_joint_coercive (k : Fin 3) (v : StateSpace) :
    16 * (‖v.1‖ ^ 2 + ‖v.2‖ ^ 2) ≤
      ⟪v.1, (stateOperator k v).1⟫ + ⟪v.2, (stateOperator k v).2⟫ := by
  simp only [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, stateOperator_fst_apply, stateOperator_snd_apply,
    mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have h := scalar_quadratic_coercive (x := v.1 i) (z := v.2 i) (eigenvalue_cases k i)
  nlinarith

lemma stateOperator_coercive (k : Fin 3) (v : StateSpace) :
    16 * ‖v‖ ^ 2 ≤
      ⟪v.1, (stateOperator k v).1⟫ + ⟪v.2, (stateOperator k v).2⟫ := by
  have hn : ‖v‖ ^ 2 ≤ ‖v.1‖ ^ 2 + ‖v.2‖ ^ 2 := by
    rw [Prod.norm_def]
    rcases le_total ‖v.1‖ ‖v.2‖ with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg ‖v.1‖]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ‖v.2‖]
  nlinarith [stateOperator_joint_coercive k v]

/-- The derivative in the parameter variable at the center. -/
def parameterOperator (k : Fin 3) : AxisSpace →L[ℝ] StateSpace :=
  let Q := Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (pairHessian k)
  (-Q).prod ((-(1 / 8 : ℝ)) • Q)

/-- The derivative of the stationary branch: central and opposite components. -/
def branchOperator (k : Fin 3) : AxisSpace →L[ℝ] StateSpace :=
  (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (centralDerivative k)).prod
    (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) (oppositeDerivative k))

@[simp] lemma branchOperator_fst_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (branchOperator k v).1 i = (if i = k then 9 / 106 else -15 / 271) * v i := by
  change ((centralDerivative k) *ᵥ WithLp.ofLp v) i = _
  simp [centralDerivative, mulVec_diagonal]

@[simp] lemma branchOperator_snd_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (branchOperator k v).2 i = (if i = k then 1 / 53 else -1 / 271) * v i := by
  change ((oppositeDerivative k) *ᵥ WithLp.ofLp v) i = _
  simp [oppositeDerivative, mulVec_diagonal]

@[simp] lemma parameterOperator_fst_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (parameterOperator k v).1 i = -eigenvalue k i * v i := by
  change -(((pairHessian k) *ᵥ WithLp.ofLp v) i) = _
  simp [pairHessian, mulVec_diagonal]

@[simp] lemma parameterOperator_snd_apply (k : Fin 3) (v : AxisSpace) (i : Fin 3) :
    (parameterOperator k v).2 i = -(eigenvalue k i * v i) / 8 := by
  change (-(1 / 8 : ℝ)) * (((pairHessian k) *ᵥ WithLp.ofLp v) i) = _
  simp [pairHessian, mulVec_diagonal]
  ring

lemma stateOperator_comp_branchOperator (k : Fin 3) :
    stateOperator k ∘L branchOperator k = -parameterOperator k := by
  apply ContinuousLinearMap.ext
  intro v
  apply Prod.ext
  · ext i
    simp only [ContinuousLinearMap.comp_apply, stateOperator_fst_apply,
      branchOperator_fst_apply, branchOperator_snd_apply,
      _root_.neg_apply, Prod.fst_neg, PiLp.neg_apply,
      parameterOperator_fst_apply]
    unfold eigenvalue
    split_ifs <;> ring
  · ext i
    simp only [ContinuousLinearMap.comp_apply, stateOperator_snd_apply,
      branchOperator_fst_apply, branchOperator_snd_apply,
      _root_.neg_apply, Prod.snd_neg, PiLp.neg_apply,
      parameterOperator_snd_apply]
    unfold eigenvalue
    split_ifs <;> ring

lemma neg_inverse_comp_parameterOperator (k : Fin 3) :
    -((stateOperator k).inverse ∘L parameterOperator k) = branchOperator k := by
  calc
    -((stateOperator k).inverse ∘L parameterOperator k) =
        (stateOperator k).inverse ∘L (-parameterOperator k) := by
          rw [ContinuousLinearMap.comp_neg]
    _ = (stateOperator k).inverse ∘L (stateOperator k ∘L branchOperator k) := by
          rw [stateOperator_comp_branchOperator]
    _ = branchOperator k := by
          rw [← ContinuousLinearMap.comp_assoc,
            (stateOperator_isInvertible k).inverse_comp_self, ContinuousLinearMap.id_comp]

lemma central_inverse_block_isInvertible (k : Fin 3) :
    ((ContinuousLinearMap.fst ℝ AxisSpace AxisSpace) ∘L
      (-((stateOperator k).inverse ∘L parameterOperator k))).IsInvertible := by
  rw [neg_inverse_comp_parameterOperator]
  exact centralDerivativeCLM_isInvertible k

lemma opposite_inverse_block_isInvertible (k : Fin 3) :
    ((ContinuousLinearMap.snd ℝ AxisSpace AxisSpace) ∘L
      (-((stateOperator k).inverse ∘L parameterOperator k))).IsInvertible := by
  rw [neg_inverse_comp_parameterOperator]
  exact oppositeDerivativeCLM_isInvertible k

end Problem356.LocalHessian

end

end OAI
