import OAI.Analysis.BoundedHochschild.OperatorSystemMatrices
import OAI.Analysis.BoundedHochschild.MatrixFunctionalDilation

namespace OAI

/-! The finite-dimensional operator-valued positive extension theorem.
Only positivity at the target matrix size is needed. -/

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def operatorSystemSingle (S : Submodule ℂ A) {n : ℕ} (i j : Fin n) (a : S) :
    operatorSystemMatrices S n :=
  ⟨singleCStarMatrix i j (a : A), fun p q => by
    change (if i = p ∧ j = q then (a : A) else 0) ∈ S
    split_ifs
    · exact a.property
    · exact S.zero_mem⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma operatorSystemSingle_amplification (S : Submodule ℂ A) {n : ℕ}
    (φ : S →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (i j : Fin n) (a : S) :
    operatorSystemAmplification S φ n (operatorSystemSingle S i j a) =
      singleCStarMatrix i j (φ a) := by
  apply CStarMatrix.ext
  intro p q
  by_cases h : i = p ∧ j = q
  · rcases h with ⟨rfl, rfl⟩
    have he : (⟨(operatorSystemSingle S i j a).val i j,
        (operatorSystemSingle S i j a).property i j⟩ : S) = a :=
      Subtype.ext (Matrix.single_apply_same i j (a : A))
    exact (congrArg φ he).trans (Matrix.single_apply_same i j (φ a)).symm
  · have hz : (operatorSystemSingle S i j a).val p q = 0 := by
      exact ite_eq_right (fun h' => (h h').elim)
    have he : (⟨(operatorSystemSingle S i j a).val p q,
        (operatorSystemSingle S i j a).property p q⟩ : S) = 0 := Subtype.ext hz
    exact (congrArg φ he).trans ((map_zero φ).trans
      (show singleCStarMatrix i j (φ a) p q = 0 from
        ite_eq_right (fun h' => (h h').elim)).symm)

omit [PartialOrder A] [StarOrderedRing A] in
lemma operatorSystemMatrixFunctional_single (S : Submodule ℂ A) {n : ℕ}
    (φ : S →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (i j : Fin n) (a : S) :
    operatorSystemMatrixFunctional S φ (fun k => EuclideanSpace.single k 1)
      (operatorSystemSingle S i j a) =
        inner ℂ (EuclideanSpace.single i 1) (φ a (EuclideanSpace.single j 1)) := by
  change operatorMatrixVectorFunctional (fun k => EuclideanSpace.single k 1)
    (operatorSystemAmplification S φ n (operatorSystemSingle S i j a)) = _
  rw [operatorSystemSingle_amplification]
  change (∑ p, ∑ q, inner ℂ (EuclideanSpace.single p 1)
    ((if i = p ∧ j = q then φ a else 0) (EuclideanSpace.single q 1))) = _
  have he (p q : Fin n) : inner ℂ (EuclideanSpace.single p 1)
      ((if i = p ∧ j = q then φ a else 0) (EuclideanSpace.single q 1)) =
      if p = i ∧ q = j then
        inner ℂ (EuclideanSpace.single i 1) (φ a (EuclideanSpace.single j 1)) else 0 := by
    by_cases hp : p = i <;> by_cases hq : q = j
    · subst p; subst q; simp
    · simp [hp, hq, Ne.symm hq]
    · simp [hp, Ne.symm hp]
    · simp [hp, Ne.symm hp]
  simp_rw [he]
  simp [ite_and]

lemma euclideanOperator_ext {n : ℕ}
    (T U : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (h : ∀ i j, inner ℂ (EuclideanSpace.single i 1) (T (EuclideanSpace.single j 1)) =
      inner ℂ (EuclideanSpace.single i 1) (U (EuclideanSpace.single j 1))) : T = U := by
  have he (j : Fin n) : T (EuclideanSpace.single j 1) = U (EuclideanSpace.single j 1) := by
    apply PiLp.ext
    intro i
    have hh := h i j
    simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at hh
    exact hh
  apply ContinuousLinearMap.coe_injective
  apply (PiLp.basisFun 2 ℂ (Fin n)).ext
  intro j
  rw [PiLp.basisFun_apply]
  exact he j

theorem exists_finite_completelyPositive_extension (S : Submodule ℂ A)
    (h1 : (1 : A) ∈ S) (hstar : ∀ a ∈ S, star a ∈ S) {n : ℕ} (i₀ : Fin n)
    (φ : S →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)))
    (hφ : ∀ X : operatorSystemMatrices S n,
      0 ≤ (X : CStarMatrix (Fin n) (Fin n) A) →
        0 ≤ operatorSystemAmplification S φ n X) :
    ∃ Φ : CompletelyPositiveMap A
      (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)),
        ∀ a : S, Φ (a : A) = φ a := by
  let ξ : Fin n → EuclideanSpace ℂ (Fin n) := fun i => EuclideanSpace.single i 1
  obtain ⟨F, hF⟩ := exists_positive_operatorSystem_extension
    (operatorSystemMatrices S n) (operatorSystemMatrices_one S h1 n)
    (operatorSystemMatrices_star S hstar n) (operatorSystemMatrixFunctional S φ ξ)
    (operatorSystemMatrixFunctional_nonneg S φ ξ hφ)
  refine ⟨matrixFunctionalCP F i₀, fun a => euclideanOperator_ext _ _ (fun i j => ?_)⟩
  rw [matrixFunctionalCP_coefficient]
  exact (hF (operatorSystemSingle S i j a)).trans
    (operatorSystemMatrixFunctional_single S φ i j a)

end BoundedHochschild.KadisonRingrose

end

end OAI
